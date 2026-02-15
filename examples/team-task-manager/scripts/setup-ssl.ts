#!/usr/bin/env bun

/**
 * SSL Certificate Setup for Team Task Manager
 *
 * Generates self-signed SSL certificates for local development using either:
 * - mkcert (preferred) - generates trusted certificates
 * - openssl (fallback) - generates self-signed certificates
 */

const SERVER_CERTS_DIR = `${import.meta.dir}/../server/certs`;
const CLIENT_CERTS_DIR = `${import.meta.dir}/../client/certs`;

async function checkMkcertAvailable(): Promise<boolean> {
  try {
    const result = await Bun.$`which mkcert`.quiet();
    return result.exitCode === 0;
  } catch {
    return false;
  }
}

async function checkHomebrewAvailable(): Promise<boolean> {
  try {
    const result = await Bun.$`which brew`.quiet();
    return result.exitCode === 0;
  } catch {
    return false;
  }
}

function promptUser(question: string): Promise<string> {
  process.stdout.write(question);

  return new Promise((resolve) => {
    const stdin = process.stdin;
    stdin.setEncoding("utf8");
    stdin.resume();

    const onData = (data: string) => {
      stdin.pause();
      stdin.removeListener("data", onData);
      resolve(data.trim().toLowerCase());
    };

    stdin.on("data", onData);
  });
}

async function installMkcert(): Promise<boolean> {
  try {
    console.log("Installing mkcert...");
    await Bun.$`brew install mkcert`;
    console.log("Installing local CA...");
    await Bun.$`mkcert -install`;
    console.log("mkcert installed successfully");
    return true;
  } catch (error) {
    console.error("Failed to install mkcert:", error);
    return false;
  }
}

async function generateWithMkcert() {
  console.log("Generating SSL certificates with mkcert...");

  // Generate certificates for localhost
  await Bun.$`mkcert -key-file ${CLIENT_CERTS_DIR}/key.pem -cert-file ${CLIENT_CERTS_DIR}/cert.pem localhost 127.0.0.1 ::1 "*.localhost"`;

  // Copy to server directory
  await Bun.$`cp ${CLIENT_CERTS_DIR}/cert.pem ${SERVER_CERTS_DIR}/cert.pem`;
  await Bun.$`cp ${CLIENT_CERTS_DIR}/key.pem ${SERVER_CERTS_DIR}/key.pem`;
}

async function generateWithOpenSSL() {
  console.log("Generating self-signed SSL certificates with OpenSSL...");

  const certConfig = `
[req]
distinguished_name = req_distinguished_name
x509_extensions = v3_req
prompt = no

[req_distinguished_name]
CN = localhost

[v3_req]
keyUsage = digitalSignature, keyEncipherment, dataEncipherment
extendedKeyUsage = serverAuth
subjectAltName = @alt_names

[alt_names]
DNS.1 = localhost
DNS.2 = *.localhost
IP.1 = 127.0.0.1
IP.2 = ::1
  `.trim();

  // Write config file
  await Bun.write(`${CLIENT_CERTS_DIR}/openssl.cnf`, certConfig);

  // Generate certificate
  await Bun.$`openssl req -x509 -newkey rsa:2048 -nodes -sha256 -days 365 -keyout ${CLIENT_CERTS_DIR}/key.pem -out ${CLIENT_CERTS_DIR}/cert.pem -config ${CLIENT_CERTS_DIR}/openssl.cnf`;

  // Copy to server directory
  await Bun.$`cp ${CLIENT_CERTS_DIR}/cert.pem ${SERVER_CERTS_DIR}/cert.pem`;
  await Bun.$`cp ${CLIENT_CERTS_DIR}/key.pem ${SERVER_CERTS_DIR}/key.pem`;

  // Clean up config
  await Bun.$`rm ${CLIENT_CERTS_DIR}/openssl.cnf`;
}

async function main() {
  console.log("Team Task Manager - SSL Certificate Setup\n");

  // Check if certificates already exist
  const serverCertExists = await Bun.file(`${SERVER_CERTS_DIR}/cert.pem`).exists();
  const serverKeyExists = await Bun.file(`${SERVER_CERTS_DIR}/key.pem`).exists();
  const clientCertExists = await Bun.file(`${CLIENT_CERTS_DIR}/cert.pem`).exists();
  const clientKeyExists = await Bun.file(`${CLIENT_CERTS_DIR}/key.pem`).exists();

  if (serverCertExists && serverKeyExists && clientCertExists && clientKeyExists) {
    console.log("SSL certificates already exist");
    console.log("   To regenerate, delete the cert files and run this script again\n");
    process.exit(0);
  }

  // Create cert directories
  await Bun.$`mkdir -p ${SERVER_CERTS_DIR}`;
  await Bun.$`mkdir -p ${CLIENT_CERTS_DIR}`;

  // Check if mkcert is available
  let hasMkcert = await checkMkcertAvailable();

  // Offer to install mkcert if not available
  if (!hasMkcert) {
    console.log("WARNING: mkcert not found");
    console.log("   mkcert generates locally-trusted SSL certificates (no browser warnings)\n");

    const hasHomebrew = await checkHomebrewAvailable();
    if (hasHomebrew) {
      const answer = await promptUser("   Install mkcert now? (Y/n): ");
      if (answer === "" || answer === "y" || answer === "yes") {
        const installed = await installMkcert();
        if (installed) {
          hasMkcert = true;
        }
      }
    } else {
      console.log("   Install mkcert manually: https://github.com/FiloSottile/mkcert\n");
    }
  }

  // Generate certificates
  if (hasMkcert) {
    await generateWithMkcert();
    console.log("SSL certificates generated with mkcert");
    console.log("   Your browser will trust these certificates automatically\n");
  } else {
    await generateWithOpenSSL();
    console.log("Self-signed SSL certificates generated");
    console.log("\nWARNING: Browser Setup Required:");
    console.log("   Your browser will show security warnings for self-signed certificates.");
    console.log("   You can either:");
    console.log("   1. Accept the warning and continue (not recommended for production)");
    console.log("   2. Install mkcert for trusted certificates: brew install mkcert\n");
  }

  console.log("Certificates saved to:");
  console.log(`   Server: ${SERVER_CERTS_DIR}/`);
  console.log(`   Client: ${CLIENT_CERTS_DIR}/\n`);
  console.log("You can now run: bun run dev\n");
}

main().catch((error) => {
  console.error("Setup failed:", error);
  process.exit(1);
});
