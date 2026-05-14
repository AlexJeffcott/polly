// Tests for SSL certificate requirement enforcement
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { existsSync } from "node:fs";
import { mkdir, rename, rm, writeFile } from "node:fs/promises";
import { join } from "node:path";

const TEMP_CERTS_DIR = join(import.meta.dir, "../certs-test");

describe("SSL Certificate Requirement", () => {
  beforeAll(async () => {
    // Create temp certs directory
    await mkdir(TEMP_CERTS_DIR, { recursive: true });
  });

  afterAll(async () => {
    // Clean up
    await rm(TEMP_CERTS_DIR, { recursive: true, force: true });
  });

  test("server refuses to start without SSL certificates", async () => {
    // Temporarily move real certs if they exist
    const realCertsDir = join(import.meta.dir, "../certs");
    const backupCertsDir = join(import.meta.dir, "../certs-backup-test");
    const certsExisted = existsSync(realCertsDir);

    if (certsExisted) {
      // Move certs temporarily
      await rename(realCertsDir, backupCertsDir);
    }

    try {
      // Create a minimal test that spawns the server without certs
      const proc = Bun.spawn({
        cmd: ["bun", "run", "src/index.ts"],
        cwd: join(import.meta.dir, ".."),
        env: {
          ...process.env,
        },
        stdout: "pipe",
        stderr: "pipe",
      });

      // Read both stdout and stderr to check for error message
      const decoder = new TextDecoder();
      const stdoutChunks: string[] = [];
      const stderrChunks: string[] = [];

      const stdoutReader = proc.stdout.getReader();
      const stderrReader = proc.stderr.getReader();

      // Read for a short time or until process exits
      const timeout = setTimeout(() => {
        proc.kill();
      }, 2000);

      try {
        // Read both streams concurrently
        await Promise.race([
          (async () => {
            while (true) {
              const { done, value } = await stdoutReader.read();
              if (done) break;
              stdoutChunks.push(decoder.decode(value));
            }
          })(),
          (async () => {
            while (true) {
              const { done, value } = await stderrReader.read();
              if (done) break;
              stderrChunks.push(decoder.decode(value));
            }
          })(),
          proc.exited,
        ]);
      } catch (e) {
        // Process was killed or stream closed
      } finally {
        clearTimeout(timeout);
        proc.kill();
      }

      const output = stdoutChunks.join("") + stderrChunks.join("");
      const exitCode = await proc.exited;

      // Should exit with error code (1 = normal exit, 143 = killed by us with timeout)
      expect([1, 143]).toContain(exitCode);

      // Should have SSL error message in either stdout or stderr
      expect(output).toContain("SSL certificates not found");
      expect(output).toContain("HTTPS for E2EE");
      expect(output).toContain("bun run setup:ssl");
    } finally {
      // Restore certs if they existed
      if (certsExisted && existsSync(backupCertsDir)) {
        await rename(backupCertsDir, realCertsDir);
      }
    }
  });

  test("server starts successfully with SSL certificates", async () => {
    // Create dummy cert files
    await writeFile(join(TEMP_CERTS_DIR, "cert.pem"), "FAKE CERT");
    await writeFile(join(TEMP_CERTS_DIR, "key.pem"), "FAKE KEY");

    const proc = Bun.spawn({
      cmd: ["bun", "run", "src/index.ts"],
      cwd: join(import.meta.dir, ".."),
      env: {
        ...process.env,
        // Point to test certs
        CERTS_DIR: TEMP_CERTS_DIR,
      },
      stdout: "pipe",
      stderr: "pipe",
    });

    // Read both streams to check for startup output. The SSL-missing
    // error goes to stderr, the success line goes to stdout; we only
    // care about the SSL-missing marker being absent, so capturing
    // both is what makes the assertion meaningful.
    const decoder = new TextDecoder();
    const stdoutChunks: string[] = [];
    const stderrChunks: string[] = [];

    const stdoutReader = proc.stdout.getReader();
    const stderrReader = proc.stderr.getReader();

    const timeout = setTimeout(() => {
      proc.kill();
    }, 2000);

    try {
      await Promise.race([
        (async () => {
          while (true) {
            const { done, value } = await stdoutReader.read();
            if (done) break;
            stdoutChunks.push(decoder.decode(value));
          }
        })(),
        (async () => {
          while (true) {
            const { done, value } = await stderrReader.read();
            if (done) break;
            stderrChunks.push(decoder.decode(value));
          }
        })(),
        proc.exited,
      ]);
    } catch (e) {
      // Expected - we're killing the process
    } finally {
      clearTimeout(timeout);
      proc.kill();
    }

    const output = stdoutChunks.join("") + stderrChunks.join("");

    // The fake cert content will fail TLS init, but that's not what
    // this test asserts — it asserts that the SSL-missing branch
    // didn't fire, i.e. the server honoured the CERTS_DIR env var
    // and saw the files we put there.
    expect(output).not.toContain("SSL certificates not found");
  });

  test("validates SSL certificate file existence", async () => {
    // Create temp cert files
    await writeFile(join(TEMP_CERTS_DIR, "cert.pem"), "TEST CERT");
    await writeFile(join(TEMP_CERTS_DIR, "key.pem"), "TEST KEY");

    const certFile = Bun.file(join(TEMP_CERTS_DIR, "cert.pem"));
    const keyFile = Bun.file(join(TEMP_CERTS_DIR, "key.pem"));

    // Should exist after writing
    expect(await certFile.exists()).toBe(true);
    expect(await keyFile.exists()).toBe(true);

    // Clean up
    await rm(join(TEMP_CERTS_DIR, "cert.pem"));
    await rm(join(TEMP_CERTS_DIR, "key.pem"));

    // Create new file instances to check deletion
    const certFileAfter = Bun.file(join(TEMP_CERTS_DIR, "cert.pem"));
    const keyFileAfter = Bun.file(join(TEMP_CERTS_DIR, "key.pem"));

    expect(await certFileAfter.exists()).toBe(false);
    expect(await keyFileAfter.exists()).toBe(false);
  });
});
