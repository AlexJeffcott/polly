#!/usr/bin/env bun
/**
 * CLI for Polly test runner
 *
 * Wraps bun test with Polly-specific test utilities and helpers.
 */

async function main() {
  const args = process.argv.slice(2);
  const cwd = process.cwd();

  // Run bun test with all provided arguments
  const proc = Bun.spawn(["bun", "test", ...args], {
    cwd,
    stdout: "pipe",
    stderr: "pipe",
    stdin: "inherit",
  });

  const stdout = await new Response(proc.stdout).text();
  const stderr = await new Response(proc.stderr).text();

  // Output the results
  if (stdout) process.stdout.write(stdout);
  if (stderr) process.stderr.write(stderr);

  const exitCode = await proc.exited;

  // Check if no tests were found (not a failure)
  if (stderr.includes("0 test files matching")) {
    console.log("\nNo test files found.");
    process.exit(0);
  }

  if (exitCode !== 0) {
    process.exit(exitCode);
  }
}

main();
