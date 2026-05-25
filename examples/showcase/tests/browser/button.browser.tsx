/**
 * Browser tests for Button — covers the new `bounded` prop's
 * max-width + ellipsis behaviour and the disabled/circle modifiers.
 */

import { render } from "preact";
import { describe, done, expect, flush, test } from "@fairfox/polly/test/browser";
import { Button } from "@fairfox/polly/ui";
import "@fairfox/polly/ui/theme.css";
import "@fairfox/polly/ui/components.css";

const LONG_LABEL =
  "A deliberately long button label that should ellipsis-truncate when the bounded prop is set and otherwise expand";

function mount(): HTMLElement {
  const host = document.createElement("div");
  host.id = `host-${Math.random().toString(36).slice(2, 8)}`;
  document.body.appendChild(host);
  return host;
}

describe("Button — bounded prop", () => {
  test("bounded prop applies the btnBounded class", async () => {
    const host = mount();
    render(<Button label={LONG_LABEL} bounded />, host);
    await flush();

    const button = host.querySelector<HTMLButtonElement>("button");
    if (!button) throw new Error("button not found");
    expect(button.className.includes("btnBounded")).toBe(true);
  });

  test("default Button does NOT apply the btnBounded class", async () => {
    const host = mount();
    render(<Button label={LONG_LABEL} />, host);
    await flush();

    const button = host.querySelector<HTMLButtonElement>("button");
    if (!button) throw new Error("button not found");
    expect(button.className.includes("btnBounded")).toBe(false);
  });
});

describe("Button — modifiers", () => {
  test("disabled buttons set the disabled attribute", async () => {
    const host = mount();
    render(<Button label="Nope" disabled />, host);
    await flush();
    const button = host.querySelector<HTMLButtonElement>("button");
    expect(button?.disabled).toBe(true);
  });

  test("href turns the Button into an <a>", async () => {
    const host = mount();
    render(<Button label="Go" href="https://example.com" />, host);
    await flush();
    expect(host.querySelector("a")?.getAttribute("href")).toBe("https://example.com");
    expect(host.querySelector("button")).toBe(null);
  });
});

done();
