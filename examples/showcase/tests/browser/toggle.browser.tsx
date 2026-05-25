/**
 * Browser tests for Checkbox + Toggle — confirms the controls render
 * the right ARIA state and that the signal-bound Checkbox tracks the
 * underlying signal value.
 */

import { signal } from "@preact/signals";
import { render } from "preact";
import { describe, done, expect, flush, test } from "@fairfox/polly/test/browser";
import { Checkbox, Toggle } from "@fairfox/polly/ui";

function mount(): HTMLElement {
  const host = document.createElement("div");
  host.id = `host-${Math.random().toString(36).slice(2, 8)}`;
  document.body.appendChild(host);
  return host;
}

describe("Checkbox", () => {
  test("renders checked when the bound signal is true", async () => {
    const host = mount();
    const value = signal(true);
    render(<Checkbox label="Bound" checked={value} />, host);
    await flush();
    expect(host.querySelector<HTMLInputElement>("input[type='checkbox']")?.checked).toBe(true);
  });

  test("reflects signal mutation", async () => {
    const host = mount();
    const value = signal(false);
    render(<Checkbox label="Bound" checked={value} />, host);
    await flush();
    expect(host.querySelector<HTMLInputElement>("input[type='checkbox']")?.checked).toBe(false);

    value.value = true;
    await flush();
    expect(host.querySelector<HTMLInputElement>("input[type='checkbox']")?.checked).toBe(true);
  });

  test("disabled checkbox sets the disabled attribute", async () => {
    const host = mount();
    render(<Checkbox label="No" disabled />, host);
    await flush();
    expect(host.querySelector<HTMLInputElement>("input[type='checkbox']")?.disabled).toBe(true);
  });
});

describe("Toggle", () => {
  test("renders role=switch with aria-checked", async () => {
    const host = mount();
    render(<Toggle label="Off" />, host);
    await flush();
    const input = host.querySelector<HTMLInputElement>("input[role='switch']");
    expect(input?.getAttribute("aria-checked")).toBe("false");
  });

  test("checked Toggle reports aria-checked=true", async () => {
    const host = mount();
    render(<Toggle label="On" checked />, host);
    await flush();
    expect(
      host
        .querySelector<HTMLInputElement>("input[role='switch']")
        ?.getAttribute("aria-checked"),
    ).toBe("true");
  });
});

done();
