/**
 * Browser tests for Select — covers the "N selected" collapse, the
 * width-bound trigger, and basic interaction. Runs against the real
 * @fairfox/polly/ui Select rendered into a fresh container.
 */

import { signal } from "@preact/signals";
import { render } from "preact";
import { describe, done, expect, flush, test } from "@fairfox/polly/test/browser";
import { Select, type SelectOption } from "@fairfox/polly/ui";
import "@fairfox/polly/ui/theme.css";
import "@fairfox/polly/ui/components.css";

const fruits: SelectOption<string>[] = [
  { value: "apple", label: "Apple" },
  { value: "banana", label: "Banana" },
  { value: "cherry", label: "Cherry" },
  { value: "date", label: "Date" },
  { value: "elderberry", label: "Elderberry — a deliberately long option label" },
];

function mount(): HTMLElement {
  const host = document.createElement("div");
  host.id = `host-${Math.random().toString(36).slice(2, 8)}`;
  document.body.appendChild(host);
  return host;
}

function readTriggerLabel(host: HTMLElement): string {
  const label = host.querySelector<HTMLElement>("[data-polly-select] button > span");
  return label?.textContent?.trim() ?? "";
}

describe("Select — single", () => {
  test("renders the placeholder when nothing is selected", async () => {
    const host = mount();
    const selected = signal(new Set<string>());
    render(<Select options={fruits} selected={selected} placeholder="Pick a fruit" />, host);
    await flush();
    expect(readTriggerLabel(host)).toBe("Pick a fruit");
  });

  test("renders the selected label when one option is chosen", async () => {
    const host = mount();
    const selected = signal(new Set<string>(["banana"]));
    render(<Select options={fruits} selected={selected} />, host);
    await flush();
    expect(readTriggerLabel(host)).toBe("Banana");
  });
});

describe("Select — multi", () => {
  test("joins labels with comma when <=2 chosen", async () => {
    const host = mount();
    const selected = signal(new Set<string>(["apple", "banana"]));
    render(<Select options={fruits} selected={selected} multiSelect />, host);
    await flush();
    expect(readTriggerLabel(host)).toBe("Apple, Banana");
  });

  test("collapses to 'N selected' when more than 2 chosen", async () => {
    const host = mount();
    const selected = signal(new Set<string>(["apple", "banana", "cherry"]));
    render(<Select options={fruits} selected={selected} multiSelect />, host);
    await flush();
    expect(readTriggerLabel(host)).toBe("3 selected");
  });

  test("collapse threshold updates reactively as the set grows", async () => {
    const host = mount();
    const selected = signal(new Set<string>(["apple"]));
    render(<Select options={fruits} selected={selected} multiSelect />, host);
    await flush();
    expect(readTriggerLabel(host)).toBe("Apple");

    selected.value = new Set([...selected.value, "banana"]);
    await flush();
    expect(readTriggerLabel(host)).toBe("Apple, Banana");

    selected.value = new Set([...selected.value, "cherry"]);
    await flush();
    expect(readTriggerLabel(host)).toBe("3 selected");
  });
});

describe("Select — trigger label ellipsis contract", () => {
  test("label span has ellipsis overflow styles applied via class", async () => {
    const host = mount();
    const selected = signal(new Set<string>(["elderberry"]));
    render(<Select options={fruits} selected={selected} wide />, host);
    await flush();

    // The inner label span must carry the triggerLabel class so the
    // ellipsis rules apply at the trigger boundary. Width-token
    // verification (actual pixels) belongs in visual regression.
    const labelSpan = host.querySelector<HTMLElement>("[data-polly-select] button > span");
    if (!labelSpan) throw new Error("label span not found");
    expect(labelSpan.className.includes("triggerLabel")).toBe(true);
  });
});

done();
