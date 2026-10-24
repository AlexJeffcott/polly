import { counter } from "./state";

export function handleAdd(payload: { n: number }) {
  counter.value.count = payload.n;
}

export function handleRemove() {
  counter.value.count = 0;
}

export const handleArrow = (payload: { label: string }) => {
  counter.value.label = payload.label;
};

function handleRenamed() {
  counter.value.label = "renamed";
}

export { handleRenamed as handleExportedAlias };
