import { beforeEach, expect, test } from "bun:test";
import {
  clearError,
  createForm,
  createFormSet,
  errorState,
  runAction,
} from "@fairfox/polly/actions";
import { signal } from "@preact/signals";

type TeamValues = { name: string; description: string };
type TestStores = {
  teams: { value: Array<{ id: string; name: string }> };
  modalEntityId: { value: string | null };
  createCalls: TeamValues[];
};

function makeStores(): TestStores {
  return {
    teams: signal<Array<{ id: string; name: string }>>([]),
    modalEntityId: signal<string | null>(null),
    createCalls: [],
  } as unknown as TestStores;
}

beforeEach(() => {
  clearError();
});

test("form exposes initial field signals and values signal", () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onSubmit: async ({ values, stores }) => {
      stores.createCalls.push(values);
    },
  });
  expect(form.fields.name.value).toBe("");
  expect(form.fields.description.value).toBe("");
  expect(form.values.value).toEqual({ name: "", description: "" });
  expect(form.isOpen.value).toBe(false);
});

test("open records openParams, sets isOpen, applies overrides", () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onSubmit: async () => {},
  });
  form.bindStores(() => makeStores());
  form.open({ name: "Seed" }, { entityId: "42" });
  expect(form.isOpen.value).toBe(true);
  expect(form.openParams.value).toEqual({ entityId: "42" });
  expect(form.fields.name.value).toBe("Seed");
  expect(form.fields.description.value).toBe("");
});

test("close resets fields and clears openParams", () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onSubmit: async () => {},
  });
  form.bindStores(() => makeStores());
  form.open({ name: "Seed" }, { entityId: "42" });
  form.close();
  expect(form.isOpen.value).toBe(false);
  expect(form.fields.name.value).toBe("");
  expect(form.openParams.value).toEqual({});
});

test("onOpen overrides initial values using stores", () => {
  const stores = makeStores();
  stores.teams.value = [{ id: "42", name: "Seed" }];
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onOpen: ({ data, stores: s }) => {
      const entity = s.teams.value.find((t) => t.id === data.entityId);
      return entity ? { name: entity.name } : {};
    },
    onSubmit: async () => {},
  });
  form.bindStores(() => stores);
  form.open(undefined, { entityId: "42" });
  expect(form.fields.name.value).toBe("Seed");
});

test("validate blocks submit and populates errors", async () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    validate: (v) => (v.name === "" ? { name: "required" } : null),
    onSubmit: async ({ stores }) => {
      stores.createCalls.push({ name: "never", description: "" });
    },
  });
  const stores = makeStores();
  form.bindStores(() => stores);
  form.open();
  await form.submit();
  expect(form.errors.value).toEqual({ name: "required" });
  expect(stores.createCalls.length).toBe(0);
});

test("submit runs onSubmit with current values and closes on success", async () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onSubmit: async ({ values, stores }) => {
      stores.createCalls.push(values);
    },
  });
  const stores = makeStores();
  form.bindStores(() => stores);
  form.open();
  form.fields.name.value = "New team";
  form.fields.description.value = "x";
  await form.submit();
  expect(stores.createCalls).toEqual([{ name: "New team", description: "x" }]);
  expect(form.isOpen.value).toBe(false);
});

test("submit routes thrown errors through submitError", async () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onSubmit: async () => {
      throw new Error("conflict");
    },
  });
  form.bindStores(() => makeStores());
  form.open();
  form.fields.name.value = "x";
  await form.submit();
  expect(errorState.value.some((e) => e.message === "conflict")).toBe(true);
  expect(form.isSubmitting.value).toBe(false);
});

test("auto-registered actions open, close, and submit via runAction", async () => {
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    onSubmit: async ({ values, stores }) => {
      stores.createCalls.push(values);
    },
  });
  const stores = makeStores();
  form.bindStores(() => stores);

  await runAction(form.actions, "team:open", {
    stores,
    data: { entityId: "42" },
  });
  expect(form.isOpen.value).toBe(true);
  expect(form.openParams.value).toEqual({ entityId: "42" });

  form.fields.name.value = "T";
  form.fields.description.value = "D";
  await runAction(form.actions, "team:submit", { stores });
  expect(stores.createCalls).toEqual([{ name: "T", description: "D" }]);
  expect(form.isOpen.value).toBe(false);
});

test("guard closes form when predicate turns false while open", () => {
  const stores = makeStores();
  stores.teams.value = [{ id: "42", name: "x" }];
  stores.modalEntityId.value = "42";
  const form = createForm<TeamValues, TestStores>({
    name: "team",
    initialValues: { name: "", description: "" },
    guard: ({ stores: s }) => s.teams.value.some((t) => t.id === s.modalEntityId.value),
    onSubmit: async () => {},
  });
  form.bindStores(() => stores);
  form.open(undefined, { entityId: "42" });
  expect(form.isOpen.value).toBe(true);
  stores.teams.value = [];
  expect(form.isOpen.value).toBe(false);
});

test("createFormSet merges actions and exposes openForm signal", () => {
  const formA = createForm<TeamValues, TestStores>({
    name: "a",
    initialValues: { name: "", description: "" },
    onSubmit: async () => {},
  });
  const formB = createForm<TeamValues, TestStores>({
    name: "b",
    initialValues: { name: "", description: "" },
    onSubmit: async () => {},
  });
  const set = createFormSet<TestStores>([formA, formB]);
  set.bindStores(() => makeStores());

  expect(Object.keys(set.actions).sort()).toEqual([
    "a:close",
    "a:open",
    "a:submit",
    "b:close",
    "b:open",
    "b:submit",
  ]);
  expect(set.openForm.value).toBeNull();
  formA.open();
  expect(set.openForm.value).toBe("a");
  formA.close();
  formB.open();
  expect(set.openForm.value).toBe("b");
  set.closeAll();
  expect(set.openForm.value).toBeNull();
});
