import { handleAdd, handleRemove as remove, handleArrow, handleExportedAlias } from "./impl";
import { handleAddAgain } from "./reexport";
import { bus } from "./runtime";
import { counter } from "./state";

bus.on("ADD", handleAdd);
bus.on("REMOVE", remove);
bus.on("ARROW", handleArrow);
bus.on("EXPORTED_ALIAS", handleExportedAlias);
bus.on("ADD_AGAIN", handleAddAgain);

const handleLocal = (payload: { n: number }) => {
  counter.value.count = payload.n + 1;
};
bus.on("LOCAL", handleLocal);

const handleFnExpr = function (payload: { label: string }) {
  counter.value.label = payload.label;
};
bus.on("FN_EXPR", handleFnExpr);

function overloaded(x: string): void;
function overloaded(x: number): void;
function overloaded(_x: unknown): void {
  counter.value.label = "overloaded";
}
bus.on("OVERLOADED", overloaded);

const { handleAdd: lazyAdd } = await import("./impl");
bus.on("LAZY", lazyAdd);

// An identifier that is not a function (a type error; the corpus is not typechecked).
const notAHandler = 7;
bus.on("NOT_A_HANDLER", notAHandler);

// A default-library function as the handler.
bus.on("TIMER", setTimeout);

const messageHandlers = {
  INC: handleAdd,
  DEC: remove,
  LOCAL_AGAIN: handleLocal,
  "QUOTED-KEY": handleArrow,
  INLINE: () => {
    counter.value.count = 2;
  },
};
bus.on("MAP", () => messageHandlers);
