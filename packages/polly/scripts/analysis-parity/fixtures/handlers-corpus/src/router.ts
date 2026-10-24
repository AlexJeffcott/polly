import { assertPing, isPing, isPong, isReset, looksCustom, type Msg } from "./guards";
import { isPingAlias } from "./reexport";

function isLocalPong(m: Msg): m is Msg & { type: "pong" } {
  return m.type === "pong";
}

export function route(m: Msg) {
  if (isPing(m)) {
    console.log("ping");
  } else if (isPong(m)) {
    console.log("pong");
  } else if (isReset(m)) {
    console.log("reset");
  } else if (looksCustom(m)) {
    console.log("custom");
  } else if (isPingAlias(m)) {
    console.log("ping again");
  } else if (isLocalPong(m)) {
    console.log("local pong");
  } else if (isAmbientMessage(m)) {
    console.log("ambient");
  } else if (isFinite(Number(m.type))) {
    console.log("number");
  } else if (assertPing(m)) {
    console.log("asserted");
  }
}
