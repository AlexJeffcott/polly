import { describe, expect, test } from "bun:test";
import { messageFromWireHeader } from "@/shared/lib/wire-message";

const data = new Uint8Array([1, 2]);

describe("messageFromWireHeader", () => {
  test("carries every header field plus data", () => {
    const message = messageFromWireHeader(
      {
        type: "ephemeral",
        senderId: "a",
        targetId: "b",
        documentId: "d",
        count: 3,
        sessionId: "s",
      },
      data,
      "T"
    );
    expect<unknown>(message).toEqual({
      type: "ephemeral",
      senderId: "a",
      targetId: "b",
      documentId: "d",
      count: 3,
      sessionId: "s",
      data,
    });
  });

  test("leaves documentId off when the header has none", () => {
    const message = messageFromWireHeader({ type: "sync", senderId: "", targetId: "b" }, data, "T");
    expect("documentId" in message).toBe(false);
    expect<unknown>(message.senderId).toBe("");
  });

  test("the payload replaces a data field in the header", () => {
    const message = messageFromWireHeader(
      { type: "sync", senderId: "a", targetId: "b", data: "header-data" },
      data,
      "T"
    );
    expect(message.data).toBe(data);
  });

  test("throws, naming the caller, on a malformed header", () => {
    expect(() => messageFromWireHeader(null, data, "Label")).toThrow(/^Label: /);
    expect(() => messageFromWireHeader([], data, "T")).toThrow(/not an object/);
    expect(() => messageFromWireHeader({ senderId: "a", targetId: "b" }, data, "T")).toThrow(
      /type/
    );
    expect(() => messageFromWireHeader({ type: "sync", targetId: "b" }, data, "T")).toThrow(
      /senderId/
    );
    expect(() => messageFromWireHeader({ type: "sync", senderId: "a" }, data, "T")).toThrow(
      /targetId/
    );
    expect(() =>
      messageFromWireHeader(
        { type: "sync", senderId: "a", targetId: "b", documentId: 1 },
        data,
        "T"
      )
    ).toThrow(/documentId/);
  });
});
