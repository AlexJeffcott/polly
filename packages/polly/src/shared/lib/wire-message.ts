/**
 * Rebuild an automerge-repo {@link Message} from the JSON header and binary
 * payload of the length-prefixed wire frame MeshWebRTCAdapter and
 * MeshNetworkAdapter both use.
 */

import type { Message } from "@automerge/automerge-repo/slim";
import { toDocumentId, toPeerId } from "./branded";
import { isRecord, readString } from "./guards";

/**
 * The message the header describes, carrying every header field plus
 * `data`. Throws when the header is not an object with string `type`,
 * `senderId` and `targetId`, or carries a non-string `documentId`; the
 * callers already treat a throw from their deserialiser as a dropped frame.
 */
export function messageFromWireHeader(header: unknown, data: Uint8Array, label: string): Message {
  if (!isRecord(header)) {
    throw new Error(`${label}: message header is not an object.`);
  }
  const type = readString(header["type"]);
  const senderId = readString(header["senderId"]);
  const targetId = readString(header["targetId"]);
  if (type === undefined || senderId === undefined || targetId === undefined) {
    throw new Error(`${label}: message header lacks a string type, senderId or targetId.`);
  }
  const message: Message = {
    ...header,
    type,
    senderId: toPeerId(senderId),
    targetId: toPeerId(targetId),
    data,
  };
  const documentId = header["documentId"];
  if (documentId !== undefined) {
    const id = readString(documentId);
    if (id === undefined) {
      throw new Error(`${label}: message header documentId is not a string.`);
    }
    message.documentId = toDocumentId(id);
  }
  return message;
}
