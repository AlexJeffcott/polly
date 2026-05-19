import { describe, expect, test } from "bun:test";
import {
  type Access,
  and,
  anyOfPeers,
  anyone,
  groupAccess,
  nobody,
  not,
  onlyPeer,
  or,
  ownerAccess,
  type PeerIdentity,
  publicAccess,
  readOnlyExcept,
} from "@/shared/lib/access";

const id = (peerId: string, metadata?: Record<string, unknown>): PeerIdentity => ({
  peerId,
  ...(metadata ? { metadata } : {}),
});

describe("primitive predicates", () => {
  test("anyone() accepts every identity", () => {
    const pred = anyone();
    expect(pred(id("a"))).toBe(true);
    expect(pred(id("b"))).toBe(true);
    expect(pred(id(""))).toBe(true);
  });

  test("nobody() rejects every identity", () => {
    const pred = nobody();
    expect(pred(id("a"))).toBe(false);
    expect(pred(id("b"))).toBe(false);
    expect(pred(id(""))).toBe(false);
  });

  test("onlyPeer() accepts exactly the named peer", () => {
    const pred = onlyPeer("alice");
    expect(pred(id("alice"))).toBe(true);
    expect(pred(id("bob"))).toBe(false);
    expect(pred(id(""))).toBe(false);
  });

  test("anyOfPeers() accepts any peer in the set", () => {
    const pred = anyOfPeers(["alice", "bob", "carol"]);
    expect(pred(id("alice"))).toBe(true);
    expect(pred(id("bob"))).toBe(true);
    expect(pred(id("carol"))).toBe(true);
    expect(pred(id("dave"))).toBe(false);
  });

  test("anyOfPeers() captures the peer list at factory time", () => {
    const peerIds: string[] = ["alice", "bob"];
    const pred = anyOfPeers(peerIds);
    peerIds.push("carol");
    // Mutation after factory does not affect the predicate.
    expect(pred(id("carol"))).toBe(false);
    expect(pred(id("alice"))).toBe(true);
  });

  test("anyOfPeers() with empty list rejects everyone", () => {
    const pred = anyOfPeers([]);
    expect(pred(id("alice"))).toBe(false);
  });
});

describe("compositors", () => {
  test("and() accepts only when both predicates accept", () => {
    const pred = and(onlyPeer("alice"), anyone());
    expect(pred(id("alice"))).toBe(true);
    expect(pred(id("bob"))).toBe(false);
  });

  test("and() with two nobodies rejects everyone", () => {
    const pred = and(nobody(), nobody());
    expect(pred(id("alice"))).toBe(false);
  });

  test("and() short-circuits on false", () => {
    let rightCalled = false;
    const pred = and(nobody(), (i) => {
      rightCalled = true;
      return i.peerId === "alice";
    });
    pred(id("alice"));
    expect(rightCalled).toBe(false);
  });

  test("or() accepts when either predicate accepts", () => {
    const pred = or(onlyPeer("alice"), onlyPeer("bob"));
    expect(pred(id("alice"))).toBe(true);
    expect(pred(id("bob"))).toBe(true);
    expect(pred(id("carol"))).toBe(false);
  });

  test("or() with two nobodies rejects everyone", () => {
    const pred = or(nobody(), nobody());
    expect(pred(id("alice"))).toBe(false);
  });

  test("or() short-circuits on true", () => {
    let rightCalled = false;
    const pred = or(anyone(), (i) => {
      rightCalled = true;
      return i.peerId === "alice";
    });
    pred(id("alice"));
    expect(rightCalled).toBe(false);
  });

  test("not() inverts a predicate", () => {
    const pred = not(onlyPeer("alice"));
    expect(pred(id("alice"))).toBe(false);
    expect(pred(id("bob"))).toBe(true);
  });

  test("not(not(p)) is equivalent to p", () => {
    const pred = not(not(onlyPeer("alice")));
    expect(pred(id("alice"))).toBe(true);
    expect(pred(id("bob"))).toBe(false);
  });
});

describe("publicAccess", () => {
  test("allows read and write for everyone", () => {
    const access: Access = publicAccess();
    expect(access.read(id("alice"))).toBe(true);
    expect(access.write(id("bob"))).toBe(true);
    expect(access.read(id(""))).toBe(true);
  });
});

describe("ownerAccess", () => {
  test("allows the named owner to read and write", () => {
    const access = ownerAccess("alice");
    expect(access.read(id("alice"))).toBe(true);
    expect(access.write(id("alice"))).toBe(true);
  });

  test("rejects non-owners for both read and write", () => {
    const access = ownerAccess("alice");
    expect(access.read(id("bob"))).toBe(false);
    expect(access.write(id("bob"))).toBe(false);
  });
});

describe("groupAccess", () => {
  test("allows any member to read and write", () => {
    const access = groupAccess(["alice", "bob"]);
    expect(access.read(id("alice"))).toBe(true);
    expect(access.read(id("bob"))).toBe(true);
    expect(access.write(id("alice"))).toBe(true);
    expect(access.write(id("bob"))).toBe(true);
  });

  test("rejects non-members for both read and write", () => {
    const access = groupAccess(["alice", "bob"]);
    expect(access.read(id("carol"))).toBe(false);
    expect(access.write(id("carol"))).toBe(false);
  });

  test("with an empty group rejects everyone", () => {
    const access = groupAccess([]);
    expect(access.read(id("alice"))).toBe(false);
    expect(access.write(id("alice"))).toBe(false);
  });
});

describe("readOnlyExcept", () => {
  test("read is public, write is gated by the writer predicate", () => {
    const access = readOnlyExcept(onlyPeer("alice"));
    expect(access.read(id("alice"))).toBe(true);
    expect(access.read(id("bob"))).toBe(true);
    expect(access.read(id("carol"))).toBe(true);
    expect(access.write(id("alice"))).toBe(true);
    expect(access.write(id("bob"))).toBe(false);
    expect(access.write(id("carol"))).toBe(false);
  });

  test("composes with a group writer predicate", () => {
    const access = readOnlyExcept(anyOfPeers(["alice", "bob"]));
    expect(access.read(id("carol"))).toBe(true);
    expect(access.write(id("alice"))).toBe(true);
    expect(access.write(id("bob"))).toBe(true);
    expect(access.write(id("carol"))).toBe(false);
  });
});

describe("typed narrowing", () => {
  test("predicates accept narrower identity types", () => {
    interface UserIdentity extends PeerIdentity {
      userId: string;
    }
    const pred = onlyPeer<UserIdentity>("alice");
    const user: UserIdentity = { peerId: "alice", userId: "u-1" };
    expect(pred(user)).toBe(true);
  });
});
