-------------------------- MODULE MeshSeed --------------------------
(*
  Formal specification of Polly's $meshState concurrent first-time seed.

  This spec exists to close the polly#114 gap: the polly#113 concurrent-
  seed race lived entirely outside the verify and visualise pipelines, so
  "all green" told a mesh-using consumer nothing about it. MeshSeed makes
  the seed path a first-class, model-checked property.

  The race
  --------

  When a device first reads a $meshState document it materialises the
  document against empty local storage — the loadOrSeed path in
  mesh-state.ts. If two devices do this concurrently for the same logical
  key, each writes its own copy of the initial document.

  - Pre-fix, loadOrSeed used `Automerge.from(initialDoc)`, which stamps
    the seed change with a fresh random actorId and a `Date.now()`
    timestamp. Two devices therefore produce two *distinct* Automerge
    documents — same logical content, different identity. They have no
    common ancestor, so a later sync cannot reconcile them: the two
    seeds coexist as a permanent fork.

  - The polly#113 fix switched loadOrSeed to
    `Automerge.init({ actor: deriveSeedActor(docId) })` plus
    `Automerge.change(doc, { time: 0 }, …)`. The actor is derived from
    the docId and the change time is fixed, so every device seeding the
    same key produces byte-identical content — literally the same
    document. There is nothing to reconcile.

  Model
  -----

  `SeedDeterministic` is the spec's single knob. TRUE models the
  polly#113 fix; FALSE restores the pre-fix behaviour — the same toggle
  the `POLLY_113_DISABLE_FIX` environment variable exposes in
  seedDocumentBytes. The verify CLI flips this constant when the
  environment variable is set, so a regression in the seed path is
  caught here as a TLC counterexample rather than only by a hand-written
  unit test.

  - `doc[p]` is peer p's copy of the document, or `Unseeded` before it
    has materialised one.

  - `SeedValue(p)` is the content peer p writes when it seeds. Under the
    fix it is a single shared constant (all peers agree); pre-fix it is
    tagged by the seeding peer (every peer differs). The pre-fix model
    treats every peer's seed as distinct: a specification must withstand
    what is *possible*, and pre-fix divergence is possible, so the worst
    case is the honest one. A nondeterministic seed choice would only
    multiply states without adding insight — the divergent branch is
    what matters and TLC explores it either way.

  - `Sync` delivers a seeded document to a peer that holds none. A peer
    that has already seeded independently is never overwritten: its
    document and the remote one have no common ancestor, so no merge
    reconciles them. Modelling the fork this way is sound for the safety
    property below — `SeedConvergence` is violated the moment two peers
    hold distinct documents, and no later step can un-violate a safety
    invariant TLC has already reported.

  One document is enough
  ----------------------

  The polly#113 race is per-docId. Distinct $meshState documents seed
  through independent loadOrSeed calls, hold independent storage entries,
  and never share state — there is no action by which one document's
  seed influences another's. A model of one document is therefore a
  sound representative of any number of them: the reachable seed/sync
  interleavings of N independent documents are exactly the product of
  N copies of this model, and a safety invariant that holds on one copy
  holds on the product. Modelling one document keeps the state space
  minimal without weakening the result.

  Properties verified
  -------------------

  1. TypeOK — type safety across every transition.

  2. SeedConvergence — every peer that holds the document holds the same
     one. Under the fix this is invariant. Pre-fix, the trace
     `Seed(p)` then `Seed(q)` reaches a state where p and q hold
     distinct documents and the invariant fails — that failure is the
     polly#113 race, surfaced by model checking.

  3. EventuallySeeded (liveness) — every peer eventually materialises
     the document. Holds under both settings of SeedDeterministic; it
     is the property that earns the WF_vars(Next) fairness conjunct.
     Weak fairness on the whole next-state relation suffices because the
     model is monotone: every step moves one peer from Unseeded to
     seeded and none ever back, so no step can be starved of progress.
*)

CONSTANTS
    Peers,              \* Set of mesh peer identifiers
    SeedDeterministic   \* TRUE = polly#113 fix; FALSE = pre-fix seed race

VARIABLES
    doc                 \* [Peers -> SeedValues \cup {Unseeded}]

vars == <<doc>>

\* A peer that has not yet materialised the document.
Unseeded == "unseeded"

\* The content a peer writes when it first seeds the document. Under the
\* fix every peer produces the same bytes, so the value is one shared
\* constant; pre-fix each peer produces a distinct document, modelled as
\* a value tagged by the seeding peer.
SeedValue(p) == IF SeedDeterministic THEN "seed" ELSE p

\* The set of all possible seeded values, for the type invariant.
SeedValues == IF SeedDeterministic THEN {"seed"} ELSE Peers

-----------------------------------------------------------------------------

(* Initial state: no peer has materialised the document. *)

Init ==
    doc = [p \in Peers |-> Unseeded]

-----------------------------------------------------------------------------

(* Actions *)

(* A peer materialises the document for the first time against empty
   local storage — Polly's $meshState loadOrSeed path. *)
Seed(p) ==
    /\ doc[p] = Unseeded
    /\ doc' = [doc EXCEPT ![p] = SeedValue(p)]

(* Sync delivers a seeded peer's document to a peer that holds none.
   A peer that has already seeded independently is never overwritten —
   see the header note on why that is sound for SeedConvergence. *)
Sync(src, dst) ==
    /\ src # dst
    /\ doc[src] # Unseeded
    /\ doc[dst] = Unseeded
    /\ doc' = [doc EXCEPT ![dst] = doc[src]]

-----------------------------------------------------------------------------

(* Next-state relation *)

Next ==
    \/ \E p \in Peers : Seed(p)
    \/ \E src, dst \in Peers : Sync(src, dst)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

(* Invariants *)

(* Type safety: every peer's slot is Unseeded or a valid seeded value. *)
TypeOK ==
    doc \in [Peers -> SeedValues \cup {Unseeded}]

(* Seed convergence: every peer that holds the document holds the same
   one. Under the polly#113 fix (SeedDeterministic = TRUE) this is
   invariant. Pre-fix (FALSE) the trace Seed(p) ; Seed(q) reaches a
   state where p and q hold distinct documents and TLC reports the
   violation — that is the polly#113 race. *)
SeedConvergence ==
    \A p, q \in Peers :
        (doc[p] # Unseeded /\ doc[q] # Unseeded) => doc[p] = doc[q]

-----------------------------------------------------------------------------

(* Liveness *)

(* Every peer eventually materialises the document. Holds under both
   settings of SeedDeterministic — see the header note on why weak
   fairness on Next suffices for this monotone model. *)
EventuallySeeded ==
    <>(\A p \in Peers : doc[p] # Unseeded)

=============================================================================
