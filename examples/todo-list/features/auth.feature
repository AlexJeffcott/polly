Feature: Signing in and out
  As a todo-list user
  I want to sign in and out
  So that my todos are tied to my account and not a guest session

  Scenario: A signed-out user can sign in
    Given the user is signed out
    When the user signs in as "admin"
    Then the user is signed in
    And their role is "admin"

  Scenario: Signing out returns the user to a guest session
    Given the user is signed in as "user"
    When the user signs out
    Then the user is signed out
    And their role is "guest"

  @formal
  Scenario: A guest sign-in is refused
    # Precondition-only: requires(payload.role !== "guest") is a runtime no-op,
    # so the runtime cannot observe this rejection. The runner defers it; the
    # guarantee lives in the TLA+ model (polly verify --witness).
    Given the user is signed out
    When the user attempts to sign in as a guest
    Then the user is signed out

  @forbidden
  Scenario: A signed-in guest is an impossible state
    # A safety claim, not an example: there is no path to a logged-in guest.
    # The runner defers it; `polly verify --witness` proves the state unreachable
    # (and would fail, with the trace, if any handler made it reachable).
    Then a signed-in guest exists
