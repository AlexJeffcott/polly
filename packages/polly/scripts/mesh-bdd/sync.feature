Feature: Mesh sync across two devices
  As someone signed in on two devices
  I want a todo I add on one device to appear on the other
  So that my list is the same everywhere I look

  # This scenario is the only one that crosses the real process / network /
  # device boundary: two cold browser peers, a real signalling relay, WebRTC,
  # and Automerge convergence — driven through the documented createMeshClient
  # bootstrap, never a hand-wired transport (the polly#57 lesson). The step
  # definitions drive Puppeteer pages and the e2e-mesh kit; the scenario itself
  # stays declarative.
  Scenario: A todo added on one device appears on the other
    Given two devices are connected to the same mesh
    When device A adds the todo "buy milk"
    Then device B sees the todo "buy milk"
    When device B adds the todo "walk dog"
    Then device A sees the todo "walk dog"
    And both devices show 2 todos
