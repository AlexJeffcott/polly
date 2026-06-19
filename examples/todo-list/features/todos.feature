Feature: Managing todos
  As a todo-list user
  I want to add, complete and clear todos
  So that I can track what I still have to do

  Scenario: A new todo appears in the list
    Given the todo list is empty
    When a todo "Buy milk" is added
    Then the list contains 1 todo
    And the list contains the todo "Buy milk"

  Scenario: Completing a todo marks it done
    Given a todo "Write the spec" exists
    When that todo is completed
    Then that todo is marked done

  @negative
  Scenario: Completing a todo that does not exist is refused
    # Runtime-observable: the handler returns { success: false } for a missing id.
    Given a todo "Write the spec" exists
    When a todo with id "ghost" is completed
    Then the change is refused

  @negative
  Scenario: Clearing completed todos removes only the completed ones
    Given a completed todo "Old task" and an active todo "New task" exist
    When completed todos are cleared
    Then the list contains the todo "New task"
    And the list does not contain the todo "Old task"
