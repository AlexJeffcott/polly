workspace "Todo List Example" "A todo list extension demonstrating verification primitives" {

  !identifiers hierarchical

  model {

    user = person "User" "Extension user"



    extension = softwareSystem "Todo List Example" {

      background = container "Background" "// Background script entry point" "Service Worker / Background Script" {
        user_login_handler = component "User Login Handler" "Authenticates users and establishes sessions" {
          tags "Message Handler" "Authentication" "User Management"
        }
        user_logout_handler = component "User Logout Handler" "Terminates user sessions and clears credentials" {
          tags "Message Handler" "Authentication" "User Management"
        }
        todo_add_handler = component "Todo Add Handler" "Creates new todo items and persists to storage" {
          tags "Message Handler" "CRUD" "Todo Management"
        }
        todo_toggle_handler = component "Todo Toggle Handler" "Updates todo item state and syncs with storage" {
          tags "Message Handler" "CRUD" "Todo Management"
        }
        todo_remove_handler = component "Todo Remove Handler" "Removes todo items from storage" {
          tags "Message Handler" "CRUD" "Todo Management"
        }
        todo_clear_completed_handler = component "Todo Clear Completed Handler" "Clears all todo items matching criteria" {
          tags "Message Handler" "Todo Management"
        }
        get_state_handler = component "Get State Handler" "Retrieves get state data from storage" {
          tags "Message Handler" "Query" "State Management"
        }
        get_todos_handler = component "Get Todos Handler" "Retrieves get todos data from storage" {
          tags "Message Handler" "Query" "Todo Management"
        }

        user_login_handler -> get_state_handler "Updates state" {
          tags "Implicit"
        }
        user_logout_handler -> get_state_handler "Updates state" {
          tags "Implicit"
        }
        todo_add_handler -> get_state_handler "Updates state" {
          tags "Implicit"
        }
        todo_toggle_handler -> get_state_handler "Updates state" {
          tags "Implicit"
        }
        todo_remove_handler -> get_state_handler "Updates state" {
          tags "Implicit"
        }
        todo_clear_completed_handler -> get_state_handler "Updates state" {
          tags "Implicit"
        }
        user_login_handler -> get_todos_handler "Updates state" {
          tags "Implicit"
        }
        user_logout_handler -> get_todos_handler "Updates state" {
          tags "Implicit"
        }
        todo_add_handler -> get_todos_handler "Updates state" {
          tags "Implicit"
        }
        todo_toggle_handler -> get_todos_handler "Updates state" {
          tags "Implicit"
        }
        todo_remove_handler -> get_todos_handler "Updates state" {
          tags "Implicit"
        }
        todo_clear_completed_handler -> get_todos_handler "Updates state" {
          tags "Implicit"
        }
      }

      extension.popup -> extension.background "Sends USER_LOGIN"
      extension.popup -> extension.background "Sends USER_LOGOUT"
      extension.popup -> extension.background "Sends TODO_ADD"
      extension.popup -> extension.background "Sends TODO_TOGGLE"
      extension.popup -> extension.background "Sends TODO_REMOVE"
      extension.popup -> extension.background "Sends TODO_CLEAR_COMPLETED"
      extension.popup -> extension.background "Sends GET_STATE"
      extension.popup -> extension.background "Sends GET_STATE"
      extension.popup -> extension.background "Sends GET_STATE"
      extension.popup -> extension.background "Sends GET_STATE"
      extension.popup -> extension.background "Sends GET_STATE"
      extension.popup -> extension.background "Sends GET_STATE"

    }

  }

  views {

    systemContext extension "SystemContext" {
      include *
      autoLayout lr
    }

    container extension "Containers" {
      include *
      autoLayout lr
    }

    component extension.background "Components_Background" {
      include *
      autoLayout tb
    }

    dynamic extension "Authentication Flow" "User authentication and session management" {
      user -> extension.popup "Initiates login"
      extension.popup -> extension.background "Authenticate user"
      extension.popup -> extension.background "End session"
      autoLayout lr
    }

    dynamic extension "Todo Flow" "Todo item creation, updates, and retrieval" {
      user -> extension.popup "Manages todo items"
      extension.popup -> extension.background "Create item"
      extension.popup -> extension.background "Update item"
      extension.popup -> extension.background "Delete item"
      extension.popup -> extension.background "Clear items"
      autoLayout lr
    }

    dynamic extension "State Flow" "Application state synchronization" {
      user -> extension.popup "Requests state"
      extension.popup -> extension.background "Retrieve data"
      extension.popup -> extension.background "Retrieve data"
      extension.popup -> extension.background "Retrieve data"
      extension.popup -> extension.background "Retrieve data"
      extension.popup -> extension.background "Retrieve data"
      extension.popup -> extension.background "Retrieve data"
      autoLayout lr
    }

    styles {
      element "extension.background" {
        background #2E7D32
        color #ffffff
      }
    }

  }

}