workspace "Full-Featured Example" "Demonstrates real-world extension patterns: authentication, bookmarks, tab management, and settings" {

  !identifiers hierarchical

  model {

    user = person "User" "Extension user"



    extension = softwareSystem "Full-Featured Example" {

      background = container "Background" "/**" "Service Worker / Background Script" {
        user_login_handler = component "User Login Handler" "Authenticates users and establishes sessions" {
          tags "Message Handler" "Authentication" "User Management"
        }
        user_logout_handler = component "User Logout Handler" "Terminates user sessions and clears credentials" {
          tags "Message Handler" "Authentication" "User Management"
        }
        bookmark_add_handler = component "Bookmark Add Handler" "Creates new bookmark items and persists to storage" {
          tags "Message Handler" "CRUD"
        }
        bookmark_remove_handler = component "Bookmark Remove Handler" "Removes bookmark items from storage" {
          tags "Message Handler" "CRUD"
        }
        tab_get_current_handler = component "Tab Get Current Handler" "Retrieves tab current data from storage" {
          tags "Message Handler" "Query"
        }
        tab_open_handler = component "Tab Open Handler" "Processes TAB_OPEN messages and coordinates business logic" {
          tags "Message Handler"
        }
        settings_update_handler = component "Settings Update Handler" "Updates settings item state and syncs with storage" {
          tags "Message Handler" "CRUD"
        }
        get_settings_handler = component "Get Settings Handler" "Retrieves get settings data from storage" {
          tags "Message Handler" "Query"
        }
        get_bookmarks_handler = component "Get Bookmarks Handler" "Retrieves get bookmarks data from storage" {
          tags "Message Handler" "Query"
        }
        chrome_storage = component "Chrome Storage API" "Browser API for storage" {
          tags "Chrome API" "External"
        }
        chrome_tabs = component "Chrome Tabs API" "Browser API for tabs" {
          tags "Chrome API" "External"
        }

        user_login_handler -> chrome_storage "Writes to storage"
        user_logout_handler -> chrome_storage "Writes to storage"
        bookmark_add_handler -> chrome_storage "Writes to storage"
        bookmark_remove_handler -> chrome_storage "Writes to storage"
        tab_get_current_handler -> chrome_storage "Reads from storage"
        tab_open_handler -> chrome_storage "Writes to storage"
        settings_update_handler -> chrome_storage "Writes to storage"
        get_settings_handler -> chrome_storage "Reads from storage"
        get_bookmarks_handler -> chrome_storage "Reads from storage"
        user_login_handler -> chrome_tabs "Manages browser tabs"
        user_logout_handler -> chrome_tabs "Manages browser tabs"
        bookmark_add_handler -> chrome_tabs "Manages browser tabs"
        bookmark_remove_handler -> chrome_tabs "Manages browser tabs"
        tab_get_current_handler -> chrome_tabs "Manages browser tabs"
        tab_open_handler -> chrome_tabs "Manages browser tabs"
        settings_update_handler -> chrome_tabs "Manages browser tabs"
        get_settings_handler -> chrome_tabs "Manages browser tabs"
        get_bookmarks_handler -> chrome_tabs "Manages browser tabs"
        user_login_handler -> tab_get_current_handler "Updates state" {
          tags "Implicit"
        }
        user_logout_handler -> tab_get_current_handler "Updates state" {
          tags "Implicit"
        }
        bookmark_add_handler -> tab_get_current_handler "Updates state" {
          tags "Implicit"
        }
        bookmark_remove_handler -> tab_get_current_handler "Updates state" {
          tags "Implicit"
        }
        settings_update_handler -> tab_get_current_handler "Updates state" {
          tags "Implicit"
        }
        user_login_handler -> get_settings_handler "Updates state" {
          tags "Implicit"
        }
        user_logout_handler -> get_settings_handler "Updates state" {
          tags "Implicit"
        }
        bookmark_add_handler -> get_settings_handler "Updates state" {
          tags "Implicit"
        }
        bookmark_remove_handler -> get_settings_handler "Updates state" {
          tags "Implicit"
        }
        settings_update_handler -> get_settings_handler "Updates state" {
          tags "Implicit"
        }
        user_login_handler -> get_bookmarks_handler "Updates state" {
          tags "Implicit"
        }
        user_logout_handler -> get_bookmarks_handler "Updates state" {
          tags "Implicit"
        }
        bookmark_add_handler -> get_bookmarks_handler "Updates state" {
          tags "Implicit"
        }
        bookmark_remove_handler -> get_bookmarks_handler "Updates state" {
          tags "Implicit"
        }
        settings_update_handler -> get_bookmarks_handler "Updates state" {
          tags "Implicit"
        }
      }

      extension.popup -> extension.background "Sends USER_LOGIN"
      extension.popup -> extension.background "Sends USER_LOGOUT"
      extension.popup -> extension.background "Sends BOOKMARK_ADD"
      extension.popup -> extension.background "Sends BOOKMARK_ADD"
      extension.popup -> extension.background "Sends BOOKMARK_REMOVE"
      extension.popup -> extension.background "Sends TAB_GET_CURRENT"
      extension.popup -> extension.background "Sends SETTINGS_UPDATE"

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

    dynamic extension "General Flow" "Message flow through the system" {
      user -> extension.popup "Interacts"
      extension.popup -> extension.background "Create item"
      extension.popup -> extension.background "Create item"
      extension.popup -> extension.background "Delete item"
      extension.popup -> extension.background "Retrieve data"
      extension.popup -> extension.background "Update item"
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