workspace "Unknown Project" "" {

  !identifiers hierarchical

  model {

    user = person "User" "Extension user"



    extension = softwareSystem "Unknown Project" {

      server = container "Server" "// Router/Server file - this is where Polly detects handlers" "Extension Context" {
        message_handler = component "Message Handler" "Processes message messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "server.ts:18"
            "Technology" "TypeScript, WebSocket"
            "Pattern" "Message Handler"
          }
        }
        query_handler = component "Query Handler" "Processes query messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "server.ts:23"
            "Technology" "TypeScript, WebSocket"
            "Message Type" "Query"
            "Pattern" "Query Handler"
          }
        }
        command_handler = component "Command Handler" "Processes command messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "server.ts:27"
            "Technology" "TypeScript, WebSocket"
            "Message Type" "Command"
            "Pattern" "Command Handler"
          }
        }
        user_service = component "User Service" "Business logic service" {
          tags "Service" "Auto-detected"
        }
        database = component "Database" "Business logic service" {
          tags "Service" "Auto-detected"
        }
        db_client = component "Db Client" "Business logic service" {
          tags "Service" "Auto-detected"
        }
        repositories = component "Repositories" "Business logic service" {
          tags "Service" "Auto-detected"
        }

        message_handler -> user_service "Calls listUsers()" {
          technology "Function Call"
          tags "Auto-detected"
        }
        message_handler -> database "Reads from database" {
          technology "SQL"
          tags "Auto-detected"
        }
        message_handler -> db_client "Calls query()" {
          technology "Function Call"
          tags "Auto-detected"
        }
        message_handler -> repositories "Calls create()" {
          technology "Function Call"
          tags "Auto-detected"
        }
        query_handler -> user_service "Calls listUsers()" {
          technology "Function Call"
          tags "Auto-detected"
        }
        query_handler -> database "Reads from database" {
          technology "SQL"
          tags "Auto-detected"
        }
        query_handler -> db_client "Calls query()" {
          technology "Function Call"
          tags "Auto-detected"
        }
        command_handler -> repositories "Calls create()" {
          technology "Function Call"
          tags "Auto-detected"
        }
      }



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

    component extension.server "Components_Server" {
      include *
      autoLayout tb
    }

    dynamic extension.server "Message Processing Flow" "Shows message processing flow through handlers and services" {
      message_handler -> user_service "Calls listUsers()"
      message_handler -> database "Reads from database"
      message_handler -> db_client "Calls query()"
      message_handler -> repositories "Calls create()"
      query_handler -> user_service "Calls listUsers()"
      query_handler -> database "Reads from database"
      query_handler -> db_client "Calls query()"
      command_handler -> repositories "Calls create()"
      autoLayout lr
    }

    styles {
      element "Message Handler" {
        shape Hexagon
        background #1168bd
        color #ffffff
        fontSize 14
      }
      element "Query" {
        background #51cf66
        color #2d3436
      }
      element "Command" {
        background #ff922b
        color #2d3436
      }
      element "Authentication" {
        background #ff6b6b
        color #ffffff
      }
      element "Subscribe" {
        background #845ef7
        color #ffffff
      }
      element "Service" {
        shape RoundedBox
        background #95a5a6
        color #ffffff
      }
      element "Repository" {
        shape Cylinder
        background #74b9ff
        color #2d3436
      }
      element "Database" {
        shape Cylinder
        background #0984e3
        color #ffffff
      }
      element "External System" {
        background #e17055
        color #ffffff
      }
      element "Container" {
        background #6c5ce7
        color #ffffff
      }
      relationship "Relationship" {
        thickness 2
        color #707070
        routing Orthogonal
        fontSize 12
      }
      relationship "Sync" {
        thickness 2
        style Solid
      }
      relationship "Async" {
        thickness 2
        style Dashed
      }
      relationship "Database" {
        thickness 3
        color #0984e3
        style Solid
      }
      theme https://static.structurizr.com/themes/default/theme.json
    }

  }

}