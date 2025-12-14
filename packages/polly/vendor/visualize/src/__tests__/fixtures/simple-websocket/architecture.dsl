workspace "test-websocket-server" "" {

  !identifiers hierarchical

  model {

    user = person "User" "Extension user"



    extension = softwareSystem "test-websocket-server" {

      server = container "Server" "// WebSocket server entry point" "Extension Context" {
        connection_handler = component "Connection Handler" "Processes connection messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "src/server.ts:9"
            "Technology" "TypeScript, WebSocket"
            "Pattern" "Message Handler"
          }
        }
        message_handler = component "Message Handler" "Processes message messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "src/server.ts:12"
            "Technology" "TypeScript, WebSocket"
            "Pattern" "Message Handler"
          }
        }
        close_handler = component "Close Handler" "Processes close messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "src/server.ts:22"
            "Technology" "TypeScript, WebSocket"
            "Pattern" "Message Handler"
          }
        }
        query_handler = component "Query Handler" "Processes query messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "src/server/handlers.ts:55"
            "Technology" "TypeScript, WebSocket"
            "Message Type" "Query"
            "Pattern" "Query Handler"
          }
        }
        command_handler = component "Command Handler" "Processes command messages and coordinates business logic" {
          tags "Message Handler"
          properties {
            "Source" "src/server/handlers.ts:57"
            "Technology" "TypeScript, WebSocket"
            "Message Type" "Command"
            "Pattern" "Command Handler"
          }
        }
        auth_handler = component "Auth Handler" "Processes auth messages and coordinates business logic" {
          tags "Message Handler" "Authentication"
          properties {
            "Source" "src/server/handlers.ts:59"
            "Technology" "TypeScript, WebSocket"
            "Message Type" "Authentication"
            "Pattern" "Authentication Handler"
          }
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