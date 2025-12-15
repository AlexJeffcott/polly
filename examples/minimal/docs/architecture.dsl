workspace "Minimal Example" "Dead simple @fairfox/polly example" {

  !identifiers hierarchical

  model {

    user = person "User" "Extension user"



    extension = softwareSystem "Minimal Example" {

      background = container "Background" "// Background script - runs when extension loads" "Service Worker / Background Script" {
        ping_handler = component "Ping Handler" "Processes PING messages and coordinates business logic" {
          tags "Message Handler"
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

    component extension.background "Components_Background" {
      include *
      autoLayout tb
    }



    styles {
      element "extension.background" {
        background #2E7D32
        color #ffffff
      }
    }

  }

}