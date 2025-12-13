workspace "@fairfox/polly" "Multi-execution-context framework with reactive state and cross-context messaging for Chrome extensions, PWAs, and worker-based applications" {

  !identifiers hierarchical

  model {

    user = person "User" "Extension user"



    extension = softwareSystem "@fairfox/polly" {

      main = container "Main" "/**" "Extension Context" {
      }

      extension.background -> extension.content "Sends DOM_QUERY"
      extension.devtools -> extension.content "Sends DOM_QUERY"
      extension.popup -> extension.content "Sends DOM_QUERY"
      extension.devtools -> extension.content "Sends DEVTOOLS_INSPECT_ELEMENT"
      extension.background -> extension.offscreen "Sends CLIPBOARD_WRITE"
      extension.devtools -> extension.unknown "Sends PAGE_CALL_FN"

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

    dynamic extension "General Flow" "Message flow through the system" {
      user -> extension.devtools "Interacts"
      extension.background -> extension.content "DOM_QUERY"
      extension.devtools -> extension.content "DOM_QUERY"
      extension.popup -> extension.content "DOM_QUERY"
      extension.devtools -> extension.content "DEVTOOLS_INSPECT_ELEMENT"
      extension.background -> extension.offscreen "CLIPBOARD_WRITE"
      extension.devtools -> extension.unknown "PAGE_CALL_FN"
      autoLayout lr
    }

    styles {
    }

  }

}