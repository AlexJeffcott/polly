/**
 * Window type extensions for test result storage
 */

declare global {
  interface Window {
    __POPUP_TEST_RESULTS__?: unknown
    __POPUP_INIT_RESULTS__?: unknown
    __CONTENT_TEST_RESULTS__?: unknown
    __OPTIONS_TEST_RESULTS__?: unknown
    __DEVTOOLS_TEST_RESULTS__?: unknown
    __DEVTOOLS_INIT_RESULTS__?: unknown
    __SIDEPANEL_TEST_RESULTS__?: unknown
  }
}

export {}
