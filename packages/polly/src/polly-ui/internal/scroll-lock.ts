/**
 * Scroll lock.
 *
 * Reference-counted. Multiple overlays can request a lock; the body
 * stays locked until every request releases. A scrollbar-gutter token
 * is written at acquire time so content behind the overlay doesn't
 * reflow when the bar disappears.
 */

let count = 0;

export function acquireScrollLock(): () => void {
  if (count === 0) {
    const html = document.documentElement;
    const gutter = window.innerWidth - html.clientWidth;
    html.style.setProperty("--polly-scrollbar-gutter", `${gutter}px`);
    html.setAttribute("data-polly-scroll-locked", "true");
  }
  count += 1;
  let released = false;
  return () => {
    if (released) return;
    released = true;
    count -= 1;
    if (count <= 0) {
      count = 0;
      const html = document.documentElement;
      html.removeAttribute("data-polly-scroll-locked");
      html.style.removeProperty("--polly-scrollbar-gutter");
    }
  };
}
