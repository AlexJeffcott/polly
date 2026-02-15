// Popup UI - appears when clicking extension icon
import { render } from "preact";
import { counter } from "../shared/state";

function Popup() {
  return (
    <div style={{ padding: "20px", minWidth: "200px" }}>
      <h2>Counter Demo</h2>
      <p>Count: {counter.value}</p>
      <button
        type="button"
        onClick={() => {
          counter.value++;
        }}
      >
        Increment
      </button>
      <button
        type="button"
        onClick={() => {
          counter.value--;
        }}
      >
        Decrement
      </button>
      <button
        type="button"
        onClick={() => {
          counter.value = 0;
        }}
      >
        Reset
      </button>
    </div>
  );
}

const rootElement = document.getElementById("root");
if (rootElement) {
  render(<Popup />, rootElement);
}
