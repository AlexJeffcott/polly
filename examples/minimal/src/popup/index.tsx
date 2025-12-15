// Popup UI - appears when clicking extension icon
import { render } from "preact";
import { counter } from "../shared/state";

function Popup() {
  return (
    <div style={{ padding: "20px", minWidth: "200px" }}>
      <h2>Counter Demo</h2>
      <p>Count: {counter.value}</p>
      <button onClick={() => counter.value++}>Increment</button>
      <button onClick={() => counter.value--}>Decrement</button>
      <button onClick={() => (counter.value = 0)}>Reset</button>
    </div>
  );
}

render(<Popup />, document.getElementById("root")!);
