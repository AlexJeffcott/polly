/**
 * Popup UI.
 *
 * Shows the current user.
 */
import { h } from "./jsx";

class Component<P, S = object> {
  props!: P;
  state!: S;
}

interface CounterProps {
  start: number;
  step?: number;
  label: string;
}

type Keys = "zeta" | "alpha";
type MappedProps = { [K in Keys]: string };

/**
 * The app shell.
 * Renders the header and the counter,
 *   with an indented continuation line.
 *
 * @param props - the props
 */
export function App(props: { user: string; onLogout: () => void }) {
  chrome.tabs.create({ url: "x" });
  return (
    <div>
      <Header title={props.user} />
    </div>
  );
}

/** Just the title. */
export const Header = ({ title }: { title: string }) => <h1>{title}</h1>;

// biome-ignore lint/complexity/useArrowFunction: a function expression is the case under test
export const Footer = function (props: MappedProps) {
  if (props.alpha) {
    return <footer />;
  }
  return null;
};

// biome-ignore format: the parenthesised body is the case under test
export const Wrapped = (props: CounterProps) => (<span>{props.label}</span>);

/**
 * Counter as a class.
 */
export class Counter extends Component<CounterProps> {
  render() {
    return <span>{this.props.start}</span>;
  }
}

export class Plain {
  render() {
    return <i />;
  }
}

export function helper() {
  return <b />;
}

export function NoJsx() {
  return 1;
}

export function NoProps() {
  return <hr />;
}

void h;
