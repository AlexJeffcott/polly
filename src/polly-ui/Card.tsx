/**
 * Card — compound primitive that composes Surface for each named slot.
 *
 * Card is the first compound that is purely a re-skin of Surface — no
 * behavioural layer. Header, Body, and Footer are each Surfaces with
 * sensible defaults; Root is a raised Surface that wraps them. Every
 * slot accepts the full SurfaceProps, so consumers retint, override, or
 * reach for raw padding without reaching past the primitive.
 */

import type { JSX } from "preact";
import { Surface, type SurfaceProps } from "./Surface.tsx";

export type CardProps = SurfaceProps;
export type CardSlotProps = SurfaceProps;

function Root(props: CardProps): JSX.Element {
  const { variant = "raised", radius = "md", ...rest } = props;
  return (
    <Surface variant={variant} radius={radius} data-polly-card {...rest}>
      {props.children}
    </Surface>
  );
}

function Header(props: CardSlotProps): JSX.Element {
  const {
    padding = "var(--polly-space-md) var(--polly-space-lg)",
    border = "default",
    borderSides = "block-end",
    ...rest
  } = props;
  return (
    <Surface
      padding={padding}
      border={border}
      borderSides={borderSides}
      data-polly-card-header
      {...rest}
    >
      {props.children}
    </Surface>
  );
}

function Body(props: CardSlotProps): JSX.Element {
  const { padding = "var(--polly-space-lg)", ...rest } = props;
  return (
    <Surface padding={padding} data-polly-card-body {...rest}>
      {props.children}
    </Surface>
  );
}

function Footer(props: CardSlotProps): JSX.Element {
  const {
    padding = "var(--polly-space-md) var(--polly-space-lg)",
    border = "default",
    borderSides = "block-start",
    ...rest
  } = props;
  return (
    <Surface
      padding={padding}
      border={border}
      borderSides={borderSides}
      data-polly-card-footer
      {...rest}
    >
      {props.children}
    </Surface>
  );
}

export const Card = { Root, Header, Body, Footer };
