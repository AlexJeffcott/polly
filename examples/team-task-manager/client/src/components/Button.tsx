import type { ComponentChildren, JSX } from "preact";

export type ButtonTier = "primary" | "secondary" | "tertiary";
export type ButtonSize = "normal" | "small";

type BaseProps = {
  tier?: ButtonTier;
  size?: ButtonSize;
  disabled?: boolean;
  fullWidth?: boolean;
  className?: string;
  children: ComponentChildren;
};

type AsButton = BaseProps & {
  href?: never;
  onPress?: (e: Event) => void;
  type?: "button" | "submit" | "reset";
};

type AsLink = BaseProps & {
  href: string;
  onPress?: (e: Event) => void;
  type?: never;
};

export type ButtonProps = AsButton | AsLink;

export function Button({
  tier = "secondary",
  size = "normal",
  disabled = false,
  fullWidth = false,
  className,
  onPress,
  type = "button",
  children,
  ...props
}: ButtonProps) {
  const classes = [
    "btn",
    `btn-${tier}`,
    size === "small" && "btn-small",
    fullWidth && "btn-full-width",
    className,
  ]
    .filter(Boolean)
    .join(" ");

  const handleClick = (e: Event) => {
    if (!disabled && onPress) {
      onPress(e);
    }
  };

  // Render as link if href is provided
  if ("href" in props && props.href) {
    return (
      <a
        class={classes}
        href={disabled ? undefined : props.href}
        onClick={handleClick}
        aria-disabled={disabled}
      >
        {children}
      </a>
    );
  }

  return (
    <button class={classes} type={type} disabled={disabled} onClick={handleClick}>
      {children}
    </button>
  );
}
