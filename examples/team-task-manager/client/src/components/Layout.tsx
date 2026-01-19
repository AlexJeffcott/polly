import type { ComponentChildren, JSX } from "preact";

type Props = {
  children: ComponentChildren;
  rows?: string;
  columns?: string;
  gap?: string;
  padding?: string;
  justifyItems?: "start" | "end" | "center" | "stretch";
  alignItems?: "start" | "end" | "center" | "stretch";
  justifyContent?:
    | "start"
    | "end"
    | "center"
    | "stretch"
    | "space-between"
    | "space-around"
    | "space-evenly";
  alignContent?:
    | "start"
    | "end"
    | "center"
    | "stretch"
    | "space-between"
    | "space-around"
    | "space-evenly";
  autoFlow?: "row" | "column" | "dense" | "row dense" | "column dense";
  autoRows?: string;
  autoColumns?: string;
  className?: string;
  style?: JSX.CSSProperties;
};

export function Layout({
  children,
  rows,
  columns,
  gap,
  padding,
  justifyItems,
  alignItems,
  justifyContent,
  alignContent,
  autoFlow,
  autoRows,
  autoColumns,
  className,
  style: customStyle,
}: Props) {
  const style: JSX.CSSProperties = { ...customStyle };

  if (rows) style.gridTemplateRows = rows;
  if (columns) style.gridTemplateColumns = columns;
  if (gap) style.gap = gap;
  if (padding) style.padding = padding;
  if (justifyItems) style.justifyItems = justifyItems;
  if (alignItems) style.alignItems = alignItems;
  if (justifyContent) style.justifyContent = justifyContent;
  if (alignContent) style.alignContent = alignContent;
  if (autoFlow) style.gridAutoFlow = autoFlow;
  if (autoRows) style.gridAutoRows = autoRows;
  if (autoColumns) style.gridAutoColumns = autoColumns;

  const classNames = ["layout", className].filter(Boolean).join(" ");

  return (
    <div class={classNames} style={style}>
      {children}
    </div>
  );
}
