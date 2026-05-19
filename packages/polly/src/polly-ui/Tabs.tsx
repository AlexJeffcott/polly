/**
 * Tabs — horizontal nav with active-tab accent.
 *
 * Each button carries `data-action` (the consumer-provided action name)
 * and `data-action-id={tab.id}` so the event delegator resolves the
 * activated tab. The active tab gets `aria-current="page"` and a
 * bottom-border accent. The nav scrolls horizontally with a hidden
 * scrollbar for overflow. Internal arrangement uses <Layout>.
 */

import type { JSX } from "preact";
import { Layout } from "./Layout.tsx";
import classes from "./Tabs.module.css";

export type Tab = { id: string; label: string; disabled?: boolean };

export type TabsProps = {
  tabs: Tab[];
  activeTab: string;
  action?: string;
  className?: string;
  id?: string;
  "aria-label"?: string;
};

export function Tabs(props: TabsProps): JSX.Element {
  const { tabs, activeTab, action, className, id } = props;
  const parts = [classes["tabs"] ?? ""];
  if (className) parts.push(className);
  return (
    <nav
      id={id}
      class={parts.filter(Boolean).join(" ")}
      aria-label={props["aria-label"]}
      data-polly-ui
      data-polly-tabs
    >
      <Layout columns={`repeat(${tabs.length}, auto)`} gap="0" alignItems="end">
        {tabs.map((tab) => {
          const isActive = activeTab === tab.id;
          const tabClass = isActive ? `${classes["tab"]} ${classes["active"]}` : classes["tab"];
          return (
            <button
              key={tab.id}
              type="button"
              class={tabClass}
              disabled={tab.disabled}
              aria-current={isActive ? "page" : undefined}
              data-action={action}
              data-action-id={tab.id}
            >
              {tab.label}
            </button>
          );
        })}
      </Layout>
    </nav>
  );
}
