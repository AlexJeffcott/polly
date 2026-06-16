/**
 * The gallery app root — a single scrollable page cataloguing every polly-ui
 * primitive in its configurations. An in-page nav jumps between sections; a
 * theme toggle forces light/dark on the panel subtree via `data-polly-theme`
 * so both palettes can be inspected without changing the OS setting.
 *
 * The overlay hosts (OverlayRoot / Toast.Viewport / ConfirmDialog.Host) are
 * mounted here once, so the Modal, Toast, and ConfirmDialog specimens have a
 * portal target — the same wiring a real consumer app does at its root.
 */

import {
  Button,
  Cluster,
  ConfirmDialog,
  Layout,
  OverlayRoot,
  Surface,
  Text,
  Toast,
} from "../../../src/polly-ui";
import { THEMES } from "./actions.ts";
import { GALLERY_SECTIONS, type GallerySection } from "./specimens.tsx";
import { $galleryTheme } from "./stores.ts";

/** A capitalised label for a theme option. */
function themeLabel(theme: string): string {
  return theme.charAt(0).toUpperCase() + theme.slice(1);
}

/** One catalogued component: a labelled landmark with a grid of specimens. */
function Section(props: { section: GallerySection }) {
  const { section } = props;
  const headingId = `${section.id}-heading`;
  return (
    <Surface
      as="section"
      id={section.id}
      variant="plain"
      className="gallery-section"
      aria-labelledby={headingId}
    >
      <Layout gap="var(--polly-space-sm)">
        <h2 id={headingId} class="gallery-section-title">
          {section.title}
        </h2>
        <Text as="p" tone="muted">
          {section.summary}
        </Text>
        <Layout
          columns="repeat(auto-fill, minmax(min(100%, 14rem), 1fr))"
          gap="var(--polly-space-md)"
        >
          {section.render()}
        </Layout>
      </Layout>
    </Surface>
  );
}

export function GalleryApp() {
  const theme = $galleryTheme.value;
  return (
    <Surface
      variant="raised"
      padding="clamp(var(--polly-space-sm), 3vw, var(--polly-space-xl))"
      data-gallery-panel="true"
      data-polly-theme={theme === "system" ? undefined : theme}
    >
      <Layout gap="var(--polly-space-lg)">
        <Layout gap="var(--polly-space-sm)">
          <h1 class="gallery-title">Polly UI gallery</h1>
          <Text as="p" tone="muted">
            Every <Text weight="medium">@fairfox/polly/ui</Text> primitive, in its configurations —
            a reference for building polly apps, and a single surface for accessibility and
            visual-regression checks.
          </Text>
        </Layout>

        <Surface variant="callout" radius="md" padding="var(--polly-space-md)">
          <Cluster gap="var(--polly-space-sm)" align="center">
            <Text size="sm" tone="muted">
              Theme
            </Text>
            {THEMES.map((t) => (
              <Button
                key={t}
                size="small"
                tier={t === theme ? "primary" : "tertiary"}
                data-action="gallery:set-theme"
                data-action-theme={t}
                label={themeLabel(t)}
              />
            ))}
          </Cluster>
        </Surface>

        <nav aria-label="Components">
          <Cluster gap="var(--polly-space-xs)">
            {GALLERY_SECTIONS.map((section) => (
              <Button
                key={section.id}
                size="small"
                tier="tertiary"
                href={`#${section.id}`}
                label={section.title}
              />
            ))}
          </Cluster>
        </nav>

        <Layout gap="var(--polly-space-xl)">
          {GALLERY_SECTIONS.map((section) => (
            <Section key={section.id} section={section} />
          ))}
        </Layout>
      </Layout>

      {/* Mounted once so the overlay specimens have a portal target. */}
      <OverlayRoot />
      <Toast.Viewport />
      <ConfirmDialog.Host />
    </Surface>
  );
}
