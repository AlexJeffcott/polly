// ADR (Architecture Decision Record) extractor
// Parses ADRs from markdown files following Michael Nygard's format

import * as fs from "node:fs";
import * as path from "node:path";
import type { ADR, ADRCollection, ADRLink, ADRStatus } from "../types/adr";

export class ADRExtractor {
  private projectRoot: string;

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
  }

  /**
   * Extract ADRs from docs/adr directory
   */
  extract(): ADRCollection {
    const adrDir = this.findADRDirectory();

    if (!adrDir || !fs.existsSync(adrDir)) {
      return {
        adrs: [],
        directory: adrDir || path.join(this.projectRoot, "docs", "adr"),
      };
    }

    const files = fs
      .readdirSync(adrDir)
      .filter((file) => file.endsWith(".md"))
      .map((file) => path.join(adrDir, file));

    const adrs: ADR[] = [];

    for (const file of files) {
      try {
        const adr = this.parseADR(file);
        if (adr) {
          adrs.push(adr);
        }
      } catch (_error) {}
    }

    // Sort by ID
    adrs.sort((a, b) => a.id.localeCompare(b.id));

    return {
      adrs,
      directory: adrDir,
    };
  }

  /**
   * Find ADR directory
   */
  private findADRDirectory(): string | null {
    const candidates = [
      path.join(this.projectRoot, "docs", "adr"),
      path.join(this.projectRoot, "docs", "architecture", "decisions"),
      path.join(this.projectRoot, "adr"),
      path.join(this.projectRoot, "architecture", "decisions"),
    ];

    for (const candidate of candidates) {
      if (fs.existsSync(candidate)) {
        return candidate;
      }
    }

    return null;
  }

  /**
   * Parse ADR from markdown file
   */
  private parseADR(filePath: string): ADR | null {
    const content = fs.readFileSync(filePath, "utf-8");
    const fileName = path.basename(filePath, ".md");

    // Extract ID from filename (e.g., "0001-use-preact.md" → "0001")
    const idMatch = fileName.match(/^(\d+)/);
    const id = idMatch?.[1] ?? fileName;

    // Extract title from first heading
    const titleMatch = content.match(/^#\s+(.+)$/m);
    const title = titleMatch?.[1]?.trim() ?? fileName;

    // Extract status
    const status = this.extractStatus(content);

    // Extract date
    const date = this.extractDate(content);

    // Extract sections
    const context = this.extractSection(content, "Context");
    const decision = this.extractSection(content, "Decision");
    const consequences = this.extractSection(content, "Consequences");

    // Extract alternatives (if present)
    const alternativesSection = this.extractSection(content, "Alternatives");
    const alternatives = alternativesSection
      ? alternativesSection
          .split("\n")
          .filter((line) => line.trim().startsWith("-"))
          .map((line) => line.replace(/^-\s*/, "").trim())
      : undefined;

    // Extract links
    const links = this.extractLinks(content);

    if (!context || !decision || !consequences) {
      // Not a valid ADR format
      return null;
    }

    return {
      id,
      title,
      status,
      date,
      context,
      decision,
      consequences,
      ...(alternatives && alternatives.length > 0 ? { alternatives } : {}),
      ...(links.length > 0 ? { links } : {}),
      source: filePath,
    };
  }

  /**
   * Extract status from content
   */
  private extractStatus(content: string): ADRStatus {
    const statusMatch = content.match(/Status:\s*(\w+)/i);
    if (!statusMatch) return "accepted";

    const status = statusMatch[1]?.toLowerCase();
    if (status && ["proposed", "accepted", "deprecated", "superseded"].includes(status)) {
      return status as ADRStatus;
    }

    return "accepted";
  }

  /**
   * Extract date from content
   */
  private extractDate(content: string): string {
    // Try to find date in various formats
    const dateMatch =
      content.match(/Date:\s*(\d{4}-\d{2}-\d{2})/i) || content.match(/(\d{4}-\d{2}-\d{2})/i);

    return dateMatch?.[1] ?? new Date().toISOString().split("T")[0]!;
  }

  /**
   * Extract section content
   */
  private extractSection(content: string, sectionName: string): string {
    // Match section heading and capture content until next heading or end
    const regex = new RegExp(`##\\s+${sectionName}\\s*\\n([\\s\\S]*?)(?=\\n##|$)`, "i");
    const match = content.match(regex);

    return match?.[1]?.trim() ?? "";
  }

  /**
   * Extract links to other ADRs
   */
  private extractLinks(content: string): ADRLink[] {
    const links: ADRLink[] = [];

    // Look for supersedes/superseded-by links
    const supersedesMatch = content.match(/Supersedes:\s*ADR-(\d+)/gi);
    if (supersedesMatch) {
      for (const match of supersedesMatch) {
        const idMatch = match.match(/ADR-(\d+)/);
        const id = idMatch?.[1];
        if (id) {
          links.push({
            type: "supersedes",
            adrId: id,
          });
        }
      }
    }

    const supersededByMatch = content.match(/Superseded by:\s*ADR-(\d+)/gi);
    if (supersededByMatch) {
      for (const match of supersededByMatch) {
        const idMatch = match.match(/ADR-(\d+)/);
        const id = idMatch?.[1];
        if (id) {
          links.push({
            type: "superseded-by",
            adrId: id,
          });
        }
      }
    }

    return links;
  }
}

/**
 * Extract ADRs from project
 */
export function extractADRs(projectRoot: string): ADRCollection {
  const extractor = new ADRExtractor(projectRoot);
  return extractor.extract();
}
