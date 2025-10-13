// Configuration file generator with smart comments

import type { FieldAnalysis, CodebaseAnalysis, TypeInfo } from "../types"

export class ConfigGenerator {
  private lines: string[] = []
  private indent = 0

  generate(analysis: CodebaseAnalysis): string {
    this.lines = []
    this.indent = 0

    this.addHeader()
    this.addImports()
    this.addExport()
    this.addStateConfig(analysis.fields)
    this.addMessagesConfig()
    this.addBehaviorConfig()
    this.closeExport()

    return this.lines.join("\n")
  }

  private addHeader(): void {
    this.line("// ═══════════════════════════════════════════════════════════════")
    this.line("// Verification Configuration")
    this.line("// ═══════════════════════════════════════════════════════════════")
    this.line("//")
    this.line("// This file configures TLA+ verification for your extension.")
    this.line("// Some values are auto-configured, others need your input.")
    this.line("//")
    this.line("// Look for:")
    this.line("//   • /* CONFIGURE */ - Replace with your value")
    this.line("//   • /* REVIEW */ - Check the auto-generated value")
    this.line("//   • null - Must be replaced with a concrete value")
    this.line("//")
    this.line("// Run 'bun verify' to check for incomplete configuration.")
    this.line("// Run 'bun verify --setup' for interactive help.")
    this.line("//")
    this.line("")
  }

  private addImports(): void {
    this.line("import { defineVerification } from '@fairfox/web-ext/verify'")
    this.line("")
  }

  private addExport(): void {
    this.line("export default defineVerification({")
    this.indent++
  }

  private closeExport(): void {
    this.indent--
    this.line("})")
  }

  private addStateConfig(fields: FieldAnalysis[]): void {
    this.line("state: {")
    this.indent++

    for (let i = 0; i < fields.length; i++) {
      const field = fields[i]

      // Add blank line between fields
      if (i > 0) {
        this.line("")
      }

      this.addFieldConfig(field)
    }

    this.indent--
    this.line("},")
    this.line("")
  }

  private addFieldConfig(field: FieldAnalysis): void {
    // Generate comment block
    this.addFieldComment(field)

    // Generate configuration line
    const config = this.generateFieldConfig(field)
    this.line(`"${field.path}": ${config},`)
  }

  private addFieldComment(field: FieldAnalysis): void {
    const separator = "─".repeat(60)

    // Header
    this.line(`// ${separator}`)
    this.line(`// ${field.path}: ${this.formatTypeName(field.type)}`)
    this.line(`// ${separator}`)

    // High confidence: auto-configured
    if (field.confidence === "high") {
      this.line("// ✓ Auto-configured from code analysis")
      if (field.evidence.length > 0) {
        for (const evidence of field.evidence) {
          this.line(`//   ${evidence}`)
        }
      }
      this.line("//")
      return
    }

    // Medium confidence: needs review
    if (field.confidence === "medium") {
      this.line("// ⚠️  Please review this auto-generated value")
      if (field.evidence.length > 0) {
        for (const evidence of field.evidence) {
          this.line(`//   Found: ${evidence}`)
        }
      }
      this.line("//")
      this.line("// REVIEW: Adjust if needed")
      this.line("//")
      return
    }

    // Low confidence: manual configuration required
    this.line("// ⚠️  Manual configuration required")
    this.line("//")

    // Type-specific guidance
    this.addTypeGuidance(field)

    // Suggestions
    if (field.suggestions.length > 0) {
      this.line("//")
      for (const suggestion of field.suggestions) {
        this.line(`// ${suggestion}`)
      }
    }

    this.line("//")
    this.line("// CONFIGURE: Fill in the value below")
    this.line("//")
  }

  private addTypeGuidance(field: FieldAnalysis): void {
    switch (field.type.kind) {
      case "array":
        this.line("// This array has no bounds in your code. Choose a maximum")
        this.line("// length for verification. Tradeoffs:")
        this.line("//   • Small (3-5): Fast, catches basic bugs")
        this.line("//   • Medium (10-15): Balanced, catches most bugs")
        this.line("//   • Large (20+): Thorough, much slower")
        break

      case "string":
        this.line("// Strings need concrete values for precise verification.")
        this.line("// Provide 2-3 representative values from your app.")
        if (field.type.nullable) {
          this.line("//")
          this.line("// Note: This field is nullable (can be null)")
        }
        this.line("//")
        this.line("// Examples:")
        this.line('//   ["user_abc123", "user_xyz789", "guest_000"]')
        this.line('//   ["active", "inactive", "pending"]')
        this.line("//")
        this.line("// Alternative: Use abstract verification (less precise, faster)")
        this.line("//   { abstract: true }")
        break

      case "number":
        this.line("// Numbers need a range. Choose min and max values based on")
        this.line("// realistic bounds in your application.")
        if (field.type.nullable) {
          this.line("//")
          this.line("// Note: This field is nullable (can be null)")
        }
        this.line("//")
        this.line("// Examples:")
        this.line("//   { min: 0, max: 100 }  // Counter")
        this.line("//   { min: 0, max: 999999 }  // Timestamp")
        break

      case "map":
      case "set":
        this.line(`// ${field.type.kind} needs a maximum size. How many entries`)
        this.line("// do you need to model to catch bugs?")
        this.line("//")
        this.line("// Recommended: 3-5 for most cases")
        break

      case "object":
        this.line("// Complex nested object. Configure each field separately.")
        break

      default:
        this.line(`// ${field.type.kind} type requires configuration.`)
    }
  }

  private generateFieldConfig(field: FieldAnalysis): string {
    switch (field.type.kind) {
      case "boolean":
        return "{ type: 'boolean' }"

      case "enum":
        if (field.type.enumValues) {
          const values = field.type.enumValues.map(v => `"${v}"`).join(", ")
          return `{ type: "enum", values: [${values}] }`
        }
        return "{ type: 'enum', values: /* CONFIGURE */ null }"

      case "array":
        if (field.bounds?.maxLength !== undefined && field.bounds.maxLength !== null) {
          if (field.confidence === "medium") {
            return `{ maxLength: /* REVIEW */ ${field.bounds.maxLength} }`
          }
          return `{ maxLength: ${field.bounds.maxLength} }`
        }
        return "{ maxLength: /* CONFIGURE */ null }"

      case "number":
        if (field.bounds?.min !== undefined && field.bounds?.max !== undefined) {
          const minStr = field.bounds.min !== null ? field.bounds.min : "/* CONFIGURE */"
          const maxStr = field.bounds.max !== null ? field.bounds.max : "/* CONFIGURE */"

          if (field.confidence === "high") {
            return `{ min: ${minStr}, max: ${maxStr} }`
          }
          return `{ min: /* REVIEW */ ${minStr}, max: /* REVIEW */ ${maxStr} }`
        }
        return "{ min: /* CONFIGURE */ null, max: /* CONFIGURE */ null }"

      case "string":
        return "{ values: /* CONFIGURE */ null }"

      case "map":
      case "set":
        return "{ maxSize: /* CONFIGURE */ null }"

      default:
        return "{ /* CONFIGURE */ }"
    }
  }

  private addMessagesConfig(): void {
    this.line("messages: {")
    this.indent++

    this.line("// Maximum messages in flight simultaneously across all contexts.")
    this.line("// Higher = more realistic concurrency, but exponentially slower.")
    this.line("//")
    this.line("// Recommended values:")
    this.line("//   • 2-3: Fast verification (< 10 seconds)")
    this.line("//   • 4-6: Balanced (10-60 seconds)")
    this.line("//   • 8+: Thorough but slow (minutes)")
    this.line("//")
    this.line("// WARNING: State space grows exponentially! Start small.")
    this.line("maxInFlight: 3,")
    this.line("")
    this.line("// Maximum tab IDs to model (content scripts are per-tab).")
    this.line("//")
    this.line("// Recommended:")
    this.line("//   • 0-1: Most extensions (single tab or tab-agnostic)")
    this.line("//   • 2-3: Multi-tab coordination")
    this.line("//")
    this.line("// Start with 0 or 1 for faster verification.")
    this.line("maxTabs: 1,")

    this.indent--
    this.line("},")
    this.line("")
  }

  private addBehaviorConfig(): void {
    this.line("// Verification behavior")
    this.line("// ─────────────────────")
    this.line("//")
    this.line("// onBuild: What to do during development builds")
    this.line("//   • 'warn' - Show warnings but don't fail (recommended)")
    this.line("//   • 'error' - Fail the build on violations")
    this.line("//   • 'off' - Skip verification")
    this.line("//")
    this.line("onBuild: 'warn',")
    this.line("")
    this.line("// onRelease: What to do during production builds")
    this.line("//   • 'error' - Fail the build on violations (recommended)")
    this.line("//   • 'warn' - Show warnings but don't fail")
    this.line("//   • 'off' - Skip verification")
    this.line("//")
    this.line("onRelease: 'error',")
  }

  private formatTypeName(type: TypeInfo): string {
    let typeName: string

    switch (type.kind) {
      case "boolean":
        typeName = "boolean"
        break
      case "string":
        typeName = "string"
        break
      case "number":
        typeName = "number"
        break
      case "enum":
        if (type.enumValues) {
          typeName = type.enumValues.map(v => `"${v}"`).join(" | ")
        } else {
          typeName = "enum"
        }
        break
      case "array":
        if (type.elementType) {
          typeName = `${this.formatTypeName(type.elementType)}[]`
        } else {
          typeName = "array"
        }
        break
      case "object":
        typeName = "object"
        break
      case "map":
        typeName = "Map"
        break
      case "set":
        typeName = "Set"
        break
      case "null":
        typeName = "null"
        break
      default:
        typeName = "unknown"
    }

    // Append " | null" if type is nullable
    if (type.nullable && type.kind !== "null") {
      typeName += " | null"
    }

    return typeName
  }

  private line(content: string): void {
    if (content === "") {
      this.lines.push("")
    } else {
      const indentation = "  ".repeat(this.indent)
      this.lines.push(indentation + content)
    }
  }
}

export function generateConfig(analysis: CodebaseAnalysis): string {
  const generator = new ConfigGenerator()
  return generator.generate(analysis)
}
