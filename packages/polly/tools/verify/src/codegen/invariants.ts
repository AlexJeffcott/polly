// Render application invariants as TLA+ definitions and INVARIANT clauses.
//
// polly#168 removed the JSDoc `@invariant` extractor that used to live here. It
// was gated on a flag no caller set, so it had never run in production, and
// `capabilities` (polly#160) already covers the same need through a validated
// path. Every remaining producer synthesises its invariants and supplies its
// own name — see `addCapabilityInvariants` and `addTemporalConstraints` in
// codegen/tla.ts.

/**
 * One invariant to check at every reachable state.
 */
export type Invariant = {
  /** TLA+ identifier for the invariant. Supplied by the producer. */
  name: string;
  /** Human-readable comment rendered above the definition. May be multi-line. */
  description: string;
  /** TypeScript boolean expression, translated by `tsExpressionToTLA`. */
  expression: string;
  /** Source location. Omitted for synthesised invariants (e.g. polly#160
   *  capabilities) that have no originating source line. */
  location?: {
    file: string;
    line: number;
  };
};

/**
 * Render a description as TLA+ comment lines, one `\\*` marker per line
 * (polly#168). Returns an empty array for an absent or blank description.
 */
export function describe(description: string | undefined): string[] {
  if (!description?.trim()) return [];
  return description.split("\n").map((line) => `\\* ${line.trimEnd()}`);
}

/**
 * InvariantGenerator converts extracted invariants to TLA+ format
 */
export class InvariantGenerator {
  /**
   * Generate TLA+ invariant definitions.
   */
  generateTLAInvariants(
    invariants: Invariant[],
    tsExpressionToTLA: (expr: string) => string
  ): string[] {
    const tlaInvariants: string[] = [];

    for (const invariant of invariants) {
      tlaInvariants.push(this.generateSingleInvariant(invariant, tsExpressionToTLA));
    }

    return tlaInvariants;
  }

  /**
   * Generate single TLA+ invariant
   */
  private generateSingleInvariant(
    invariant: Invariant,
    tsExpressionToTLA: (expr: string) => string
  ): string {
    const lines: string[] = [];

    // Every line needs its own `\\*`. A description with an embedded newline
    // used to emit line 2 onward as bare prose inside the module body, which
    // SANY rejects (polly#168). Reachable in production through a capability's
    // `message` (tla.ts addCapabilityInvariants).
    for (const line of describe(invariant.description)) {
      lines.push(line);
    }

    // Translate expression to TLA+
    const tlaExpr = tsExpressionToTLA(invariant.expression);

    // Wrap in universal quantifier over all contexts
    lines.push(`${invariant.name} ==`);
    lines.push(`  \\A ctx \\in Contexts : ${tlaExpr}`);

    return lines.join("\n");
  }

  /**
   * Generate INVARIANT declarations for TLA+ config file
   */
  generateConfigInvariants(invariants: Invariant[]): string[] {
    return invariants.map((inv) => `INVARIANT ${inv.name}`);
  }
}
