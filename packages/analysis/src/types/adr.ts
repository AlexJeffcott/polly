// Architecture Decision Record types

/**
 * Architecture Decision Record
 * Based on Michael Nygard's ADR format
 */
export type ADR = {
  /** ADR number/ID */
  id: string

  /** Decision title */
  title: string

  /** Status: proposed, accepted, deprecated, superseded */
  status: ADRStatus

  /** Date of decision */
  date: string

  /** Context - what is the issue motivating this decision */
  context: string

  /** Decision - what is the change we're proposing */
  decision: string

  /** Consequences - what becomes easier or more difficult */
  consequences: string

  /** Optional: Alternatives considered */
  alternatives?: string[]

  /** Optional: Links to superseding/superseded ADRs */
  links?: ADRLink[]

  /** Source file path */
  source: string
}

export type ADRStatus = "proposed" | "accepted" | "deprecated" | "superseded"

export type ADRLink = {
  type: "supersedes" | "superseded-by" | "related-to"
  adrId: string
  title?: string
}

/**
 * Collection of ADRs
 */
export type ADRCollection = {
  adrs: ADR[]
  directory: string
}
