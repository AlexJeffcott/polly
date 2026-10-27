// Config keys that name message types, checked against the types the analysis
// found. A name that matches no type filters, bounds or orders nothing, and the
// run says nothing about it: examples/full-featured listed `SETTINGS_GET` under
// `messages.include` for a handler registered as `GET_SETTINGS`, so that
// handler was out of the model and no output said so.

export type UnknownMessageName = {
  /** Config path of the name, e.g. `messages.include` or `subsystems.auth.handlers`. */
  where: string;
  name: string;
};

type MessageNameConfig = {
  messages?: {
    include?: string[];
    exclude?: string[];
    symmetry?: string[][];
    perMessageBounds?: Record<string, number>;
  };
  subsystems?: Record<
    string,
    { handlers?: string[]; bounds?: { perMessageBounds?: Record<string, number> } }
  >;
  tier2?: {
    temporalConstraints?: Array<{ before: string; after: string }>;
    boundedExploration?: { criticalPaths?: string[][] };
  };
};

function namedMessages(config: MessageNameConfig): UnknownMessageName[] {
  const named: UnknownMessageName[] = [];
  const add = (where: string, names: Iterable<string> | undefined) => {
    for (const name of names ?? []) named.push({ where, name });
  };

  const messages = config.messages;
  add("messages.include", messages?.include);
  add("messages.exclude", messages?.exclude);
  add("messages.symmetry", messages?.symmetry?.flat());
  add("messages.perMessageBounds", Object.keys(messages?.perMessageBounds ?? {}));

  for (const [subsystem, sub] of Object.entries(config.subsystems ?? {})) {
    add(`subsystems.${subsystem}.handlers`, sub.handlers);
    add(
      `subsystems.${subsystem}.bounds.perMessageBounds`,
      Object.keys(sub.bounds?.perMessageBounds ?? {})
    );
  }

  const tier2 = config.tier2;
  add(
    "tier2.temporalConstraints",
    tier2?.temporalConstraints?.flatMap((c) => [c.before, c.after])
  );
  add("tier2.boundedExploration.criticalPaths", tier2?.boundedExploration?.criticalPaths?.flat());
  return named;
}

/** Each config name that matches no message type, once per config path. */
export function unknownMessageNames(
  config: MessageNameConfig,
  messageTypes: readonly string[]
): UnknownMessageName[] {
  const known = new Set(messageTypes);
  const seen = new Set<string>();
  return namedMessages(config).filter(({ where, name }) => {
    const key = `${where}\0${name}`;
    if (known.has(name) || seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}
