# Provable DeFi Agent Setup v3

This layout distinguishes **persistent rules**, **one-shot prompts**, **reusable skills**, and **durable project knowledge**.

```text
AGENTS.md

.agents/
└── skills/
    ├── implement-and-prove/
    │   └── SKILL.md
    └── simplify-and-modularize/
        └── SKILL.md

docs/
├── PROJECT_GOAL.md
└── architecture/
    └── README.md

prompts/
└── architecture-review-2026-09.md
```

## Classification

- `AGENTS.md` — always-on operating rules.
- `prompts/architecture-review-2026-09.md` — the one-shot architecture investigation to run now.
- `implement-and-prove` — reusable implementation/proof workflow.
- `simplify-and-modularize` — reusable post-milestone cleanup workflow.
- `docs/PROJECT_GOAL.md` — stable product intent.
- `docs/architecture/` — concise architecture contracts produced by the review.

The architecture review should produce the initial language, security, proof-chain, module-map, and TCB documents rather than assuming those decisions in advance.
