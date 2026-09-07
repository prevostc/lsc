# Provable DeFi Agent Setup v3

Token and Vault anti-exploit theorems are proved through to EVM bytecode (Token
S1 / call-free; Vault S2 / one external IERC20 binding):
`token_bytecode_no_unauthorized_extraction` / `_solvent` and
`vault_bytecode_no_unauthorized_extraction` / `_solvent`. AMM is spec-level only
(`amm_no_unauthorized_extraction`, `amm_solvent`). Details:
`docs/architecture/PROOF_CHAIN.md`.

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
```

## Classification

- `AGENTS.md` — always-on operating rules.
- `prompts/architecture-review-2026-09.md` — the one-shot architecture investigation to run now.
- `implement-and-prove` — reusable implementation/proof workflow.
- `simplify-and-modularize` — reusable post-milestone cleanup workflow.
- `docs/PROJECT_GOAL.md` — stable product intent.
- `docs/architecture/` — concise architecture contracts (language, security, proof chain, TCB).
