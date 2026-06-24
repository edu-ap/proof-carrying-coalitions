# PCC interactive demo

A client-side demonstration of Proof-Carrying Coalitions: build an AI-agent
coalition and watch `Cl(A) ∩ F = ∅` decide admission live, on a capability
hypergraph, with each kernel-checked preset tied to its Lean theorem.

## Live

- **https://pcc.aguilar-pelaez.co.uk** (Cloudflare Pages, deployed 2026-06-23)
- https://proof-carrying-coalitions.pages.dev (default)

## See it locally

Open `index.html` in a browser:

```bash
# from the repo root
open projects/dev/aria/demo/index.html        # macOS
xdg-open projects/dev/aria/demo/index.html     # Linux
# or just double-click the file
```

No build step, no server. (Cytoscape loads from a CDN; engine.js is a plain script.)

## Faithfulness to Lean (the honesty mechanism)

`engine.js` mirrors `lean/Spec/Model.lean`. It is **not** the proof — it makes the
page interactive. `selftest.js` asserts the engine reproduces the kernel-checked
Lean verdicts for every preset, so engine-vs-Lean drift is caught:

```bash
node projects/dev/aria/demo/selftest.js
```

In the page, presets are badged **kernel-checked ✓** with their Lean theorem name;
any other coalition you build is labelled "computed in-browser, run verify.sh to
kernel-check". The page header shows a live "engine matches Lean ✓" badge.

## Deploy (gated on Eduardo — domain TBD)

Static SPA, deploys to Cloudflare Pages with no backend:

```bash
export CLOUDFLARE_API_TOKEN=$AGUILARPELAEZ_CLOUDFLARE_API_TOKEN_FULL
npx wrangler pages deploy projects/dev/aria/demo --project-name=proof-carrying-coalitions --branch=main
```

Then point the chosen domain at the Pages project.
