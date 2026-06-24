/*
  PCC demo engine — a faithful in-browser mirror of lean/Spec/Model.lean.

  Same model: agents hold capability sets; a coalition's joint capabilities are
  closed under CONJUNCTIVE hyperedges (a rule fires only when ALL prerequisites
  are present); the security property is Cl(A) cap F = empty.

  HONESTY: this engine is NOT the proof. It mirrors the Lean model so the page is
  interactive, and `selftest.js` asserts the kernel-checked presets get the same
  verdict here as in Lean (catching engine-vs-Lean drift). For a custom scenario
  the page shows "computed in-browser, run verify.sh to kernel-check". UMD so the
  same file runs in the browser (window.PCC) and under node (require) for the test.
*/
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory();
  else root.PCC = factory();
})(typeof self !== "undefined" ? self : this, function () {
  // --- set helpers over arrays of strings (mirror memC/subsetC/insertC/unionC) ---
  const mem = (c, l) => l.indexOf(c) !== -1;
  const subset = (a, b) => a.every((x) => mem(x, b));
  const insert = (c, l) => (mem(c, l) ? l : l.concat([c]));
  const union = (a, b) => a.reduce((acc, x) => insert(x, acc), b.slice());
  const inter = (a, b) => a.filter((x) => mem(x, b));
  const diff = (a, b) => a.filter((x) => !mem(x, b));

  // one saturation step: fire every rule whose prereqs are all present
  function stepOnce(rules, s) {
    return rules.reduce(
      (acc, r) => (subset(r.prereqs, acc) ? insert(r.output, acc) : acc),
      s.slice()
    );
  }

  // fixpoint closure (early-exit when the set stops growing; mirrors `saturate`)
  function closure(rules, seed) {
    let s = seed.slice();
    const fuel = rules.length + seed.length + 8;
    for (let i = 0; i < fuel; i++) {
      const s2 = stepOnce(rules, s);
      if (s2.length === s.length) return s2;
      s = s2;
    }
    return s;
  }

  const coalitionCaps = (agents) => agents.reduce((acc, a) => union(a, acc), []);

  // THE property: Cl(coalition) disjoint from F
  function coalitionSafe(rules, F, agents) {
    return inter(closure(rules, coalitionCaps(agents)), F).length === 0;
  }
  const admit = coalitionSafe;

  // capabilities gained through closure beyond the seed (for the animation)
  const gained = (rules, seed) => diff(closure(rules, seed), seed);
  // forbidden capabilities actually reached (the audit surface)
  const frontierForbidden = (rules, F, agents) =>
    inter(closure(rules, coalitionCaps(agents)), F);

  // --- the standard PCC instance (identical to lean/Spec/Model.lean) ---
  const CAPS = [
    "readDoc", "summarise", "redact", "classify",
    "forge", "exfil", "escalate", "signDeed", "wireFunds",
  ];
  const RULES = [
    { prereqs: ["forge", "exfil"], output: "signDeed" },
    { prereqs: ["signDeed", "escalate"], output: "wireFunds" },
  ];
  const FORBIDDEN = ["signDeed", "wireFunds"];
  const AGENTS = {
    A: ["readDoc", "forge"],
    B: ["summarise", "exfil"],
    C: ["readDoc", "summarise", "redact"],
    D: ["classify", "escalate"],
  };

  // Presets that ARE kernel-checked in lean/Spec/Theorems.lean. `expect` is the
  // Lean verdict; the selftest asserts the engine reproduces it.
  const PRESETS = [
    { id: "A_alone", label: "Agent A alone", agents: ["A"], expectSafe: true, theorem: "agentA_safe_alone" },
    { id: "B_alone", label: "Agent B alone", agents: ["B"], expectSafe: true, theorem: "agentB_safe_alone" },
    { id: "AB", label: "A + B (the Spera case)", agents: ["A", "B"], expectSafe: false, theorem: "coalition_AB_unsafe / non_compositional" },
    { id: "AC", label: "A + C (benign)", agents: ["A", "C"], expectSafe: true, theorem: "benign_coalition_safe" },
    { id: "ABD", label: "A + B + D (chain)", agents: ["A", "B", "D"], expectSafe: false, theorem: "chain_reaches_wireFunds" },
  ];

  return {
    mem, subset, insert, union, inter, diff,
    stepOnce, closure, coalitionCaps, coalitionSafe, admit, gained, frontierForbidden,
    CAPS, RULES, FORBIDDEN, AGENTS, PRESETS,
  };
});
