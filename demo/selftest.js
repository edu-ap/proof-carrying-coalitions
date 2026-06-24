/*
  Demo engine self-test (node): assert the in-browser engine reproduces the
  kernel-checked Lean verdicts for every preset. Catches engine-vs-Lean drift,
  the one real c_sys risk of having a JS mirror of the Lean model.

  Run: node demo/selftest.js   (also runnable in the browser; see index.html)
*/
const PCC = require("./engine.js");

let fails = 0;
for (const p of PCC.PRESETS) {
  const agents = p.agents.map((k) => PCC.AGENTS[k]);
  const safe = PCC.coalitionSafe(PCC.RULES, PCC.FORBIDDEN, agents);
  const ok = safe === p.expectSafe;
  if (!ok) fails++;
  console.log(
    `${ok ? "OK  " : "FAIL"}  ${p.id.padEnd(8)} engine=${safe ? "safe" : "UNSAFE"} ` +
      `lean=${p.expectSafe ? "safe" : "UNSAFE"}  (${p.theorem})`
  );
}
// the chain must actually reach wireFunds (matches chain_reaches_wireFunds)
const abd = PCC.coalitionCaps([PCC.AGENTS.A, PCC.AGENTS.B, PCC.AGENTS.D]);
const reachesWire = PCC.mem("wireFunds", PCC.closure(PCC.RULES, abd));
if (!reachesWire) { fails++; console.log("FAIL  chain does not reach wireFunds"); }
else console.log("OK    chain reaches wireFunds (chain_reaches_wireFunds)");

if (fails) { console.error(`\n[selftest] FAIL: ${fails} mismatch(es) engine vs Lean`); process.exit(1); }
console.log("\n[selftest] PASS: engine matches all kernel-checked Lean verdicts");
