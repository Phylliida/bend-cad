// Prints, for each record of the request the page would send, the GUI
// constraint it came from ("#id kind entities"), as a JSON list indexed by
// request position (the positions the solver's red list and owners use).
// Usage: bun tools/diag/owners.mjs sketch.json > owners.json
import * as PL from "../../gui/pipeline.js";
import { readFileSync } from "fs";
const sk = JSON.parse(readFileSync(process.argv[2], "utf8"));
const prep = PL.prepare(sk, { relax: true, order: true, dyadic: true }, []);
const byId = new Map(sk.cons.map(c => [c.id, c]));
const name = id => { const e = sk.ents.find(e => e.id === id); return e ? e.kind + id : "?" + id; };
console.log(JSON.stringify(prep.map.owner.map(id => { const c = byId.get(id); return `#${id} ${c.kind} ${c.ents.map(name).join(" ")}`; })));
