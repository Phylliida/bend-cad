// Replays the page's prepare step (relax, order, dyadic rounding) on a
// sketch exported from the GUI, writing the request the page would POST.
// Usage: bun tools/diag/replay.mjs sketch.json req.json [--repeats]
// --repeats keeps repeated constraints, which the page leaves out.
import * as PL from "../../gui/pipeline.js";
import { readFileSync, writeFileSync } from "fs";
const [inp, out, flag] = process.argv.slice(2);
const sk = JSON.parse(readFileSync(inp, "utf8"));
const prep = PL.prepare(sk, { relax: true, order: true, dyadic: true, repeats: flag === "--repeats" }, []);
writeFileSync(out, JSON.stringify(prep.req));
console.log(JSON.stringify({ nvars: prep.req.g0.length, ncons: prep.req.cons.length, nents: prep.req.ents.length, residual: prep.residual, order: prep.order }));
