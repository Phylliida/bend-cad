# Turns a request (from replay.mjs) into gui/solve_cli's sketch.in, exactly
# as gui/serve.py does. Usage: python3 tools/diag/totext.py req.json > sketch.in
import json, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gui'))
import serve
print(serve.sketch_text(json.load(open(sys.argv[1]))), end='')
