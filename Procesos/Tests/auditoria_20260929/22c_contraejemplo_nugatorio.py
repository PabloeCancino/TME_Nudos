"""SONDA 22c: contraejemplo a 'sin R1/R2 => sin cuerdas aisladas' en alternantes. Dos treboles unidos por una cuerda aislada (n=7):
cuerda c=(0,7) con un trebol en el arco 1..6 y otro en el arco 8..13. La cuerda c no es R1 (sus extremos no son adyacentes: hay cruces a ambos lados)
pero SI es aislada (nugatoria): ningun cruce la entrelaza."""
import itertools, importlib.util, sys
sys.argv = [sys.argv[0]]
def load(name, f):
    sp = importlib.util.spec_from_file_location(name, f); m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m
s22 = load("s22", "22_span_bracket.py"); s20 = load("s20", "20_transiciones_fieles.py"); s18 = s22.s18
N = 14
base = [(0, 7), (2, 5), (4, 1), (6, 3), (8, 11), (10, 13), (12, 9)]
found = 0
for signs in itertools.product([False, True], repeat=7):
    cfg = tuple(sorted((o, u, s) for (o, u), s in zip(base, signs)))
    if not s18.planar(N, cfg):
        continue
    iso = s22.isolated_chords(cfg, N)
    r1 = s20.r1_cands(cfg); r2 = s20.r2_cands(cfg)
    found += 1
    if found <= 3:
        print("planar, alternante, signos", signs, "| cuerdas aisladas:", iso, "| candidatos R1:", len(r1), "| R2:", len(r2))
print("configuraciones planares de esta forma:", found)
