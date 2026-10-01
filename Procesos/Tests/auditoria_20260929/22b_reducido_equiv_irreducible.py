"""SONDA 22b: ¿'reducido' (sin cuerdas aisladas) equivale a 'sin candidatos R1' en TODO diagrama, y en los alternantes a 'sin R1/R2'?
Tesis: (1) hay una cuerda aislada  <=>  hay un candidato R1   (la cuerda mas interna de un arco libre es adyacente);
       (2) un diagrama ALTERNANTE no tiene candidatos R2 (R2 exige pasos superiores consecutivos).
Comprobacion exhaustiva sobre todos los diagramas sin indices con n <= 4."""
import importlib.util, itertools
spec = importlib.util.spec_from_file_location("s22", "22_span_bracket.py")
s22 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s22)
s20 = importlib.util.module_from_spec(importlib.util.spec_from_file_location("s20", "20_transiciones_fieles.py")); 
import sys
sys.argv=[sys.argv[0]]
spec20 = importlib.util.spec_from_file_location("s20", "20_transiciones_fieles.py"); s20 = importlib.util.module_from_spec(spec20); spec20.loader.exec_module(s20)

def alternating(cfg, N):
    ov = {o % 2 for o, u, s in cfg}
    return len(ov) == 1

tot = 0
bad1 = bad2 = 0
for n in (1, 2, 3, 4):
    N = 2 * n
    uniq = {}
    for K in s20.configs(n):
        uniq.setdefault(tuple(sorted(K)), K)
    for key, K in uniq.items():
        tot += 1
        iso = s22.isolated_chords(K, N)
        r1 = len(s20.r1_cands(K))
        if (iso > 0) != (r1 > 0):
            bad1 += 1
        if alternating(K, N) and s20.r2_cands(K):
            bad2 += 1
print(f"diagramas probados: {tot}; (1) discrepancias aislada<=>R1cand: {bad1}; (2) alternantes con candidato R2: {bad2}")
