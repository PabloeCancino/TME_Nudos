"""SONDA 27 (2026-10-02), etapa S5b: palabras de Gauss en formato Lean para SpanCensos.lean.

Reutiliza 22 (corchete, lazos, cuerdas aisladas) y 24 (adecuacion) para enumerar los alternantes
planares REDUCIDOS (sin cuerdas aisladas) y emite, en formato Lean:
  * una palabra `Word` (formato `⟨label, over, pos⟩`, posiciones consecutivas 0..2n-1) por cada
    nudo con nombre 3_1, 4_1, 5_1, 5_2, 6_1, 6_2, 6_3, identificado por su polinomio de Jones
    (modulo imagen especular y signo global);
  * `censoN` (N = 6, 7): la lista de TODOS los datos (p, sigma, mascara de signos) reducidos de
    longitud N (mismos datos que `buildL` de Reconstruccion.lean: over_i = 2i+p,
    under_i = 2 sigma(i) + 1 - p, signo_i = bit i de la mascara).
Ademas comprueba en Python: reducido planar => adecuado y sA + sB = n + 2, y el conteo (stderr).
Uso (desde esta carpeta): python 27_palabras_lean.py [nmax] > salida.lean   (nmax <= 7; omision 6)
"""
import itertools
import sys
import importlib.util

spec = importlib.util.spec_from_file_location("s24", "24_adecuacion.py")
s24 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s24)
s22 = s24.s22
s18 = s24.s18
s19 = s24.s19

# Jones conocidos (coeficientes de menor a mayor exponente), modulo reversion y signo global.
CONOCIDOS = {
    "31": [1, 0, 1, -1],
    "41": [1, -1, 1, -1, 1],
    "51": [1, 0, 1, -1, 1, -1],
    "52": [1, -1, 2, -1, 1, -1],
    "61": [1, -1, 1, -2, 2, -1, 1],
    "62": [1, -1, 2, -2, 2, -2, 1],
    "63": [-1, 2, -2, 3, -2, 2, -1],
}


def jones_seq(cfg, poly):
    w = sum(1 if s else -1 for _, _, s in cfg)
    sign = -1 if (w % 2) else 1
    pj = {}
    for e, c in poly.items():
        e2 = e - 3 * w
        assert e2 % 4 == 0
        pj[-e2 // 4] = c * sign
    lo, hi = min(pj), max(pj)
    return [pj.get(k, 0) for k in range(lo, hi + 1)]


def nombre(seq):
    for nm, k in CONOCIDOS.items():
        for cand in (k, k[::-1]):
            if seq == cand or seq == [-x for x in cand]:
                return nm
    return None


def cfg_to_word(cfg, N):
    """Palabra de Gauss: posicion q -> Letter. Etiquetas 1.. por orden de paso superior."""
    lab = {}
    for (o, u, s) in sorted(cfg):
        lab[(o, u)] = len(lab) + 1
    letters = [None] * N
    for (o, u, s) in cfg:
        letters[o] = (lab[(o, u)], True, s)
        letters[u] = (lab[(o, u)], False, s)
    return letters


def lean_letter(t):
    return "⟨%d, %s, %s⟩" % (t[0], str(t[1]).lower(), str(t[2]).lower())


def lean_word(name, letters):
    out = ["def %s : Word :=" % name]
    chunks = [", ".join(lean_letter(t) for t in letters[i:i + 4]) for i in range(0, len(letters), 4)]
    out.append("  [" + ",\n   ".join(chunks) + "]")
    return "\n".join(out)


def cfg_to_datum(cfg):
    cfg = sorted(cfg)
    p = cfg[0][0] % 2
    sigma = [(u - (1 - p)) // 2 for (_, u, _) in cfg]
    mask = sum((1 << i) for i, (_, _, s) in enumerate(cfg) if s)
    return p, sigma, mask


def run(n):
    N = 2 * n
    seen = set()
    reds = []
    bad = []
    for parity in (0, 1):
        overs = [p for p in range(N) if p % 2 == parity]
        unders = [p for p in range(N) if p % 2 != parity]
        for perm in itertools.permutations(unders):
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                if not s18.planar(N, cfg):
                    continue
                if s22.isolated_chords(cfg, N) != 0:
                    continue
                a_ok, b_ok = s24.adequate(cfg, N)
                sA = s24.circles_state(cfg, N, [True] * n)
                sB = s24.circles_state(cfg, N, [False] * n)
                if not (a_ok and b_ok and sA + sB == n + 2):
                    bad.append(cfg)
                reds.append(cfg)
    print("-- n=%d: reducidos planares alternantes %d, fallos de adecuacion/genero %d"
          % (n, len(reds), len(bad)), file=sys.stderr, flush=True)
    return reds


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    print("/- Generado por Procesos/Tests/auditoria_20260929/27_palabras_lean.py -/")
    nombrados = {}
    for n in range(3, nmax + 1):
        N = 2 * n
        reds = run(n)
        if n <= 6:
            for cfg in reds:
                poly, _, _ = s22.bracket_and_circles(cfg, N)
                nm = nombre(jones_seq(cfg, poly))
                if nm and nm not in nombrados:
                    nombrados[nm] = (n, cfg)
        if n >= 6:
            ds = [cfg_to_datum(c) for c in reds]
            ds.sort()
            items = ["(%d, [%s], %d)" % (p, ", ".join(map(str, s)), m) for p, s, m in ds]
            lines = ["  " + ", ".join(items[i:i + 3]) for i in range(0, len(items), 3)]
            print("\n/-- Censo de longitud %d generado por Python (%d datos). -/" % (n, len(ds)))
            print("def censo%d : List (ℕ × List ℕ × ℕ) := [" % n)
            print(",\n".join(lines))
            print("  ]")
    for nm, (n, cfg) in sorted(nombrados.items()):
        print()
        print("-- %s: %d cruces, cfg %s" % (nm, n, list(sorted(cfg))))
        print(lean_word("k" + nm, cfg_to_word(cfg, 2 * n)))
    print("-- nombrados encontrados:", sorted(nombrados), file=sys.stderr)


if __name__ == "__main__":
    main()
