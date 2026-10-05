import Mathlib
import TMENudos.SpanCensos

/-!
# Camino (B), fase B0: palabras de Gauss de la forma de Conway `C(a₁, …, a_k)`

Etiqueta: **(B)**. NO se importa desde `TMENudos.lean`. Sin axiomas propios.

## Construccion (4-plat, la misma que la sonda `30_conway_b0.py`)

Cuatro hebras en las posiciones `0..3`. Los cruces se numeran `0..n-1` de abajo arriba; el bloque
`j` (con `a_j` cruces) cruza las hebras `(1,2)` si `j` es par y `(0,1)` si `j` es impar. Cada cruce
`c` tiene cuatro puertos `4c+0` (abajo-izq), `4c+1` (abajo-der), `4c+2` (arriba-izq), `4c+3`
(arriba-der); sus hebras son `BL-TR` y `BR-TL`. En los bloques pares pasa por encima la hebra
`BL-TR`; en los impares, la `BR-TL` (eso hace el diagrama alternante; se COMPRUEBA, no se supone).
Casquetes: abajo `(0,1),(2,3)`; arriba `(0,1),(2,3)` si `k` es impar y `(1,2),(0,3)` si `k` es
par. La palabra de Gauss es el recorrido de la curva desde el puerto 0; el signo de cada cruce
sale de la geometria (positivo si `cruz(dir_sup, dir_inf) > 0`).

## Que queda DEMOSTRADO (por `decide +kernel`, casos concretos)

* `frac` y los valores `p/q` de los casos nombrados.
* Para `C(3), C(2,2), C(5), C(3,2), C(4,2), C(3,1,2), C(2,1,1,2), C(7), C(3,1,3), C(3,2,2),
  C(5,2), C(4,3)`: `Word.wf`, numero de cruces `= suma a_i`, alternancia y `checkW = true`
  (verificador de `SpanCensos`; por `span_of_check` su span es `4n`, y `minimal_of_check` da
  minimalidad de cruces).
* Para 3_1, 4_1, 5_1, 5_2, 6_1, 6_2, 6_3: la palabra de Conway coincide con la de `Etapa1_GaussWord`
  / `SpanCensos` salvo renombrado de etiquetas, rotacion del punto de partida y, segun el caso,
  reversion del recorrido y/o imagen especular (`IsoW`/`variant`, comprobacion booleana).
* Enlaces `C(2), C(4), C(3,1)` (p par): `wf_enlace_*`, no dan una sola curva.

## Que NO esta demostrado

* Que `conwayWord a` sea bien formada, alternante, planar o de una sola curva para TODA lista `a`
  (solo por casos; la sonda 30 lo comprueba por calculo hasta n = 7, censo incluido).
* Que `frac` determine el nudo (Schubert), ni que `p` impar equivalga a una sola curva.
* Que `IsoW` implique igualdad de invariantes: es una comprobacion booleana de listas; NO se probo
  que renombrar, rotar, invertir o `swap` conserve el corchete a nivel de `Word`.
-/

namespace TMENudos.Conway

open TMENudos.Gauss TMENudos.Puente TMENudos.Invariancia TMENudos.SpanLaurent TMENudos.Nudos

/-! ### Fraccion continua -/

/-- `frac [a₁, …, a_k] = a₁ + 1/(a₂ + 1/(… + 1/a_k))`. -/
def frac : List ℕ → ℚ
  | [] => 0
  | [a] => a
  | a :: t => a + 1 / frac t

/-- Numerador `p` (determinante) de la fraccion. -/
def pOf (a : List ℕ) : ℕ := (frac a).num.natAbs

/-- Denominador `q`. -/
def qOf (a : List ℕ) : ℕ := (frac a).den

/-! ### Construccion de la palabra -/

/-- Por cada cruce: (posicion izquierda de sus hebras, si la hebra BL-TR va por encima). -/
def blocks (a : List ℕ) : List (ℕ × Bool) :=
  (a.zipIdx).flatMap fun (aj, j) => List.replicate aj (if j % 2 == 0 then 1 else 0, j % 2 == 0)

/-- Puertos que tocan la posicion `pos`, de abajo arriba. -/
def seqAt (cs : List (ℕ × Bool)) (pos : ℕ) : List ℕ :=
  (cs.zipIdx).flatMap fun ((l, _), c) =>
    if l == pos then [4 * c, 4 * c + 2] else if l + 1 == pos then [4 * c + 1, 4 * c + 3] else []

/-- Arcos entre cruces consecutivos de una misma posicion. -/
def midLinks (s : List ℕ) : List (ℕ × ℕ) :=
  (List.range (s.length / 2 - 1)).map fun j => (s.getD (2 * j + 1) 0, s.getD (2 * j + 2) 0)

/-- Casquete del lado `top` en la posicion `pos` (con `k` bloques). -/
def capOf (k : ℕ) (top : Bool) (pos : ℕ) : ℕ :=
  if top && k % 2 == 0 then 3 - pos else pos ^^^ 1

/-- Puerto extremo (primero abajo, ultimo arriba) de la posicion `pos`. -/
def endPort (cs : List (ℕ × Bool)) (top : Bool) (pos : ℕ) : ℕ :=
  if top then (seqAt cs pos).getLastD 0 else (seqAt cs pos).headD 0

/-- Sigue el casquete cruzando las hebras desnudas hasta llegar a un puerto. -/
def resolve (cs : List (ℕ × Bool)) (k : ℕ) : ℕ → Bool → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, top, pos =>
    let q := capOf k top pos
    if (seqAt cs q).isEmpty then resolve cs k fuel (!top) q else endPort cs top q

/-- Todos los arcos (pares de puertos unidos por un trozo de curva entre cruces). -/
def links (cs : List (ℕ × Bool)) (k : ℕ) : List (ℕ × ℕ) :=
  ((List.range 4).flatMap fun pos => midLinks (seqAt cs pos)) ++
  ((List.range 4).flatMap fun pos =>
    if (seqAt cs pos).isEmpty then []
    else [(endPort cs false pos, resolve cs k 4 false pos),
          (endPort cs true pos, resolve cs k 4 true pos)])

/-- El puerto al otro extremo del arco que sale de `p`. -/
def partnerOf (L : List (ℕ × ℕ)) (p : ℕ) : ℕ :=
  match L.find? (fun e => e.1 == p) with
  | some e => e.2
  | none => ((L.find? (fun e => e.2 == p)).map (·.1)).getD 0

/-- Recorrido de la curva: puertos de entrada sucesivos. -/
def walkAux (L : List (ℕ × ℕ)) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, p => p :: walkAux L f (partnerOf L ((3 - p % 4) + 4 * (p / 4)))

/-- Direccion con la que se entra por el puerto `p`. -/
def dirOf (p : ℕ) : ℤ × ℤ :=
  match p % 4 with
  | 0 => (1, 1)
  | 3 => (-1, -1)
  | 1 => (-1, 1)
  | _ => (1, -1)

/-- Puertos de entrada del recorrido (`2n` pasos desde el puerto 0). -/
def walk (a : List ℕ) : List ℕ :=
  let cs := blocks a
  walkAux (links cs a.length) (2 * cs.length) 0

/-- ¿El paso que entra por `p` va por encima? -/
def isOver (cs : List (ℕ × Bool)) (p : ℕ) : Bool :=
  ((cs.getD (p / 4) (0, false)).2 == decide (p % 4 = 0 ∨ p % 4 = 3))

/-- Palabra de Gauss con signos de la forma de Conway `C(a₁, …, a_k)` (con `aᵢ ≥ 1`).
Solo es una palabra legitima si la curva es unica (`p` impar); si no, `wf` falla. -/
def conwayWord (a : List ℕ) : Word :=
  let cs := blocks a
  let ps := walk a
  ps.map fun p =>
    let c := p / 4
    let po := (ps.find? fun q => q / 4 == c && isOver cs q).getD 0
    let pu := (ps.find? fun q => q / 4 == c && !isOver cs q).getD 0
    let d1 := dirOf po
    let d2 := dirOf pu
    ⟨c + 1, isOver cs p, decide (0 < d1.1 * d2.2 - d1.2 * d2.1)⟩

/-- Numero de cruces de la palabra. -/
def ncross (w : Word) : ℕ := (Word.crossings w).length

/-- Alternancia: los pasos superior/inferior se suceden (ciclicamente). -/
def alternates (w : Word) : Bool :=
  let d : Letter := ⟨0, false, false⟩
  (List.range w.length).all fun i => (w.getD i d).over != (w.getD ((i + 1) % w.length) d).over

/-! ### Isomorfia booleana de palabras (renombrado de etiquetas + rotacion) -/

/-- Relabela por orden de primera aparicion. -/
def canon (w : Word) : Word :=
  let labs := (w.map (·.label)).eraseDups
  w.map fun l => { l with label := labs.idxOf l.label }

/-- Igualdad salvo etiquetas y rotacion del punto de partida. -/
def IsoW (w v : Word) : Bool :=
  (List.range w.length).any fun k => canon (w.rotate k) == canon v

/-- Misma palabra recorrida en sentido contrario. -/
def rev (w : Word) : Word := w.reverse

/-- Variante `k` de `w`: 0 = tal cual, 1 = recorrido inverso, 2 = imagen especular (`swap`),
3 = ambas. -/
def variant (k : ℕ) (w : Word) : Word :=
  match k with
  | 0 => w
  | 1 => rev w
  | 2 => Word.swap w
  | _ => Word.swap (rev w)

/-- Isomorfia booleana salvo reversion y/o imagen especular: devuelve la lista de variantes
`k` para las que `variant k w` es isomorfa (`IsoW`) a `v`. -/
def isoVariants (w v : Word) : List ℕ :=
  (List.range 4).filter fun k => IsoW (variant k w) v

/-! ### Comprobaciones (evaluacion) -/

/-! ### Teoremas por casos -/

theorem frac_32 : frac [3, 2] = 7 / 2 := by decide +kernel
theorem frac_22 : frac [2, 2] = 5 / 2 := by decide +kernel
theorem frac_312 : frac [3, 1, 2] = 11 / 3 := by decide +kernel
theorem pq_32 : (pOf [3, 2], qOf [3, 2]) = (7, 2) := by decide +kernel
theorem pq_313 : (pOf [3, 1, 3], qOf [3, 1, 3]) = (15, 4) := by decide +kernel

/-- Verificacion completa de un caso: bien formada, `n` cruces y `checkW`. -/
def okCase (a : List ℕ) : Bool :=
  Word.wf (conwayWord a) && decide (ncross (conwayWord a) = a.sum) &&
    decide ((conwayWord a).length = 2 * a.sum) && alternates (conwayWord a) &&
    checkW (conwayWord a)

theorem ok_3 : okCase [3] = true := by decide +kernel
theorem ok_22 : okCase [2, 2] = true := by decide +kernel
theorem ok_5 : okCase [5] = true := by decide +kernel
theorem ok_32 : okCase [3, 2] = true := by decide +kernel
theorem ok_42 : okCase [4, 2] = true := by decide +kernel
theorem ok_312 : okCase [3, 1, 2] = true := by decide +kernel
theorem ok_2112 : okCase [2, 1, 1, 2] = true := by decide +kernel
theorem ok_7 : okCase [7] = true := by decide +kernel
theorem ok_313 : okCase [3, 1, 3] = true := by decide +kernel
theorem ok_322 : okCase [3, 2, 2] = true := by decide +kernel
theorem ok_52 : okCase [5, 2] = true := by decide +kernel
theorem ok_43 : okCase [4, 3] = true := by decide +kernel

/-- Los casos con `p` par son enlaces: la palabra de un solo recorrido NO es bien formada. -/
theorem wf_enlace_2 : Word.wf (conwayWord [2]) = false := by decide +kernel
theorem wf_enlace_4 : Word.wf (conwayWord [4]) = false := by decide +kernel
theorem wf_enlace_31 : Word.wf (conwayWord [3, 1]) = false := by decide +kernel

/-- Comparacion con las palabras ya existentes (salvo etiquetas/rotacion y variante). -/
theorem iso_31 : IsoW (conwayWord [3]) trefoil = true := by decide +kernel
theorem iso_41 : IsoW (variant 1 (conwayWord [2, 2])) knot41 = true := by decide +kernel
theorem iso_51 : IsoW (variant 2 (conwayWord [5])) knot51 = true := by decide +kernel
theorem iso_52 : IsoW (conwayWord [3, 2]) knot52 = true := by decide +kernel
theorem iso_61 : IsoW (variant 1 (conwayWord [4, 2])) knot61 = true := by decide +kernel
theorem iso_62 : IsoW (variant 3 (conwayWord [3, 1, 2])) knot62 = true := by decide +kernel
theorem iso_63 : IsoW (variant 1 (conwayWord [2, 1, 1, 2])) knot63 = true := by decide +kernel

/-- Cota de cruces transferida: `minimal_of_check` aplicado a `C(3,2)` (5_2). -/
theorem minimal_conway_32 (d' : Diag)
    (h : GRel (Diag.mk _ (ofWord (conwayWord [3, 2]) (by decide +kernel))) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    5 ≤ Fintype.card d'.D.Cross := by
  have hw : Word.wf (conwayWord [3, 2]) = true := by decide +kernel
  have := minimal_of_check (conwayWord [3, 2]) hw (by decide +kernel) d' h hf hc
  have hn : (Word.crossings (conwayWord [3, 2])).length = 5 := by decide +kernel
  omega

end TMENudos.Conway

#print axioms TMENudos.Conway.ok_7
#print axioms TMENudos.Conway.iso_62
#print axioms TMENudos.Conway.wf_enlace_2
#print axioms TMENudos.Conway.minimal_conway_32
