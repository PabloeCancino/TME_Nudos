import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Etapa 1 (spike de viabilidad): palabras de Gauss con signos y corchete de Kauffman

Este archivo NO forma parte de la biblioteca (no lo importa `TMENudos.lean`). Es el hito M1 del
mapa de ruta: valida la representación "palabra de Gauss con signos" y el cálculo del corchete
de Kauffman por suma sobre estados, antes de reescribir `Reidemeister.lean`.

## Representación
Una palabra es una lista cíclica de letras. Cada letra es un paso por un cruce: la etiqueta del
cruce, si es el paso por encima (`over`), y el signo del cruce (`pos = true` es positivo). Un
cruce aparece dos veces: una por encima y otra por debajo, con el mismo signo. La planaridad NO
se exige: el corchete se define e invariante-izará sobre cualquier código de Gauss con signos.

## Corchete de Kauffman
Las aristas son `e_j` (de la posición `j` a la `j+1`). En un cruce con paso superior en `o` e
inferior en `u`, las cuatro aristas incidentes son `e_{o-1}`, `e_o`, `e_{u-1}`, `e_u`. La
suavización orientada une `(e_{o-1}, e_u)` y `(e_{u-1}, e_o)`; la no orientada une
`(e_{o-1}, e_{u-1})` y `(e_o, e_u)`. En un cruce positivo la suavización A es la orientada; en uno
negativo, la no orientada (se comprueba con el rizo: ⟨rizo positivo⟩ = -A³).
Los lazos de un estado son las componentes conexas del grafo sobre las aristas.
-/

namespace TMENudos.Gauss

/-- Un paso por un cruce. -/
structure Letter where
  label : ℕ
  over : Bool
  pos : Bool
  deriving DecidableEq, Repr

/-- Una palabra de Gauss con signos (lista cíclica). -/
abbrev Word := List Letter

namespace Word

/-- Posición del paso por encima del cruce `c`. -/
def overPos (w : Word) (c : ℕ) : ℕ := w.findIdx (fun l => l.label == c && l.over)

/-- Posición del paso por debajo del cruce `c`. -/
def underPos (w : Word) (c : ℕ) : ℕ := w.findIdx (fun l => l.label == c && !l.over)

/-- Signo del cruce `c`. -/
def signOf (w : Word) (c : ℕ) : Bool :=
  ((w.find? (fun l => l.label == c && l.over)).map (·.pos)).getD true

/-- Las etiquetas de los cruces (una vez cada una, por su paso superior). -/
def crossings (w : Word) : List ℕ := (w.filter (·.over)).map (·.label)

/-- Buena formación: cada cruce aparece exactamente una vez por encima y una vez por debajo,
    con el mismo signo en ambos pasos. -/
def wf (w : Word) : Bool :=
  w.all fun l =>
    (w.filter (fun k => k.label == l.label && k.over)).length == 1 &&
    (w.filter (fun k => k.label == l.label && !k.over)).length == 1 &&
    (w.filter (fun k => k.label == l.label && k.pos != l.pos)).length == 0

/-- Las parejas de aristas que une la suavización `a` (`true` = A) del cruce `c`. -/
def pairsAt (w : Word) (c : ℕ) (a : Bool) : List (ℕ × ℕ) :=
  let m := w.length
  let prev := fun j => (j + m - 1) % m
  let o := overPos w c
  let u := underPos w c
  if a == signOf w c then [(prev o, u), (prev u, o)] else [(prev o, prev u), (o, u)]

/-- Une las componentes de las aristas `p.1` y `p.2` (etiquetado por relajación). -/
def unite (comp : List ℕ) (p : ℕ × ℕ) : List ℕ :=
  let ca := comp.getD p.1 0
  let cb := comp.getD p.2 0
  if ca == cb then comp else comp.map (fun c => if c == cb then ca else c)

/-- Número de lazos del estado `st` (una suavización por cruce, en el orden de `crossings`). -/
def loops (w : Word) (st : List Bool) : ℕ :=
  if w.length = 0 then 1
  else
    let pairs := ((crossings w).zip st).flatMap (fun (c, a) => pairsAt w c a)
    ((pairs.foldl unite (List.range w.length)).eraseDups).length

/-- Todas las asignaciones de suavizaciones de `k` cruces. -/
def allStates : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allStates k).flatMap fun s => [true :: s, false :: s]

/-- Para cada estado: (número de suavizaciones A, número de lazos). -/
def terms (w : Word) : List (ℕ × ℕ) :=
  (allStates (crossings w).length).map fun st => (st.count true, loops w st)

/-- Corchete de Kauffman, normalizado con ⟨círculo⟩ = 1, con `B = A⁻¹` y `d = -A² - A⁻²`. -/
def bracket {K : Type*} [Field K] (A : K) (w : Word) : K :=
  let n := (crossings w).length
  ((terms w).map fun (a, l) => A ^ a * A⁻¹ ^ (n - a) * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l - 1)).sum

/-- Writhe: suma de los signos de los cruces. -/
def writhe (w : Word) : ℤ :=
  ((w.filter (·.over)).map fun l => if l.pos then (1 : ℤ) else -1).sum

/-- Polinomio de Jones en la variable `A`: `(-A³)^{-w} ⟨D⟩`. -/
def jones {K : Type*} [Field K] (A : K) (w : Word) : K :=
  (-(A ^ 3)) ^ (-(writhe w)) * bracket A w

/-- Intercambio over/under en todos los cruces (imagen especular, τ): cambia también el signo. -/
def swap (w : Word) : Word := w.map fun l => { l with over := !l.over, pos := !l.pos }

/-- Desplaza las etiquetas. -/
def shift (k : ℕ) (w : Word) : Word := w.map fun l => { l with label := l.label + k }

/-- Mayor etiqueta usada más uno. -/
def fresh (w : Word) : ℕ := (w.map (·.label)).foldl max 0 + 1

/-- Suma conexa: concatenación (con las etiquetas de la segunda palabra desplazadas). -/
def concat (w₁ w₂ : Word) : Word := w₁ ++ shift (fresh w₁) w₂

end Word

open Word

/-- El trébol: código de Gauss `1 -2 3 -1 2 -3`, alternante. Con todos los signos positivos es el
    trébol derecho. -/
def trefoil : Word :=
  [⟨1, true, true⟩, ⟨2, false, true⟩, ⟨3, true, true⟩, ⟨1, false, true⟩, ⟨2, true, true⟩,
   ⟨3, false, true⟩]

/-- Rizo (un cruce) de signo positivo. -/
def kinkPos : Word := [⟨1, true, true⟩, ⟨1, false, true⟩]

/-- Rizo (un cruce) de signo negativo. -/
def kinkNeg : Word := [⟨1, true, false⟩, ⟨1, false, false⟩]

/-! ### Comprobaciones computables (evaluación numérica en ℚ con A = 2) -/

#eval wf trefoil
#eval wf (swap trefoil)
#eval wf (concat trefoil trefoil)
#eval terms trefoil
#eval terms kinkPos

-- ⟨rizo positivo⟩ = -A³ = -8 ;  ⟨rizo negativo⟩ = -A⁻³ = -1/8
#eval bracket (2 : ℚ) kinkPos
#eval bracket (2 : ℚ) kinkNeg
-- ⟨trébol⟩ = A⁻⁷ - A⁻³ - A⁵ = 1/128 - 1/8 - 32
#eval bracket (2 : ℚ) trefoil
#eval ((2 : ℚ) ^ (-(7 : ℤ)) - (2 : ℚ) ^ (-(3 : ℤ)) - (2 : ℚ) ^ 5)
-- ⟨espejo⟩ = A⁷ - A³ - A⁻⁵
#eval bracket (2 : ℚ) (swap trefoil)
#eval ((2 : ℚ) ^ 7 - (2 : ℚ) ^ 3 - (2 : ℚ) ^ (-(5 : ℤ)))
-- invariancia por rotación del punto de partida
#eval (List.range 6).map fun k => bracket (2 : ℚ) (trefoil.rotate k)
-- Jones con t = A⁻⁴ = 1/16 :  V(trébol) = t + t³ - t⁴
#eval jones (2 : ℚ) trefoil
#eval ((1 / 16 : ℚ) + (1 / 16) ^ 3 - (1 / 16) ^ 4)
-- suma conexa: ⟨K₁ # K₂⟩ = ⟨K₁⟩⟨K₂⟩
#eval bracket (2 : ℚ) (concat trefoil trefoil)
#eval bracket (2 : ℚ) trefoil * bracket (2 : ℚ) trefoil
#eval bracket (2 : ℚ) (concat trefoil (swap trefoil))
#eval bracket (2 : ℚ) trefoil * bracket (2 : ℚ) (swap trefoil)
-- nudo de la abuela frente al nudo cuadrado (Jones)
#eval jones (2 : ℚ) (concat trefoil trefoil)
#eval jones (2 : ℚ) (concat trefoil (swap trefoil))

/-! ### Teoremas demostrados -/

theorem wf_trefoil : wf trefoil = true := by decide

theorem wf_swap_trefoil : wf (swap trefoil) = true := by decide

/-- Los 8 estados del trébol: (número de suavizaciones A, número de lazos). -/
theorem terms_trefoil :
    terms trefoil = [(3, 2), (2, 1), (2, 1), (1, 2), (2, 1), (1, 2), (1, 2), (0, 3)] := by decide

/-- Estados del espejo: al cambiar los signos, las suavizaciones A y B intercambian su papel. -/
theorem terms_swap_trefoil :
    terms (swap trefoil) = [(3, 3), (2, 2), (2, 2), (1, 1), (2, 2), (1, 1), (1, 1), (0, 2)] := by
  decide

/-- **Corchete del trébol derecho**: ⟨3₁⟩ = A⁻⁷ - A⁻³ - A⁵. Demostrado en cualquier cuerpo. -/
theorem bracket_trefoil {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    bracket A trefoil = A⁻¹ ^ 7 - A⁻¹ ^ 3 - A ^ 5 := by
  have hn : (crossings trefoil).length = 3 := by decide
  unfold bracket
  simp only [hn, terms_trefoil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  field_simp
  ring

/-- **Corchete del trébol izquierdo** (imagen especular): ⟨3₁*⟩ = A⁷ - A³ - A⁻⁵. -/
theorem bracket_swap_trefoil {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    bracket A (swap trefoil) = A ^ 7 - A ^ 3 - A⁻¹ ^ 5 := by
  have hn : (crossings (swap trefoil)).length = 3 := by decide
  unfold bracket
  simp only [hn, terms_swap_trefoil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  field_simp
  ring

/-! ### Instancias de propiedades generales (aún no demostradas en general; ver el hito M4)

Estos teoremas son casos concretos evaluados en ℚ con A = 2. Sirven como pruebas de cordura de las
convenciones y como andamio para el hito M4 (invariancia bajo R1, R2, R3 y rotación). -/

theorem bracket_kinkPos : bracket (2 : ℚ) kinkPos = -8 := by decide +kernel

theorem bracket_kinkNeg : bracket (2 : ℚ) kinkNeg = -1 / 8 := by decide +kernel

/-- Invariancia del corchete por rotación del punto de partida, para el trébol en A = 2. -/
theorem bracket_trefoil_rotate :
    ∀ k ∈ List.range 6, bracket (2 : ℚ) (trefoil.rotate k) = bracket (2 : ℚ) trefoil := by
  decide +kernel

/-- Multiplicatividad del corchete bajo la suma conexa, para trébol # trébol en A = 2. -/
theorem bracket_concat_trefoil :
    bracket (2 : ℚ) (concat trefoil trefoil) = bracket (2 : ℚ) trefoil * bracket (2 : ℚ) trefoil := by
  decide +kernel

/-- Idem para trébol # espejo. -/
theorem bracket_concat_trefoil_swap :
    bracket (2 : ℚ) (concat trefoil (swap trefoil)) =
      bracket (2 : ℚ) trefoil * bracket (2 : ℚ) (swap trefoil) := by
  decide +kernel

/-- **Meta del spike.** El polinomio de Jones del nudo de la abuela (trébol # trébol) y el del nudo
    cuadrado (trébol # su espejo) difieren: evaluados en A = 2 dan valores distintos. Junto con la
    invariancia de Jones bajo R1-R3 (hito M4, todavía sin demostrar) esto cerraría
    `granny_distinct_from_square`. -/
theorem jones_granny_ne_square :
    jones (2 : ℚ) (concat trefoil trefoil) ≠ jones (2 : ℚ) (concat trefoil (swap trefoil)) := by
  decide +kernel

#print axioms bracket_trefoil
#print axioms bracket_swap_trefoil
#print axioms jones_granny_ne_square
#print axioms bracket_concat_trefoil

end TMENudos.Gauss
