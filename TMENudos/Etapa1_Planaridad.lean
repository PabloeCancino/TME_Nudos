import TMENudos.Etapa1_GaussWord
import TMENudos.TCN_08_Realizabilidad

/-!
# Etapa 1: planaridad exacta de una palabra de Gauss firmada, y el índice cero NO basta

Capa paralela (NO la importa `TMENudos.lean`). Formaliza la sonda
`Procesos/Tests/auditoria_20260929/15_genero_vs_indice_cero.py`.

## Convención (idéntica a la sonda)
Una palabra `w` de longitud `m` tiene `2m` semiaristas ("darts"): en la posición `p`,
`out p = 2p` es la semiarista que SALE del paso `p` (hacia el paso `p+1`) e `in p = 2p+1`
la que ENTRA al paso `p` (desde el paso `p-1`). La involución `alpha` es el pegado de aristas:
`alpha (out p) = in (p+1)`, `alpha (in q) = out (q-1)` (índices módulo `m`).

En el vértice de un cruce con paso superior en `o` e inferior en `u`, el signo fija el orden
cíclico ANTIHORARIO `sigma` de las cuatro semiaristas:
* cruce positivo: `out o → out u → in o → in u → out o`;
* cruce negativo: `out o → in u → in o → out u → out o`.

Las **caras** son los ciclos de `sigma ∘ alpha` (primero `alpha`, luego `sigma`). El mapa es
planar (género 0) sii `V - E + F = 2` con `V = n`, `E = 2n`, es decir `F = n + 2`. La palabra
vacía (la circunferencia sin cruces) se declara planar aparte, porque la fórmula exige `n ≥ 1`.

## Resultado
`indexZero` (condición necesaria usada en `TCN_05`) NO es suficiente: hay una palabra de 4
cruces con índice cero y paridad de Gauss que no es planar (`indexZero_not_sufficient`).
Para K₃ sí coinciden: `indexZero_iff_planar_toWord` (960 casos por `decide +kernel`).
Que planar ⇒ índice cero se cumple hasta `n = 4` es una OBSERVACIÓN de la sonda (no un teorema
aquí).
-/

namespace TMENudos.Planaridad

open TMENudos.Gauss TMENudos.Gauss.Word

/-! ### Semiaristas, `alpha`, `sigma`, caras -/

/-- `alpha` sobre las semiaristas de una palabra de longitud `m`. -/
def alphaD (m d : ℕ) : ℕ :=
  if d % 2 = 0 then 2 * ((d / 2 + 1) % m) + 1 else 2 * ((d / 2 + m - 1) % m)

/-- `sigma`: rotación antihoraria en el vértice al que pertenece la semiarista `d`
    (ver la convención en el docstring del módulo). -/
def sigmaD (w : Word) (d : ℕ) : ℕ :=
  match w[d / 2]? with
  | none => d
  | some l =>
    let o := overPos w l.label
    let u := underPos w l.label
    if l.pos then
      if d = 2 * o then 2 * u
      else if d = 2 * u then 2 * o + 1
      else if d = 2 * o + 1 then 2 * u + 1
      else 2 * o
    else
      if d = 2 * o then 2 * u + 1
      else if d = 2 * u + 1 then 2 * o + 1
      else if d = 2 * o + 1 then 2 * u
      else 2 * o

/-- Tabla de la permutación `sigma ∘ alpha` sobre las `2m` semiaristas. -/
def phiTable (w : Word) : List ℕ :=
  (List.range (2 * w.length)).map fun d => sigmaD w (alphaD w.length d)

/-- Mínimo de la órbita de `d` bajo la tabla `t` (recorre `t.length` iterados; si `t` es una
    permutación, cubre la órbita entera). -/
def orbitMin (t : List ℕ) (d : ℕ) : ℕ :=
  ((List.range t.length).foldl
    (fun (st : ℕ × ℕ) _ => (min st.1 (t.getD st.2 0), t.getD st.2 0)) (d, d)).1

/-- **Número de caras**: ciclos de `sigma ∘ alpha` (una semiarista por órbita: la mínima). -/
def faces (w : Word) : ℕ :=
  let t := phiTable w
  ((List.range (2 * w.length)).filter fun d => orbitMin t d == d).length

/-- **Planaridad exacta**: la palabra vacía, o `F = n + 2` (fórmula de Euler en género 0). -/
def planar (w : Word) : Prop :=
  w = [] ∨ faces w = (crossings w).length + 2

instance (w : Word) : Decidable (planar w) :=
  inferInstanceAs (Decidable (w = [] ∨ faces w = (crossings w).length + 2))

/-! ### Controles -/

#eval faces trefoil
#eval faces (swap trefoil)

/-- El trébol derecho (todos los cruces positivos) es planar. -/
theorem planar_trefoil : planar trefoil := by decide

/-- Su imagen especular (`swap`: todos negativos) es planar. -/
theorem planar_swap_trefoil : planar (swap trefoil) := by decide

/-- Trébol con signos mixtos (mismas cuerdas, último cruce negativo): NO es planar. -/
def mixedTrefoilW : Word :=
  [⟨1, true, true⟩, ⟨2, false, true⟩, ⟨3, true, false⟩, ⟨1, false, true⟩, ⟨2, true, true⟩,
   ⟨3, false, false⟩]

theorem wf_mixedTrefoilW : wf mixedTrefoilW = true := by decide

theorem not_planar_mixedTrefoilW : ¬ planar mixedTrefoilW := by decide

/-! ### Índice cero y paridad de Gauss sobre palabras

Una cuerda es `(o, u, signo)`: posiciones del paso superior e inferior y signo. Es la misma
fórmula que `indexZero` de `TCN_05` (suma de `±signo` según el extremo superior de la otra
cuerda caiga en el arco `o+1 .. u-1`), con aritmética módulo `m = w.length`. -/

/-- Las cuerdas `(o, u, pos)` de una palabra. -/
def chordsW (w : Word) : List (ℕ × ℕ × Bool) :=
  (crossings w).map fun c => (overPos w c, underPos w c, signOf w c)

/-- `x` está estrictamente en el arco que va de `o` a `u` (posiciones `o+1, …, u-1`) módulo `m`. -/
def inArcW (m o u x : ℕ) : Bool :=
  decide (0 < (x + m - o) % m ∧ (x + m - o) % m < (u + m - o) % m)

/-- Las cuerdas `c` y `d` se entrelazan: cuatro extremos distintos y exactamente un extremo de
    `d` en el arco de `c`. -/
def interlaceW (m : ℕ) (c d : ℕ × ℕ × Bool) : Bool :=
  decide (c.1 ≠ d.1 ∧ c.1 ≠ d.2.1 ∧ c.2.1 ≠ d.1 ∧ c.2.1 ≠ d.2.1) &&
    (inArcW m c.1 c.2.1 d.1 != inArcW m c.1 c.2.1 d.2.1)

/-- Índice de la cuerda `c`. -/
def indexW (w : Word) (c : ℕ × ℕ × Bool) : ℤ :=
  ((chordsW w).map fun d =>
    if interlaceW w.length c d then
      (if inArcW w.length c.1 c.2.1 d.1 then (if d.2.2 then 1 else -1)
       else (if d.2.2 then -1 else 1))
    else 0).sum

/-- **Índice cero** sobre palabras. -/
def indexZeroW (w : Word) : Prop := ∀ c ∈ chordsW w, indexW w c = 0

instance (w : Word) : Decidable (indexZeroW w) := by unfold indexZeroW; infer_instance

/-- **Paridad de Gauss** sobre palabras: cada cuerda se entrelaza con un número par de otras. -/
def gaussEvenW (w : Word) : Prop :=
  ∀ c ∈ chordsW w, ((chordsW w).filter fun d => interlaceW w.length c d).length % 2 = 0

instance (w : Word) : Decidable (gaussEvenW w) := by unfold gaussEvenW; infer_instance

/-- Controles: el trébol y su espejo tienen índice cero y paridad de Gauss. -/
theorem trefoil_indexZeroW : indexZeroW trefoil ∧ gaussEvenW trefoil := by decide

theorem swap_trefoil_indexZeroW : indexZeroW (swap trefoil) ∧ gaussEvenW (swap trefoil) := by
  decide

/-- El trébol mixto no tiene índice cero (coherente con ser no planar). -/
theorem not_indexZeroW_mixedTrefoilW : ¬ indexZeroW mixedTrefoilW := by decide

/-! ### El contraejemplo: índice cero no basta -/

/-- Cuerdas `(sup, inf, signo)`: `(0,3,−), (1,6,+), (2,5,−), (4,7,−)`. -/
def counterW : Word :=
  [⟨0, true, false⟩, ⟨1, true, true⟩, ⟨2, true, false⟩, ⟨0, false, false⟩, ⟨3, true, false⟩,
   ⟨2, false, false⟩, ⟨1, false, true⟩, ⟨3, false, false⟩]

theorem wf_counterW : wf counterW = true := by decide

theorem counterW_length : (crossings counterW).length = 4 := by decide

/-- **CONTRAEJEMPLO.** Existe una palabra bien formada de 4 cruces con índice cero y paridad de
    Gauss que NO es planar (género > 0). Por tanto el índice cero NO es suficiente para la
    planaridad (el hallazgo de la sonda 15: hay 64 configuraciones así para `n = 4`). -/
theorem indexZero_not_sufficient :
    ∃ w : Word, wf w = true ∧ (crossings w).length = 4 ∧ indexZeroW w ∧ gaussEvenW w ∧
      ¬ planar w :=
  ⟨counterW, wf_counterW, counterW_length, by decide, by decide, by decide⟩

theorem faces_counterW : faces counterW = 4 := by decide

/-! ### Puente con `K3Config` -/

open KnotTheory

/-- Letra de la posición `i` de una configuración K₃, calculada por filtros y sumas sobre
    `K.pairs` (computable en el núcleo): etiqueta = mínimo de los dos extremos de su cuerda,
    `over` = es el extremo superior (`fst`), `pos` = signo de la cuerda. -/
def _root_.KnotTheory.K3Config.letterAt (K : K3Config) (i : ℕ) : Letter :=
  ⟨∑ p ∈ K.pairs.filter (fun p => p.fst.val = i ∨ p.snd.val = i), min p.fst.val p.snd.val,
   decide (∃ p ∈ K.pairs, p.fst.val = i),
   decide (∃ p ∈ K.pairs, p.pos = true ∧ (p.fst.val = i ∨ p.snd.val = i))⟩

/-- **La palabra de Gauss firmada de una configuración K₃** (posiciones `0..5`). -/
def _root_.KnotTheory.K3Config.toWord (K : K3Config) : Word := (List.range 6).map K.letterAt

/-- `toWord` siempre es una palabra bien formada de longitud 6. -/
theorem toWord_wf : ∀ K : K3Config, wf K.toWord = true ∧ K.toWord.length = 6 := by
  decide +kernel

/-- **Para K₃, el índice cero ES la planaridad exacta** (960 casos). -/
theorem indexZero_iff_planar_toWord : ∀ K : K3Config, indexZero K ↔ planar K.toWord := by
  decide +kernel

/-- La paridad de Gauss de `TCN_05` coincide con `gaussEvenW` de la palabra. -/
theorem gaussEven_iff_gaussEvenW : ∀ K : K3Config, gaussEven K ↔ gaussEvenW K.toWord := by
  decide +kernel

/-- El índice cero de `TCN_05` coincide con `indexZeroW` de la palabra. -/
theorem indexZero_iff_indexZeroW : ∀ K : K3Config, indexZero K ↔ indexZeroW K.toWord := by
  decide +kernel

/-- **Corolario.** Para K₃: realizable ⟺ irreducible (sin R1 ni R2) ∧ planar. -/
theorem isRealizable_iff_irreducible_planar (K : K3Config) :
    isRealizable K ↔ (¬hasR1 K ∧ ¬hasR2 K) ∧ planar K.toWord := by
  rw [realizable_eq_irreducible_indexZero, indexZero_iff_planar_toWord, and_assoc]

/-- Forma alternativa: realizable ⟺ irreducible ∧ gaussEven ∧ planar. -/
theorem isRealizable_iff_irreducible_gauss_planar (K : K3Config) :
    isRealizable K ↔ (¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K ∧ planar K.toWord := by
  unfold isRealizable
  rw [indexZero_iff_planar_toWord]

#print axioms planar_trefoil
#print axioms planar_swap_trefoil
#print axioms not_planar_mixedTrefoilW
#print axioms indexZero_not_sufficient
#print axioms toWord_wf
#print axioms indexZero_iff_planar_toWord
#print axioms isRealizable_iff_irreducible_planar

end TMENudos.Planaridad
