import Mathlib
import TMENudos.SpanAdecuado

/-!
# Minimalidad de cruces para palabras de Gauss verificadas (etapa S5b)

## Que queda DEMOSTRADO

* `checkW w` (computable, sobre `Word.loops`): al menos un cruce, `s_A + s_B = n + 2` y adecuacion
  A y B (un solo cambio de suavizacion desde el estado todo-A / todo-B baja los lazos).
* `checkW_correct`: si `Word.wf w` y `checkW w`, el diagrama `ofWord w hw` es `AAdequate`,
  `BAdequate`, tiene algun cruce y cumple `lazos allA + lazos allB = card Cross + 2`
  (puente `lazos_ofWordP_eq_loops`, `card_cross_ofWord`).
* `span_of_check`: `span ⟨w⟩ = 4 n`, con `n = (Word.crossings w).length`.
* `minimal_of_check`: todo diagrama de UNA curva, sin circunferencias libres, equivalente por
  `GRel` a `ofWord w hw` tiene al menos `n` cruces (generaliza `trefoil_minimal`, que se recupera
  como `trefoil_minimal'`).
* Nudos con nombre (palabras de `27_palabras_lean.py`, `decide +kernel`): `minimal_41`,
  `minimal_51`, `minimal_52`, `minimal_61`, `minimal_62`, `minimal_63`.
* Censos: para `n = 3, 4, 5` la enumeracion COMPLETA de los datos alternantes
  `(p, sigma, signos)` (`datos n`, `2 n! 2^n` palabras) filtrada por `passes` da exactamente
  4, 8 y 24 datos (`pasan_3`, `pasan_4`, `pasan_5`), como los reducidos planares alternantes de la
  sonda 22. Para `n = 6, 7`: cada dato de las listas `censo6` (168) y `censo7` (676) generadas por
  Python pasa el verificador (`censo6_passes`, `censo7_passes`), sin repeticiones.

## Que NO esta demostrado

* Que TODO diagrama alternante reducido planar pase `checkW` (es decir, que sea A- y B-adecuado y
  tenga `s_A + s_B = n + 2`): es la parte geometrica general de S5b, ABIERTA. Aqui solo se
  verifica caso por caso.
* La COMPLETITUD de `censo6` y `censo7` (que contengan todos los reducidos planares alternantes de
  6 y 7 cruces): es un hecho de la sonda de Python (168 y 676), no de Lean. La enumeracion por el
  kernel para `n = 6, 7` no es viable (92160 y 1.3 millones de palabras).
* Que `checkW` sea ademas necesario (palabras que fallan el chequeo pueden ser minimas).
-/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.SpanLaurent TMENudos.Nudos

/-! ### Verificador computable -/

/-- Estado todo-`true` con la posicion `i` cambiada a `false`. -/
def stA (n i : ℕ) : List Bool := (List.replicate n true).set i false

/-- Estado todo-`false` con la posicion `i` cambiada a `true`. -/
def stB (n i : ℕ) : List Bool := (List.replicate n false).set i true

/-- Verificador: al menos un cruce, `s_A + s_B = n + 2`, y adecuacion A y B (cambiar UNA
suavizacion desde el estado extremo baja estrictamente los lazos). -/
def checkW (w : Word) : Bool :=
  let n := (Word.crossings w).length
  let sA := Word.loops w (List.replicate n true)
  let sB := Word.loops w (List.replicate n false)
  decide (1 ≤ n) && decide (sA + sB = n + 2) &&
    (List.range n).all fun i =>
      decide (Word.loops w (stA n i) < sA) && decide (Word.loops w (stB n i) < sB)

theorem checkW_trefoil : checkW trefoil = true := by decide +kernel

/-! ### Puente: lazos y cruces -/

section Puente

variable {w : Word}

theorem card_cross_ofWordP (hw : WfP w) :
    Fintype.card (ofWordP w hw).Cross = (Word.crossings w).length := by
  rw [Fintype.card_congr (crossEquiv w hw), Fintype.card_fin]

/-- Los lazos del diagrama de una palabra son los lazos computables de la lista de estado. -/
theorem lazos_ofWordP_eq_loops (hw : WfP w) (σ : (ofWordP w hw).Cross → Bool) :
    (ofWordP w hw).lazos σ =
      Word.loops w (List.ofFn fun k => σ ((crossEquiv w hw).symm k)) := by
  rw [loops_eq hw]
  congr 1
  funext x
  simp

theorem ofFn_updateA (n i : ℕ) (hi : i < n) :
    List.ofFn (fun k : Fin n => Function.update (fun _ : Fin n => true) ⟨i, hi⟩ false k) =
      stA n i := by
  apply List.ext_getElem
  · simp [stA]
  · intro k h1 h2
    simp only [List.getElem_ofFn, stA, List.getElem_set, List.getElem_replicate]
    by_cases hk : k = i
    · subst hk; simp [Function.update]
    · simp [Function.update, Fin.ext_iff, hk, Ne.symm hk]

theorem ofFn_updateB (n i : ℕ) (hi : i < n) :
    List.ofFn (fun k : Fin n => Function.update (fun _ : Fin n => false) ⟨i, hi⟩ true k) =
      stB n i := by
  apply List.ext_getElem
  · simp [stB]
  · intro k h1 h2
    simp only [List.getElem_ofFn, stB, List.getElem_set, List.getElem_replicate]
    by_cases hk : k = i
    · subst hk; simp [Function.update]
    · simp [Function.update, Fin.ext_iff, hk, Ne.symm hk]

/-- Lo que extrae el verificador: tres hechos numericos sobre `loops`. -/
theorem checkW_unfold (w : Word) (h : checkW w = true) :
    1 ≤ (Word.crossings w).length ∧
    Word.loops w (List.replicate (Word.crossings w).length true) +
      Word.loops w (List.replicate (Word.crossings w).length false) =
        (Word.crossings w).length + 2 ∧
    (∀ i < (Word.crossings w).length,
      Word.loops w (stA (Word.crossings w).length i) <
        Word.loops w (List.replicate (Word.crossings w).length true) ∧
      Word.loops w (stB (Word.crossings w).length i) <
        Word.loops w (List.replicate (Word.crossings w).length false)) := by
  unfold checkW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem lazos_allA_ofWordP (hw : WfP w) :
    (ofWordP w hw).lazos (ofWordP w hw).allA =
      Word.loops w (List.replicate (Word.crossings w).length true) := by
  rw [lazos_ofWordP_eq_loops hw]
  congr 1
  rw [← List.ofFn_const]
  rfl

theorem lazos_allB_ofWordP (hw : WfP w) :
    (ofWordP w hw).lazos (ofWordP w hw).allB =
      Word.loops w (List.replicate (Word.crossings w).length false) := by
  rw [lazos_ofWordP_eq_loops hw]
  congr 1
  rw [← List.ofFn_const]
  rfl

theorem aAdequate_of_check (hw : WfP w) (h : checkW w = true) :
    AAdequate (ofWordP w hw) := by
  obtain ⟨-, -, h3⟩ := checkW_unfold w h
  intro x
  have hk := (h3 (crossEquiv w hw x).1 (crossEquiv w hw x).2).1
  rw [← ofFn_updateA _ _ (crossEquiv w hw x).2] at hk
  simp only [Fin.eta] at hk
  have hfun : (fun y => Function.update (fun _ => true) (crossEquiv w hw x) false
      (crossEquiv w hw y)) = Function.update (ofWordP w hw).allA x false := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · have : crossEquiv w hw y ≠ crossEquiv w hw x :=
        fun h => hy ((crossEquiv w hw).injective h)
      simp [Function.update_of_ne hy, Function.update_of_ne this, GDiag.allA]
  rw [loops_eq hw, hfun] at hk
  rw [lazos_allA_ofWordP hw]
  exact hk

theorem bAdequate_of_check (hw : WfP w) (h : checkW w = true) :
    BAdequate (ofWordP w hw) := by
  obtain ⟨-, -, h3⟩ := checkW_unfold w h
  intro x
  have hk := (h3 (crossEquiv w hw x).1 (crossEquiv w hw x).2).2
  rw [← ofFn_updateB _ _ (crossEquiv w hw x).2] at hk
  simp only [Fin.eta] at hk
  have hfun : (fun y => Function.update (fun _ => false) (crossEquiv w hw x) true
      (crossEquiv w hw y)) = Function.update (ofWordP w hw).allB x true := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · have : crossEquiv w hw y ≠ crossEquiv w hw x :=
        fun h => hy ((crossEquiv w hw).injective h)
      simp [Function.update_of_ne hy, Function.update_of_ne this, GDiag.allB]
  rw [loops_eq hw, hfun] at hk
  rw [lazos_allB_ofWordP hw]
  exact hk

end Puente

/-! ### Correccion general del verificador -/

/-- **Correccion del verificador.** Si `checkW w` pasa, el diagrama de `w` es A- y B-adecuado,
tiene algun cruce y cumple la igualdad de genero `s_A + s_B = c + 2`. -/
theorem checkW_correct (w : Word) (hw : Word.wf w = true) (h : checkW w = true) :
    AAdequate (ofWord w hw) ∧ BAdequate (ofWord w hw) ∧ Nonempty (ofWord w hw).Cross ∧
    (ofWord w hw).lazos (ofWord w hw).allA + (ofWord w hw).lazos (ofWord w hw).allB =
      Fintype.card (ofWord w hw).Cross + 2 := by
  have hP := wfP_of_wf w hw
  obtain ⟨h1, h2, -⟩ := checkW_unfold w h
  refine ⟨aAdequate_of_check hP h, bAdequate_of_check hP h, ?_, ?_⟩
  · rw [← Fintype.card_pos_iff]
    change 0 < Fintype.card (ofWordP w hP).Cross
    rw [card_cross_ofWordP hP]
    omega
  · change (ofWordP w hP).lazos (ofWordP w hP).allA + (ofWordP w hP).lazos (ofWordP w hP).allB
      = Fintype.card (ofWordP w hP).Cross + 2
    rw [lazos_allA_ofWordP hP, lazos_allB_ofWordP hP, card_cross_ofWordP hP]
    exact h2

theorem card_cross_ofWord (w : Word) (hw : Word.wf w = true) :
    Fintype.card (ofWord w hw).Cross = (Word.crossings w).length :=
  card_cross_ofWordP (wfP_of_wf w hw)

/-- **Span exacto** de toda palabra que pasa el verificador: `span ⟨w⟩ = 4 n`. -/
theorem span_of_check (w : Word) (hw : Word.wf w = true) (h : checkW w = true) :
    span (bracketL (ofWord w hw)) = 4 * (Word.crossings w).length := by
  obtain ⟨hA, hB, hne, hg⟩ := checkW_correct w hw h
  rw [← card_cross_ofWord w hw]
  exact span_bracketL_eq_four_mul _ hA hB hne hg

/-- **Minimalidad general**: todo diagrama de UNA curva sin circunferencias libres equivalente
por `GRel` a una palabra que pasa el verificador tiene al menos tantos cruces como la palabra. -/
theorem minimal_of_check (w : Word) (hw : Word.wf w = true) (hchk : checkW w = true)
    (d' : Diag) (h : GRel (Diag.mk _ (ofWord w hw)) d') (hf : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) :
    (Word.crossings w).length ≤ Fintype.card d'.D.Cross := by
  have hspan : span (bracketL d'.D) = 4 * (Word.crossings w).length := by
    rw [← span_bracketL_rel h]; exact span_of_check w hw hchk
  by_cases hne : Nonempty d'.D.Cross
  · have h1 := span_bracketL_le_of_nonempty d'.D hne
    have h2 := GDiag.lazos_allA_add_allB_le d'.D hf hc hne
    omega
  · rw [not_nonempty_iff] at hne
    have := span_bracketL_of_isEmpty d'.D hne hf
    omega

/-- El trebol como caso particular: `trefoil_minimal` se recupera del teorema general. -/
theorem trefoil_minimal' (d' : Diag)
    (h : GRel (Diag.mk _ (ofWord trefoil wf_trefoil)) d') (hf : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) : 3 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check trefoil wf_trefoil checkW_trefoil d' h hf hc
  have hn : (Word.crossings trefoil).length = 3 := by decide
  omega

end TMENudos.Puente

#print axioms TMENudos.Puente.checkW_correct
#print axioms TMENudos.Puente.span_of_check
#print axioms TMENudos.Puente.minimal_of_check
#print axioms TMENudos.Puente.trefoil_minimal'


/-! ### Nudos con nombre (palabras generadas por `27_palabras_lean.py`)

Diagramas alternantes planares reducidos, identificados por su polinomio de Jones. Cada uno pasa
el verificador, luego su span es `4 n` y `n` es una cota inferior de cruces. -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.SpanLaurent TMENudos.Nudos

/-- Palabra de Gauss alternante reducida de 4_1 (4 cruces). -/
def knot41 : Word :=
  [⟨1, true, false⟩, ⟨4, false, true⟩, ⟨2, true, true⟩, ⟨1, false, false⟩,
   ⟨3, true, false⟩, ⟨2, false, true⟩, ⟨4, true, true⟩, ⟨3, false, false⟩]

theorem wf_knot41 : Word.wf knot41 = true := by decide +kernel

theorem checkW_knot41 : checkW knot41 = true := by decide +kernel

theorem span_knot41 : span (bracketL (ofWord knot41 wf_knot41)) = 16 := by
    rw [span_of_check _ _ checkW_knot41]
    decide +kernel

/-- Todo diagrama de una curva sin libres equivalente por `GRel` a 4_1 tiene al menos 4
cruces. -/
theorem minimal_41 (d' : Diag) (h : GRel (Diag.mk _ (ofWord knot41 wf_knot41)) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    4 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check knot41 wf_knot41 checkW_knot41 d' h hf hc
  have hn : (Word.crossings knot41).length = 4 := by decide +kernel
  omega

/-- Palabra de Gauss alternante reducida de 5_1 (5 cruces). -/
def knot51 : Word :=
  [⟨1, true, false⟩, ⟨4, false, false⟩, ⟨2, true, false⟩, ⟨5, false, false⟩,
   ⟨3, true, false⟩, ⟨1, false, false⟩, ⟨4, true, false⟩, ⟨2, false, false⟩,
   ⟨5, true, false⟩, ⟨3, false, false⟩]

theorem wf_knot51 : Word.wf knot51 = true := by decide +kernel

theorem checkW_knot51 : checkW knot51 = true := by decide +kernel

theorem span_knot51 : span (bracketL (ofWord knot51 wf_knot51)) = 20 := by
    rw [span_of_check _ _ checkW_knot51]
    decide +kernel

/-- Todo diagrama de una curva sin libres equivalente por `GRel` a 5_1 tiene al menos 5
cruces. -/
theorem minimal_51 (d' : Diag) (h : GRel (Diag.mk _ (ofWord knot51 wf_knot51)) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    5 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check knot51 wf_knot51 checkW_knot51 d' h hf hc
  have hn : (Word.crossings knot51).length = 5 := by decide +kernel
  omega

/-- Palabra de Gauss alternante reducida de 5_2 (5 cruces). -/
def knot52 : Word :=
  [⟨1, true, false⟩, ⟨4, false, false⟩, ⟨2, true, false⟩, ⟨1, false, false⟩,
   ⟨3, true, false⟩, ⟨5, false, false⟩, ⟨4, true, false⟩, ⟨2, false, false⟩,
   ⟨5, true, false⟩, ⟨3, false, false⟩]

theorem wf_knot52 : Word.wf knot52 = true := by decide +kernel

theorem checkW_knot52 : checkW knot52 = true := by decide +kernel

theorem span_knot52 : span (bracketL (ofWord knot52 wf_knot52)) = 20 := by
    rw [span_of_check _ _ checkW_knot52]
    decide +kernel

/-- Todo diagrama de una curva sin libres equivalente por `GRel` a 5_2 tiene al menos 5
cruces. -/
theorem minimal_52 (d' : Diag) (h : GRel (Diag.mk _ (ofWord knot52 wf_knot52)) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    5 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check knot52 wf_knot52 checkW_knot52 d' h hf hc
  have hn : (Word.crossings knot52).length = 5 := by decide +kernel
  omega

/-- Palabra de Gauss alternante reducida de 6_1 (6 cruces). -/
def knot61 : Word :=
  [⟨1, true, false⟩, ⟨5, false, true⟩, ⟨2, true, true⟩, ⟨1, false, false⟩,
   ⟨3, true, false⟩, ⟨6, false, false⟩, ⟨4, true, false⟩, ⟨2, false, true⟩,
   ⟨5, true, true⟩, ⟨4, false, false⟩, ⟨6, true, false⟩, ⟨3, false, false⟩]

theorem wf_knot61 : Word.wf knot61 = true := by decide +kernel

theorem checkW_knot61 : checkW knot61 = true := by decide +kernel

theorem span_knot61 : span (bracketL (ofWord knot61 wf_knot61)) = 24 := by
    rw [span_of_check _ _ checkW_knot61]
    decide +kernel

/-- Todo diagrama de una curva sin libres equivalente por `GRel` a 6_1 tiene al menos 6
cruces. -/
theorem minimal_61 (d' : Diag) (h : GRel (Diag.mk _ (ofWord knot61 wf_knot61)) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    6 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check knot61 wf_knot61 checkW_knot61 d' h hf hc
  have hn : (Word.crossings knot61).length = 6 := by decide +kernel
  omega

/-- Palabra de Gauss alternante reducida de 6_2 (6 cruces). -/
def knot62 : Word :=
  [⟨1, true, false⟩, ⟨5, false, true⟩, ⟨2, true, true⟩, ⟨1, false, false⟩,
   ⟨3, true, false⟩, ⟨6, false, false⟩, ⟨4, true, false⟩, ⟨2, false, true⟩,
   ⟨5, true, true⟩, ⟨3, false, false⟩, ⟨6, true, false⟩, ⟨4, false, false⟩]

theorem wf_knot62 : Word.wf knot62 = true := by decide +kernel

theorem checkW_knot62 : checkW knot62 = true := by decide +kernel

theorem span_knot62 : span (bracketL (ofWord knot62 wf_knot62)) = 24 := by
    rw [span_of_check _ _ checkW_knot62]
    decide +kernel

/-- Todo diagrama de una curva sin libres equivalente por `GRel` a 6_2 tiene al menos 6
cruces. -/
theorem minimal_62 (d' : Diag) (h : GRel (Diag.mk _ (ofWord knot62 wf_knot62)) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    6 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check knot62 wf_knot62 checkW_knot62 d' h hf hc
  have hn : (Word.crossings knot62).length = 6 := by decide +kernel
  omega

/-- Palabra de Gauss alternante reducida de 6_3 (6 cruces). -/
def knot63 : Word :=
  [⟨1, true, false⟩, ⟨4, false, false⟩, ⟨2, true, false⟩, ⟨1, false, false⟩,
   ⟨3, true, true⟩, ⟨6, false, true⟩, ⟨4, true, false⟩, ⟨2, false, false⟩,
   ⟨5, true, true⟩, ⟨3, false, true⟩, ⟨6, true, true⟩, ⟨5, false, true⟩]

theorem wf_knot63 : Word.wf knot63 = true := by decide +kernel

theorem checkW_knot63 : checkW knot63 = true := by decide +kernel

theorem span_knot63 : span (bracketL (ofWord knot63 wf_knot63)) = 24 := by
    rw [span_of_check _ _ checkW_knot63]
    decide +kernel

/-- Todo diagrama de una curva sin libres equivalente por `GRel` a 6_3 tiene al menos 6
cruces. -/
theorem minimal_63 (d' : Diag) (h : GRel (Diag.mk _ (ofWord knot63 wf_knot63)) d')
    (hf : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    6 ≤ Fintype.card d'.D.Cross := by
  have := minimal_of_check knot63 wf_knot63 checkW_knot63 d' h hf hc
  have hn : (Word.crossings knot63).length = 6 := by decide +kernel
  omega

end TMENudos.Puente

#print axioms TMENudos.Puente.minimal_41
#print axioms TMENudos.Puente.minimal_51
#print axioms TMENudos.Puente.minimal_52
#print axioms TMENudos.Puente.minimal_61
#print axioms TMENudos.Puente.minimal_62
#print axioms TMENudos.Puente.minimal_63

/-! ### Censo por enumeracion de datos alternantes

Los datos `(p, sigma, mascara)` son los de `buildL` de `Reconstruccion.lean`: pasos superiores en
las posiciones `2 i + p`, paso inferior del cruce `i` en `2 sigma(i) + 1 - p`, signo `i` = bit `i`
de la mascara. -/

namespace TMENudos.Puente

open TMENudos.Gauss

/-- Palabra de Gauss de los datos `(p, sigma, mascara)` con `n` cruces (etiquetas `0..n-1`). -/
def wordOfData (n p : ℕ) (σ : List ℕ) (m : ℕ) : Word :=
  (List.range (2 * n)).map fun q =>
    if q % 2 = p then ⟨(q - p) / 2, true, m.testBit ((q - p) / 2)⟩
    else ⟨σ.idxOf ((q - (1 - p)) / 2), false, m.testBit (σ.idxOf ((q - (1 - p)) / 2))⟩

/-- Un dato pasa si pasa el verificador y su palabra esta bien formada. -/
def passes (n : ℕ) (d : ℕ × List ℕ × ℕ) : Bool :=
  checkW (wordOfData n d.1 d.2.1 d.2.2) && Word.wf (wordOfData n d.1 d.2.1 d.2.2)

/-- Permutaciones de una lista (con combustible), en orden lexicografico. -/
def permsOf : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, l => l.flatMap fun x => (permsOf k (l.erase x)).map (x :: ·)

/-- Los datos de `n` cruces con paridad `p` y `sigma 0 = a`. -/
def datosFrom (n p a : ℕ) : List (ℕ × List ℕ × ℕ) :=
  ((permsOf (n - 1) ((List.range n).erase a)).map (a :: ·)).flatMap fun σ =>
    (List.range (2 ^ n)).map fun m => (p, σ, m)

/-- Todos los datos de `n ≥ 1` cruces: `2 * n! * 2^n`, en orden lexicografico. -/
def datos (n : ℕ) : List (ℕ × List ℕ × ℕ) :=
  (List.range 2).flatMap fun p => (List.range n).flatMap fun a => datosFrom n p a

/-- Los datos de `n` cruces que pasan el verificador. -/
def pasan (n : ℕ) : List (ℕ × List ℕ × ℕ) := (datos n).filter (passes n)

/-- Numero de datos del trozo `(p, a)` que pasan el verificador. -/
def cnt (n p a : ℕ) : ℕ := ((datosFrom n p a).filter (passes n)).length

theorem pasan_length (n : ℕ) :
    (pasan n).length =
      ((List.range 2).map fun p => ((List.range n).map fun a => cnt n p a).sum).sum := by
  simp only [pasan, datos, cnt, List.filter_flatMap, List.length_flatMap]

theorem datos_3 : (datos 3).length = 96 := by decide +kernel
theorem datos_4 : (datos 4).length = 768 := by decide +kernel
theorem datos_5 : (datos 5).length = 7680 := by decide +kernel

/-- **Censo `n = 3`**: exactamente 4 datos pasan el verificador (los reducidos planares
alternantes de la sonda 22), y son estos (el segundo y el ultimo son el trebol y su imagen en
espejo con otra paridad). -/
theorem pasan_3 :
    pasan 3 = [(0, [1, 2, 0], 0), (0, [1, 2, 0], 7), (1, [2, 0, 1], 0), (1, [2, 0, 1], 7)] := by
  decide +kernel

/-- **Censo `n = 4`**: exactamente 8 datos (el nudo de ocho). -/
theorem pasan_4 :
    pasan 4 = [(0, [1, 2, 3, 0], 5), (0, [1, 2, 3, 0], 10), (0, [2, 3, 0, 1], 5),
      (0, [2, 3, 0, 1], 10), (1, [2, 3, 0, 1], 5), (1, [2, 3, 0, 1], 10),
      (1, [3, 0, 1, 2], 5), (1, [3, 0, 1, 2], 10)] := by
  decide +kernel

theorem cnt5_0_0 : cnt 5 0 0 = 0 := by decide +kernel

theorem cnt5_0_1 : cnt 5 0 1 = 2 := by decide +kernel

theorem cnt5_0_2 : cnt 5 0 2 = 8 := by decide +kernel

theorem cnt5_0_3 : cnt 5 0 3 = 2 := by decide +kernel

theorem cnt5_0_4 : cnt 5 0 4 = 0 := by decide +kernel

theorem cnt5_1_0 : cnt 5 1 0 = 0 := by decide +kernel

theorem cnt5_1_1 : cnt 5 1 1 = 0 := by decide +kernel

theorem cnt5_1_2 : cnt 5 1 2 = 2 := by decide +kernel

theorem cnt5_1_3 : cnt 5 1 3 = 8 := by decide +kernel

theorem cnt5_1_4 : cnt 5 1 4 = 2 := by decide +kernel

/-- **Censo `n = 5`**: exactamente 24 datos (5_1 y 5_2 con sus variantes), en 10 trozos para
acotar el coste del kernel. -/
theorem pasan_5 : (pasan 5).length = 24 := by
  rw [pasan_length]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.sum_cons, List.sum_nil, cnt5_0_0, cnt5_0_1, cnt5_0_2, cnt5_0_3,
    cnt5_0_4, cnt5_1_0, cnt5_1_1, cnt5_1_2, cnt5_1_3, cnt5_1_4]
  omega

end TMENudos.Puente

/-! ### Censos de longitud 6 y 7 generados por Python

Las listas son la salida de `27_palabras_lean.py`. Aqui se verifica en el kernel que CADA dato de la
lista pasa el verificador. NO se demuestra que la lista sea COMPLETA (que contenga todos los
reducidos planares alternantes): eso es un hecho de la sonda de Python (168 y 676). -/

namespace TMENudos.Puente

def censo6a : List (ℕ × List ℕ × ℕ) := [
  (0, [1, 2, 0, 4, 5, 3], 0), (0, [1, 2, 0, 4, 5, 3], 7), (0, [1, 2, 0, 4, 5, 3], 56),
  (0, [1, 2, 0, 4, 5, 3], 63), (0, [1, 3, 4, 0, 5, 2], 11), (0, [1, 3, 4, 0, 5, 2], 52),
  (0, [1, 3, 4, 5, 0, 2], 18), (0, [1, 3, 4, 5, 0, 2], 45), (0, [1, 3, 5, 4, 0, 2], 18),
  (0, [1, 3, 5, 4, 0, 2], 45), (0, [1, 4, 3, 5, 0, 2], 19), (0, [1, 4, 3, 5, 0, 2], 44),
  (0, [1, 5, 0, 4, 2, 3], 0), (0, [1, 5, 0, 4, 2, 3], 7), (0, [1, 5, 0, 4, 2, 3], 56),
  (0, [1, 5, 0, 4, 2, 3], 63), (0, [1, 5, 3, 4, 2, 0], 0), (0, [1, 5, 3, 4, 2, 0], 28),
  (0, [1, 5, 3, 4, 2, 0], 35), (0, [1, 5, 3, 4, 2, 0], 63), (0, [2, 3, 4, 0, 5, 1], 27),
  (0, [2, 3, 4, 0, 5, 1], 36), (0, [2, 3, 4, 5, 1, 0], 9), (0, [2, 3, 4, 5, 1, 0], 54),
  (0, [2, 3, 5, 4, 0, 1], 18), (0, [2, 3, 5, 4, 0, 1], 45), (0, [2, 3, 5, 4, 1, 0], 26),
  (0, [2, 3, 5, 4, 1, 0], 37), (0, [2, 4, 0, 5, 1, 3], 18), (0, [2, 4, 0, 5, 1, 3], 45),
  (0, [2, 4, 3, 0, 5, 1], 13), (0, [2, 4, 3, 0, 5, 1], 50), (0, [2, 4, 3, 5, 0, 1], 9),
  (0, [2, 4, 3, 5, 0, 1], 54), (0, [2, 4, 3, 5, 1, 0], 9), (0, [2, 4, 3, 5, 1, 0], 54),
  (0, [2, 4, 5, 0, 1, 3], 18), (0, [2, 4, 5, 0, 1, 3], 45), (0, [2, 4, 5, 1, 0, 3], 13),
  (0, [2, 4, 5, 1, 0, 3], 50), (0, [2, 5, 4, 0, 1, 3], 11), (0, [2, 5, 4, 0, 1, 3], 52),
  (0, [3, 2, 4, 0, 5, 1], 27), (0, [3, 2, 4, 0, 5, 1], 36), (0, [3, 2, 4, 5, 0, 1], 27),
  (0, [3, 2, 4, 5, 0, 1], 36), (0, [3, 2, 4, 5, 1, 0], 22), (0, [3, 2, 4, 5, 1, 0], 41),
  (0, [3, 2, 5, 4, 0, 1], 25), (0, [3, 2, 5, 4, 0, 1], 38), (0, [3, 4, 0, 5, 1, 2], 18),
  (0, [3, 4, 0, 5, 1, 2], 45), (0, [3, 4, 0, 5, 2, 1], 25), (0, [3, 4, 0, 5, 2, 1], 38),
  (0, [3, 4, 5, 0, 2, 1], 9), (0, [3, 4, 5, 0, 2, 1], 54), (0, [3, 4, 5, 1, 0, 2], 27),
  (0, [3, 4, 5, 1, 0, 2], 36), (0, [3, 5, 4, 0, 1, 2], 9), (0, [3, 5, 4, 0, 1, 2], 54),
  (0, [3, 5, 4, 0, 2, 1], 9), (0, [3, 5, 4, 0, 2, 1], 54), (0, [3, 5, 4, 1, 0, 2], 19),
  (0, [3, 5, 4, 1, 0, 2], 44), (0, [4, 2, 0, 1, 5, 3], 0), (0, [4, 2, 0, 1, 5, 3], 14),
  (0, [4, 2, 0, 1, 5, 3], 49), (0, [4, 2, 0, 1, 5, 3], 63), (0, [4, 2, 3, 1, 5, 0], 0),
  (0, [4, 2, 3, 1, 5, 0], 14), (0, [4, 2, 3, 1, 5, 0], 49), (0, [4, 2, 3, 1, 5, 0], 63),
  (0, [4, 3, 0, 5, 1, 2], 22), (0, [4, 3, 0, 5, 1, 2], 41), (0, [4, 3, 5, 0, 1, 2], 27),
  (0, [4, 3, 5, 0, 1, 2], 36), (0, [4, 3, 5, 0, 2, 1], 26), (0, [4, 3, 5, 0, 2, 1], 37),
  (0, [4, 3, 5, 1, 0, 2], 27), (0, [4, 3, 5, 1, 0, 2], 36), (0, [4, 5, 3, 1, 2, 0], 0),
  (0, [4, 5, 3, 1, 2, 0], 28), (0, [4, 5, 3, 1, 2, 0], 35), (0, [4, 5, 3, 1, 2, 0], 63)
  ]

def censo6b : List (ℕ × List ℕ × ℕ) := [
  (1, [2, 0, 1, 5, 3, 4], 0), (1, [2, 0, 1, 5, 3, 4], 7), (1, [2, 0, 1, 5, 3, 4], 56),
  (1, [2, 0, 1, 5, 3, 4], 63), (1, [2, 0, 4, 5, 3, 1], 0), (1, [2, 0, 4, 5, 3, 1], 28),
  (1, [2, 0, 4, 5, 3, 1], 35), (1, [2, 0, 4, 5, 3, 1], 63), (1, [2, 3, 1, 5, 0, 4], 0),
  (1, [2, 3, 1, 5, 0, 4], 7), (1, [2, 3, 1, 5, 0, 4], 56), (1, [2, 3, 1, 5, 0, 4], 63),
  (1, [2, 4, 0, 5, 1, 3], 18), (1, [2, 4, 0, 5, 1, 3], 45), (1, [2, 4, 5, 0, 1, 3], 18),
  (1, [2, 4, 5, 0, 1, 3], 45), (1, [2, 4, 5, 1, 0, 3], 11), (1, [2, 4, 5, 1, 0, 3], 52),
  (1, [2, 5, 4, 0, 1, 3], 19), (1, [2, 5, 4, 0, 1, 3], 44), (1, [3, 0, 5, 1, 2, 4], 11),
  (1, [3, 0, 5, 1, 2, 4], 52), (1, [3, 4, 0, 5, 1, 2], 18), (1, [3, 4, 0, 5, 1, 2], 45),
  (1, [3, 4, 0, 5, 2, 1], 26), (1, [3, 4, 0, 5, 2, 1], 37), (1, [3, 4, 5, 0, 2, 1], 9),
  (1, [3, 4, 5, 0, 2, 1], 54), (1, [3, 4, 5, 1, 0, 2], 27), (1, [3, 4, 5, 1, 0, 2], 36),
  (1, [3, 5, 0, 1, 2, 4], 18), (1, [3, 5, 0, 1, 2, 4], 45), (1, [3, 5, 0, 2, 1, 4], 13),
  (1, [3, 5, 0, 2, 1, 4], 50), (1, [3, 5, 1, 0, 2, 4], 18), (1, [3, 5, 1, 0, 2, 4], 45),
  (1, [3, 5, 4, 0, 1, 2], 9), (1, [3, 5, 4, 0, 1, 2], 54), (1, [3, 5, 4, 0, 2, 1], 9),
  (1, [3, 5, 4, 0, 2, 1], 54), (1, [3, 5, 4, 1, 0, 2], 13), (1, [3, 5, 4, 1, 0, 2], 50),
  (1, [4, 0, 5, 1, 2, 3], 9), (1, [4, 0, 5, 1, 2, 3], 54), (1, [4, 0, 5, 1, 3, 2], 9),
  (1, [4, 0, 5, 1, 3, 2], 54), (1, [4, 0, 5, 2, 1, 3], 19), (1, [4, 0, 5, 2, 1, 3], 44),
  (1, [4, 3, 0, 5, 1, 2], 25), (1, [4, 3, 0, 5, 1, 2], 38), (1, [4, 3, 5, 0, 1, 2], 27),
  (1, [4, 3, 5, 0, 1, 2], 36), (1, [4, 3, 5, 0, 2, 1], 22), (1, [4, 3, 5, 0, 2, 1], 41),
  (1, [4, 3, 5, 1, 0, 2], 27), (1, [4, 3, 5, 1, 0, 2], 36), (1, [4, 5, 0, 1, 3, 2], 9),
  (1, [4, 5, 0, 1, 3, 2], 54), (1, [4, 5, 0, 2, 1, 3], 27), (1, [4, 5, 0, 2, 1, 3], 36),
  (1, [4, 5, 1, 0, 2, 3], 18), (1, [4, 5, 1, 0, 2, 3], 45), (1, [4, 5, 1, 0, 3, 2], 25),
  (1, [4, 5, 1, 0, 3, 2], 38), (1, [5, 0, 4, 2, 3, 1], 0), (1, [5, 0, 4, 2, 3, 1], 28),
  (1, [5, 0, 4, 2, 3, 1], 35), (1, [5, 0, 4, 2, 3, 1], 63), (1, [5, 3, 1, 2, 0, 4], 0),
  (1, [5, 3, 1, 2, 0, 4], 14), (1, [5, 3, 1, 2, 0, 4], 49), (1, [5, 3, 1, 2, 0, 4], 63),
  (1, [5, 3, 4, 2, 0, 1], 0), (1, [5, 3, 4, 2, 0, 1], 14), (1, [5, 3, 4, 2, 0, 1], 49),
  (1, [5, 3, 4, 2, 0, 1], 63), (1, [5, 4, 0, 1, 2, 3], 27), (1, [5, 4, 0, 1, 2, 3], 36),
  (1, [5, 4, 0, 1, 3, 2], 26), (1, [5, 4, 0, 1, 3, 2], 37), (1, [5, 4, 0, 2, 1, 3], 27),
  (1, [5, 4, 0, 2, 1, 3], 36), (1, [5, 4, 1, 0, 2, 3], 22), (1, [5, 4, 1, 0, 2, 3], 41)
  ]

def censo7a : List (ℕ × List ℕ × ℕ) := [
  (0, [1, 2, 0, 4, 5, 6, 3], 40), (0, [1, 2, 0, 4, 5, 6, 3], 47), (0, [1, 2, 0, 4, 5, 6, 3], 80),
  (0, [1, 2, 0, 4, 5, 6, 3], 87), (0, [1, 2, 0, 5, 6, 3, 4], 40), (0, [1, 2, 0, 5, 6, 3, 4], 47),
  (0, [1, 2, 0, 5, 6, 3, 4], 80), (0, [1, 2, 0, 5, 6, 3, 4], 87), (0, [1, 2, 3, 0, 5, 6, 4], 5),
  (0, [1, 2, 3, 0, 5, 6, 4], 10), (0, [1, 2, 3, 0, 5, 6, 4], 117), (0, [1, 2, 3, 0, 5, 6, 4], 122),
  (0, [1, 2, 6, 0, 5, 3, 4], 5), (0, [1, 2, 6, 0, 5, 3, 4], 10), (0, [1, 2, 6, 0, 5, 3, 4], 117),
  (0, [1, 2, 6, 0, 5, 3, 4], 122), (0, [1, 2, 6, 4, 5, 3, 0], 5), (0, [1, 2, 6, 4, 5, 3, 0], 61),
  (0, [1, 2, 6, 4, 5, 3, 0], 66), (0, [1, 2, 6, 4, 5, 3, 0], 122), (0, [1, 3, 4, 5, 0, 6, 2], 37),
  (0, [1, 3, 4, 5, 0, 6, 2], 90), (0, [1, 3, 5, 0, 6, 2, 4], 47), (0, [1, 3, 5, 0, 6, 2, 4], 80),
  (0, [1, 3, 5, 4, 0, 6, 2], 9), (0, [1, 3, 5, 4, 0, 6, 2], 118), (0, [1, 3, 5, 6, 0, 2, 4], 54),
  (0, [1, 3, 5, 6, 0, 2, 4], 73), (0, [1, 3, 6, 5, 0, 2, 4], 5), (0, [1, 3, 6, 5, 0, 2, 4], 122),
  (0, [1, 4, 3, 5, 0, 6, 2], 36), (0, [1, 4, 3, 5, 0, 6, 2], 91), (0, [1, 4, 3, 5, 6, 0, 2], 21),
  (0, [1, 4, 3, 5, 6, 0, 2], 106), (0, [1, 4, 3, 6, 5, 0, 2], 17), (0, [1, 4, 3, 6, 5, 0, 2], 110),
  (0, [1, 4, 5, 6, 0, 3, 2], 0), (0, [1, 4, 5, 6, 0, 3, 2], 127), (0, [1, 4, 5, 6, 2, 0, 3], 21),
  (0, [1, 4, 5, 6, 2, 0, 3], 106), (0, [1, 4, 6, 5, 0, 2, 3], 0), (0, [1, 4, 6, 5, 0, 2, 3], 127),
  (0, [1, 4, 6, 5, 0, 3, 2], 0), (0, [1, 4, 6, 5, 0, 3, 2], 127), (0, [1, 4, 6, 5, 2, 0, 3], 5),
  (0, [1, 4, 6, 5, 2, 0, 3], 122), (0, [1, 5, 3, 4, 2, 6, 0], 33), (0, [1, 5, 3, 4, 2, 6, 0], 61),
  (0, [1, 5, 3, 4, 2, 6, 0], 66), (0, [1, 5, 3, 4, 2, 6, 0], 94), (0, [1, 5, 4, 6, 2, 0, 3], 20),
  (0, [1, 5, 4, 6, 2, 0, 3], 107), (0, [1, 5, 6, 4, 2, 3, 0], 5), (0, [1, 5, 6, 4, 2, 3, 0], 61),
  (0, [1, 5, 6, 4, 2, 3, 0], 66), (0, [1, 5, 6, 4, 2, 3, 0], 122), (0, [1, 6, 0, 4, 5, 2, 3], 40),
  (0, [1, 6, 0, 4, 5, 2, 3], 47), (0, [1, 6, 0, 4, 5, 2, 3], 80), (0, [1, 6, 0, 4, 5, 2, 3], 87),
  (0, [1, 6, 0, 5, 2, 3, 4], 40), (0, [1, 6, 0, 5, 2, 3, 4], 47), (0, [1, 6, 0, 5, 2, 3, 4], 80),
  (0, [1, 6, 0, 5, 2, 3, 4], 87), (0, [1, 6, 3, 4, 5, 2, 0], 20), (0, [1, 6, 3, 4, 5, 2, 0], 40),
  (0, [1, 6, 3, 4, 5, 2, 0], 87), (0, [1, 6, 3, 4, 5, 2, 0], 107), (0, [1, 6, 4, 5, 2, 3, 0], 20),
  (0, [1, 6, 4, 5, 2, 3, 0], 40), (0, [1, 6, 4, 5, 2, 3, 0], 87), (0, [1, 6, 4, 5, 2, 3, 0], 107),
  (0, [2, 3, 0, 1, 5, 6, 4], 5), (0, [2, 3, 0, 1, 5, 6, 4], 10), (0, [2, 3, 0, 1, 5, 6, 4], 117),
  (0, [2, 3, 0, 1, 5, 6, 4], 122), (0, [2, 3, 4, 6, 5, 1, 0], 45), (0, [2, 3, 4, 6, 5, 1, 0], 82),
  (0, [2, 3, 5, 0, 6, 1, 4], 0), (0, [2, 3, 5, 0, 6, 1, 4], 127), (0, [2, 3, 5, 4, 0, 6, 1], 41),
  (0, [2, 3, 5, 4, 0, 6, 1], 86), (0, [2, 4, 0, 5, 1, 6, 3], 5), (0, [2, 4, 0, 5, 1, 6, 3], 122),
  (0, [2, 4, 0, 5, 6, 1, 3], 0), (0, [2, 4, 0, 5, 6, 1, 3], 127), (0, [2, 4, 0, 6, 5, 1, 3], 0),
  (0, [2, 4, 0, 6, 5, 1, 3], 127), (0, [2, 4, 3, 6, 5, 0, 1], 43), (0, [2, 4, 3, 6, 5, 0, 1], 84),
  (0, [2, 4, 3, 6, 5, 1, 0], 59), (0, [2, 4, 3, 6, 5, 1, 0], 68), (0, [2, 4, 5, 6, 0, 1, 3], 0),
  (0, [2, 4, 5, 6, 0, 1, 3], 127), (0, [2, 4, 5, 6, 1, 0, 3], 0), (0, [2, 4, 5, 6, 1, 0, 3], 127),
  (0, [2, 4, 5, 6, 1, 3, 0], 27), (0, [2, 4, 5, 6, 1, 3, 0], 100), (0, [2, 4, 6, 0, 5, 1, 3], 0),
  (0, [2, 4, 6, 0, 5, 1, 3], 127), (0, [2, 4, 6, 1, 5, 0, 3], 47), (0, [2, 4, 6, 1, 5, 0, 3], 80),
  (0, [2, 4, 6, 5, 0, 3, 1], 0), (0, [2, 4, 6, 5, 0, 3, 1], 127), (0, [2, 4, 6, 5, 1, 3, 0], 40),
  (0, [2, 4, 6, 5, 1, 3, 0], 87), (0, [2, 5, 0, 4, 6, 1, 3], 5), (0, [2, 5, 0, 4, 6, 1, 3], 122),
  (0, [2, 5, 3, 0, 6, 1, 4], 47), (0, [2, 5, 3, 0, 6, 1, 4], 80), (0, [2, 5, 3, 6, 0, 1, 4], 43),
  (0, [2, 5, 3, 6, 0, 1, 4], 84), (0, [2, 5, 3, 6, 1, 0, 4], 20)
  ]

def censo7b : List (ℕ × List ℕ × ℕ) := [
  (0, [2, 5, 3, 6, 1, 0, 4], 107), (0, [2, 5, 4, 6, 0, 1, 3], 0), (0, [2, 5, 4, 6, 0, 1, 3], 127),
  (0, [2, 5, 4, 6, 1, 3, 0], 61), (0, [2, 5, 4, 6, 1, 3, 0], 66), (0, [2, 6, 0, 1, 5, 3, 4], 5),
  (0, [2, 6, 0, 1, 5, 3, 4], 10), (0, [2, 6, 0, 1, 5, 3, 4], 117), (0, [2, 6, 0, 1, 5, 3, 4], 122),
  (0, [2, 6, 0, 4, 5, 3, 1], 5), (0, [2, 6, 0, 4, 5, 3, 1], 61), (0, [2, 6, 0, 4, 5, 3, 1], 66),
  (0, [2, 6, 0, 4, 5, 3, 1], 122), (0, [2, 6, 4, 0, 5, 1, 3], 47), (0, [2, 6, 4, 0, 5, 1, 3], 80),
  (0, [3, 2, 4, 5, 6, 1, 0], 53), (0, [3, 2, 4, 5, 6, 1, 0], 74), (0, [3, 2, 4, 6, 5, 1, 0], 18),
  (0, [3, 2, 4, 6, 5, 1, 0], 109), (0, [3, 2, 5, 0, 6, 1, 4], 0), (0, [3, 2, 5, 0, 6, 1, 4], 127),
  (0, [3, 2, 5, 4, 0, 6, 1], 34), (0, [3, 2, 5, 4, 0, 6, 1], 93), (0, [3, 2, 5, 4, 6, 0, 1], 42),
  (0, [3, 2, 5, 4, 6, 0, 1], 85), (0, [3, 2, 5, 4, 6, 1, 0], 55), (0, [3, 2, 5, 4, 6, 1, 0], 72),
  (0, [3, 2, 5, 6, 0, 1, 4], 0), (0, [3, 2, 5, 6, 0, 1, 4], 127), (0, [3, 4, 0, 5, 1, 6, 2], 37),
  (0, [3, 4, 0, 5, 1, 6, 2], 90), (0, [3, 4, 0, 6, 5, 1, 2], 0), (0, [3, 4, 0, 6, 5, 1, 2], 127),
  (0, [3, 4, 5, 0, 2, 6, 1], 50), (0, [3, 4, 5, 0, 2, 6, 1], 77), (0, [3, 4, 5, 0, 6, 1, 2], 0),
  (0, [3, 4, 5, 0, 6, 1, 2], 127), (0, [3, 4, 5, 0, 6, 2, 1], 0), (0, [3, 4, 5, 0, 6, 2, 1], 127),
  (0, [3, 4, 5, 1, 0, 6, 2], 0), (0, [3, 4, 5, 1, 0, 6, 2], 127), (0, [3, 4, 5, 1, 6, 2, 0], 53),
  (0, [3, 4, 5, 1, 6, 2, 0], 74), (0, [3, 4, 5, 6, 0, 1, 2], 0), (0, [3, 4, 5, 6, 0, 1, 2], 127),
  (0, [3, 4, 5, 6, 0, 2, 1], 0), (0, [3, 4, 5, 6, 0, 2, 1], 127), (0, [3, 4, 5, 6, 1, 0, 2], 0),
  (0, [3, 4, 5, 6, 1, 0, 2], 127), (0, [3, 4, 5, 6, 2, 1, 0], 0), (0, [3, 4, 5, 6, 2, 1, 0], 127),
  (0, [3, 4, 6, 1, 5, 0, 2], 25), (0, [3, 4, 6, 1, 5, 0, 2], 102), (0, [3, 4, 6, 5, 0, 1, 2], 0),
  (0, [3, 4, 6, 5, 0, 1, 2], 127), (0, [3, 4, 6, 5, 1, 0, 2], 0), (0, [3, 4, 6, 5, 1, 0, 2], 127),
  (0, [3, 5, 0, 4, 6, 1, 2], 51), (0, [3, 5, 0, 4, 6, 1, 2], 76), (0, [3, 5, 0, 4, 6, 2, 1], 40),
  (0, [3, 5, 0, 4, 6, 2, 1], 87), (0, [3, 5, 0, 6, 2, 1, 4], 59), (0, [3, 5, 0, 6, 2, 1, 4], 68),
  (0, [3, 5, 4, 0, 2, 6, 1], 20), (0, [3, 5, 4, 0, 2, 6, 1], 107), (0, [3, 5, 4, 0, 6, 1, 2], 0),
  (0, [3, 5, 4, 0, 6, 1, 2], 127), (0, [3, 5, 4, 1, 6, 2, 0], 61), (0, [3, 5, 4, 1, 6, 2, 0], 66),
  (0, [3, 5, 4, 6, 0, 1, 2], 0), (0, [3, 5, 4, 6, 0, 1, 2], 127), (0, [3, 5, 4, 6, 1, 2, 0], 0),
  (0, [3, 5, 4, 6, 1, 2, 0], 127), (0, [3, 5, 4, 6, 2, 0, 1], 0), (0, [3, 5, 4, 6, 2, 0, 1], 127),
  (0, [3, 5, 4, 6, 2, 1, 0], 0), (0, [3, 5, 4, 6, 2, 1, 0], 127), (0, [3, 5, 6, 0, 2, 1, 4], 43),
  (0, [3, 5, 6, 0, 2, 1, 4], 84), (0, [3, 5, 6, 4, 0, 2, 1], 0), (0, [3, 5, 6, 4, 0, 2, 1], 127),
  (0, [3, 6, 4, 0, 5, 1, 2], 45), (0, [3, 6, 4, 0, 5, 1, 2], 82), (0, [3, 6, 4, 0, 5, 2, 1], 61),
  (0, [3, 6, 4, 0, 5, 2, 1], 66), (0, [3, 6, 4, 5, 0, 2, 1], 0), (0, [3, 6, 4, 5, 0, 2, 1], 127),
  (0, [3, 6, 5, 0, 1, 2, 4], 45), (0, [3, 6, 5, 0, 1, 2, 4], 82), (0, [3, 6, 5, 0, 2, 1, 4], 18),
  (0, [3, 6, 5, 0, 2, 1, 4], 109), (0, [3, 6, 5, 1, 0, 2, 4], 55), (0, [3, 6, 5, 1, 0, 2, 4], 72),
  (0, [3, 6, 5, 4, 0, 1, 2], 0), (0, [3, 6, 5, 4, 0, 1, 2], 127), (0, [3, 6, 5, 4, 0, 2, 1], 0),
  (0, [3, 6, 5, 4, 0, 2, 1], 127), (0, [4, 2, 0, 1, 5, 6, 3], 33), (0, [4, 2, 0, 1, 5, 6, 3], 47),
  (0, [4, 2, 0, 1, 5, 6, 3], 80), (0, [4, 2, 0, 1, 5, 6, 3], 94), (0, [4, 2, 3, 1, 5, 6, 0], 33),
  (0, [4, 2, 3, 1, 5, 6, 0], 47), (0, [4, 2, 3, 1, 5, 6, 0], 80), (0, [4, 2, 3, 1, 5, 6, 0], 94),
  (0, [4, 2, 5, 0, 6, 1, 3], 0), (0, [4, 2, 5, 0, 6, 1, 3], 127), (0, [4, 2, 5, 0, 6, 3, 1], 10),
  (0, [4, 2, 5, 0, 6, 3, 1], 117), (0, [4, 2, 5, 6, 0, 3, 1], 42), (0, [4, 2, 5, 6, 0, 3, 1], 85),
  (0, [4, 2, 6, 5, 0, 3, 1], 40), (0, [4, 2, 6, 5, 0, 3, 1], 87)
  ]

def censo7c : List (ℕ × List ℕ × ℕ) := [
  (0, [4, 3, 0, 5, 1, 6, 2], 33), (0, [4, 3, 0, 5, 1, 6, 2], 94), (0, [4, 3, 5, 0, 1, 6, 2], 0),
  (0, [4, 3, 5, 0, 1, 6, 2], 127), (0, [4, 3, 5, 0, 2, 6, 1], 33), (0, [4, 3, 5, 0, 2, 6, 1], 94),
  (0, [4, 3, 5, 1, 0, 6, 2], 0), (0, [4, 3, 5, 1, 0, 6, 2], 127), (0, [4, 3, 5, 1, 6, 0, 2], 0),
  (0, [4, 3, 5, 1, 6, 0, 2], 127), (0, [4, 3, 5, 1, 6, 2, 0], 10), (0, [4, 3, 5, 1, 6, 2, 0], 117),
  (0, [4, 3, 5, 6, 0, 1, 2], 0), (0, [4, 3, 5, 6, 0, 1, 2], 127), (0, [4, 3, 5, 6, 0, 2, 1], 0),
  (0, [4, 3, 5, 6, 0, 2, 1], 127), (0, [4, 3, 6, 1, 5, 0, 2], 10), (0, [4, 3, 6, 1, 5, 0, 2], 117),
  (0, [4, 3, 6, 5, 0, 1, 2], 0), (0, [4, 3, 6, 5, 0, 1, 2], 127), (0, [4, 5, 0, 6, 2, 1, 3], 21),
  (0, [4, 5, 0, 6, 2, 1, 3], 106), (0, [4, 5, 3, 1, 2, 6, 0], 33), (0, [4, 5, 3, 1, 2, 6, 0], 61),
  (0, [4, 5, 3, 1, 2, 6, 0], 66), (0, [4, 5, 3, 1, 2, 6, 0], 94), (0, [4, 5, 3, 6, 1, 0, 2], 0),
  (0, [4, 5, 3, 6, 1, 0, 2], 127), (0, [4, 5, 6, 1, 0, 3, 2], 42), (0, [4, 5, 6, 1, 0, 3, 2], 85),
  (0, [4, 6, 3, 5, 0, 1, 2], 38), (0, [4, 6, 3, 5, 0, 1, 2], 89), (0, [4, 6, 3, 5, 0, 2, 1], 61),
  (0, [4, 6, 3, 5, 0, 2, 1], 66), (0, [4, 6, 3, 5, 1, 0, 2], 20), (0, [4, 6, 3, 5, 1, 0, 2], 107),
  (0, [4, 6, 5, 1, 0, 2, 3], 53), (0, [4, 6, 5, 1, 0, 2, 3], 74), (0, [4, 6, 5, 1, 0, 3, 2], 34),
  (0, [4, 6, 5, 1, 0, 3, 2], 93), (0, [5, 2, 0, 1, 6, 3, 4], 33), (0, [5, 2, 0, 1, 6, 3, 4], 47),
  (0, [5, 2, 0, 1, 6, 3, 4], 80), (0, [5, 2, 0, 1, 6, 3, 4], 94), (0, [5, 2, 3, 0, 1, 6, 4], 10),
  (0, [5, 2, 3, 0, 1, 6, 4], 20), (0, [5, 2, 3, 0, 1, 6, 4], 107), (0, [5, 2, 3, 0, 1, 6, 4], 117),
  (0, [5, 2, 3, 1, 6, 0, 4], 33), (0, [5, 2, 3, 1, 6, 0, 4], 47), (0, [5, 2, 3, 1, 6, 0, 4], 80),
  (0, [5, 2, 3, 1, 6, 0, 4], 94), (0, [5, 2, 3, 4, 1, 6, 0], 10), (0, [5, 2, 3, 4, 1, 6, 0], 20),
  (0, [5, 2, 3, 4, 1, 6, 0], 107), (0, [5, 2, 3, 4, 1, 6, 0], 117), (0, [5, 2, 4, 0, 6, 1, 3], 10),
  (0, [5, 2, 4, 0, 6, 1, 3], 117), (0, [5, 2, 4, 6, 0, 1, 3], 19), (0, [5, 2, 4, 6, 0, 1, 3], 108),
  (0, [5, 2, 4, 6, 1, 0, 3], 33), (0, [5, 2, 4, 6, 1, 0, 3], 94), (0, [5, 3, 0, 1, 2, 6, 4], 10),
  (0, [5, 3, 0, 1, 2, 6, 4], 20), (0, [5, 3, 0, 1, 2, 6, 4], 107), (0, [5, 3, 0, 1, 2, 6, 4], 117),
  (0, [5, 3, 4, 1, 2, 6, 0], 10), (0, [5, 3, 4, 1, 2, 6, 0], 20), (0, [5, 3, 4, 1, 2, 6, 0], 107),
  (0, [5, 3, 4, 1, 2, 6, 0], 117), (0, [5, 3, 4, 6, 1, 0, 2], 0), (0, [5, 3, 4, 6, 1, 0, 2], 127),
  (0, [5, 3, 6, 4, 0, 1, 2], 41), (0, [5, 3, 6, 4, 0, 1, 2], 86), (0, [5, 3, 6, 4, 0, 2, 1], 40),
  (0, [5, 3, 6, 4, 0, 2, 1], 87), (0, [5, 3, 6, 4, 1, 0, 2], 33), (0, [5, 3, 6, 4, 1, 0, 2], 94),
  (0, [5, 4, 0, 6, 1, 2, 3], 37), (0, [5, 4, 0, 6, 1, 2, 3], 90), (0, [5, 4, 0, 6, 1, 3, 2], 36),
  (0, [5, 4, 0, 6, 1, 3, 2], 91), (0, [5, 4, 0, 6, 2, 1, 3], 17), (0, [5, 4, 0, 6, 2, 1, 3], 110),
  (0, [5, 4, 3, 6, 0, 1, 2], 0), (0, [5, 4, 3, 6, 0, 1, 2], 127), (0, [5, 4, 3, 6, 1, 0, 2], 0),
  (0, [5, 4, 3, 6, 1, 0, 2], 127), (0, [5, 4, 6, 0, 1, 3, 2], 41), (0, [5, 4, 6, 0, 1, 3, 2], 86),
  (0, [5, 4, 6, 1, 0, 3, 2], 9), (0, [5, 4, 6, 1, 0, 3, 2], 118), (0, [5, 6, 0, 4, 2, 3, 1], 5),
  (0, [5, 6, 0, 4, 2, 3, 1], 61), (0, [5, 6, 0, 4, 2, 3, 1], 66), (0, [5, 6, 0, 4, 2, 3, 1], 122),
  (0, [5, 6, 3, 1, 2, 0, 4], 33), (0, [5, 6, 3, 1, 2, 0, 4], 61), (0, [5, 6, 3, 1, 2, 0, 4], 66),
  (0, [5, 6, 3, 1, 2, 0, 4], 94), (0, [5, 6, 3, 4, 1, 2, 0], 20), (0, [5, 6, 3, 4, 1, 2, 0], 40),
  (0, [5, 6, 3, 4, 1, 2, 0], 87), (0, [5, 6, 3, 4, 1, 2, 0], 107), (0, [5, 6, 3, 4, 2, 0, 1], 33),
  (0, [5, 6, 3, 4, 2, 0, 1], 61), (0, [5, 6, 3, 4, 2, 0, 1], 66), (0, [5, 6, 3, 4, 2, 0, 1], 94),
  (0, [5, 6, 4, 1, 2, 3, 0], 20), (0, [5, 6, 4, 1, 2, 3, 0], 40), (0, [5, 6, 4, 1, 2, 3, 0], 87),
  (0, [5, 6, 4, 1, 2, 3, 0], 107), (1, [2, 0, 1, 5, 6, 3, 4], 40)
  ]

def censo7d : List (ℕ × List ℕ × ℕ) := [
  (1, [2, 0, 1, 5, 6, 3, 4], 47), (1, [2, 0, 1, 5, 6, 3, 4], 80), (1, [2, 0, 1, 5, 6, 3, 4], 87),
  (1, [2, 0, 1, 6, 3, 4, 5], 40), (1, [2, 0, 1, 6, 3, 4, 5], 47), (1, [2, 0, 1, 6, 3, 4, 5], 80),
  (1, [2, 0, 1, 6, 3, 4, 5], 87), (1, [2, 0, 4, 5, 6, 3, 1], 20), (1, [2, 0, 4, 5, 6, 3, 1], 40),
  (1, [2, 0, 4, 5, 6, 3, 1], 87), (1, [2, 0, 4, 5, 6, 3, 1], 107), (1, [2, 0, 5, 6, 3, 4, 1], 20),
  (1, [2, 0, 5, 6, 3, 4, 1], 40), (1, [2, 0, 5, 6, 3, 4, 1], 87), (1, [2, 0, 5, 6, 3, 4, 1], 107),
  (1, [2, 3, 0, 1, 6, 4, 5], 5), (1, [2, 3, 0, 1, 6, 4, 5], 10), (1, [2, 3, 0, 1, 6, 4, 5], 117),
  (1, [2, 3, 0, 1, 6, 4, 5], 122), (1, [2, 3, 0, 5, 6, 4, 1], 5), (1, [2, 3, 0, 5, 6, 4, 1], 61),
  (1, [2, 3, 0, 5, 6, 4, 1], 66), (1, [2, 3, 0, 5, 6, 4, 1], 122), (1, [2, 3, 1, 5, 6, 0, 4], 40),
  (1, [2, 3, 1, 5, 6, 0, 4], 47), (1, [2, 3, 1, 5, 6, 0, 4], 80), (1, [2, 3, 1, 5, 6, 0, 4], 87),
  (1, [2, 3, 1, 6, 0, 4, 5], 40), (1, [2, 3, 1, 6, 0, 4, 5], 47), (1, [2, 3, 1, 6, 0, 4, 5], 80),
  (1, [2, 3, 1, 6, 0, 4, 5], 87), (1, [2, 3, 4, 1, 6, 0, 5], 5), (1, [2, 3, 4, 1, 6, 0, 5], 10),
  (1, [2, 3, 4, 1, 6, 0, 5], 117), (1, [2, 3, 4, 1, 6, 0, 5], 122), (1, [2, 4, 0, 6, 1, 3, 5], 5),
  (1, [2, 4, 0, 6, 1, 3, 5], 122), (1, [2, 4, 5, 6, 1, 0, 3], 37), (1, [2, 4, 5, 6, 1, 0, 3], 90),
  (1, [2, 4, 6, 0, 1, 3, 5], 54), (1, [2, 4, 6, 0, 1, 3, 5], 73), (1, [2, 4, 6, 1, 0, 3, 5], 47),
  (1, [2, 4, 6, 1, 0, 3, 5], 80), (1, [2, 4, 6, 5, 1, 0, 3], 9), (1, [2, 4, 6, 5, 1, 0, 3], 118),
  (1, [2, 5, 0, 6, 1, 3, 4], 0), (1, [2, 5, 0, 6, 1, 3, 4], 127), (1, [2, 5, 0, 6, 1, 4, 3], 0),
  (1, [2, 5, 0, 6, 1, 4, 3], 127), (1, [2, 5, 0, 6, 3, 1, 4], 5), (1, [2, 5, 0, 6, 3, 1, 4], 122),
  (1, [2, 5, 4, 0, 6, 1, 3], 17), (1, [2, 5, 4, 0, 6, 1, 3], 110), (1, [2, 5, 4, 6, 0, 1, 3], 21),
  (1, [2, 5, 4, 6, 0, 1, 3], 106), (1, [2, 5, 4, 6, 1, 0, 3], 36), (1, [2, 5, 4, 6, 1, 0, 3], 91),
  (1, [2, 5, 6, 0, 1, 4, 3], 0), (1, [2, 5, 6, 0, 1, 4, 3], 127), (1, [2, 5, 6, 0, 3, 1, 4], 21),
  (1, [2, 5, 6, 0, 3, 1, 4], 106), (1, [2, 6, 0, 5, 3, 4, 1], 5), (1, [2, 6, 0, 5, 3, 4, 1], 61),
  (1, [2, 6, 0, 5, 3, 4, 1], 66), (1, [2, 6, 0, 5, 3, 4, 1], 122), (1, [2, 6, 4, 5, 3, 0, 1], 33),
  (1, [2, 6, 4, 5, 3, 0, 1], 61), (1, [2, 6, 4, 5, 3, 0, 1], 66), (1, [2, 6, 4, 5, 3, 0, 1], 94),
  (1, [2, 6, 5, 0, 3, 1, 4], 20), (1, [2, 6, 5, 0, 3, 1, 4], 107), (1, [3, 0, 1, 2, 6, 4, 5], 5),
  (1, [3, 0, 1, 2, 6, 4, 5], 10), (1, [3, 0, 1, 2, 6, 4, 5], 117), (1, [3, 0, 1, 2, 6, 4, 5], 122),
  (1, [3, 0, 1, 5, 6, 4, 2], 5), (1, [3, 0, 1, 5, 6, 4, 2], 61), (1, [3, 0, 1, 5, 6, 4, 2], 66),
  (1, [3, 0, 1, 5, 6, 4, 2], 122), (1, [3, 0, 5, 1, 6, 2, 4], 47), (1, [3, 0, 5, 1, 6, 2, 4], 80),
  (1, [3, 4, 1, 2, 6, 0, 5], 5), (1, [3, 4, 1, 2, 6, 0, 5], 10), (1, [3, 4, 1, 2, 6, 0, 5], 117),
  (1, [3, 4, 1, 2, 6, 0, 5], 122), (1, [3, 4, 5, 0, 6, 2, 1], 45), (1, [3, 4, 5, 0, 6, 2, 1], 82),
  (1, [3, 4, 6, 1, 0, 2, 5], 0), (1, [3, 4, 6, 1, 0, 2, 5], 127), (1, [3, 4, 6, 5, 1, 0, 2], 41),
  (1, [3, 4, 6, 5, 1, 0, 2], 86), (1, [3, 5, 0, 1, 6, 2, 4], 0), (1, [3, 5, 0, 1, 6, 2, 4], 127),
  (1, [3, 5, 0, 2, 6, 1, 4], 47), (1, [3, 5, 0, 2, 6, 1, 4], 80), (1, [3, 5, 0, 6, 1, 4, 2], 0),
  (1, [3, 5, 0, 6, 1, 4, 2], 127), (1, [3, 5, 0, 6, 2, 4, 1], 40), (1, [3, 5, 0, 6, 2, 4, 1], 87),
  (1, [3, 5, 1, 0, 6, 2, 4], 0), (1, [3, 5, 1, 0, 6, 2, 4], 127), (1, [3, 5, 1, 6, 0, 2, 4], 0),
  (1, [3, 5, 1, 6, 0, 2, 4], 127), (1, [3, 5, 1, 6, 2, 0, 4], 5), (1, [3, 5, 1, 6, 2, 0, 4], 122),
  (1, [3, 5, 4, 0, 6, 1, 2], 43), (1, [3, 5, 4, 0, 6, 1, 2], 84), (1, [3, 5, 4, 0, 6, 2, 1], 59),
  (1, [3, 5, 4, 0, 6, 2, 1], 68), (1, [3, 5, 6, 0, 1, 2, 4], 0), (1, [3, 5, 6, 0, 1, 2, 4], 127),
  (1, [3, 5, 6, 0, 2, 1, 4], 0), (1, [3, 5, 6, 0, 2, 1, 4], 127)
  ]

def censo7e : List (ℕ × List ℕ × ℕ) := [
  (1, [3, 5, 6, 0, 2, 4, 1], 27), (1, [3, 5, 6, 0, 2, 4, 1], 100), (1, [3, 6, 1, 5, 0, 2, 4], 5),
  (1, [3, 6, 1, 5, 0, 2, 4], 122), (1, [3, 6, 4, 0, 1, 2, 5], 43), (1, [3, 6, 4, 0, 1, 2, 5], 84),
  (1, [3, 6, 4, 0, 2, 1, 5], 20), (1, [3, 6, 4, 0, 2, 1, 5], 107), (1, [3, 6, 4, 1, 0, 2, 5], 47),
  (1, [3, 6, 4, 1, 0, 2, 5], 80), (1, [3, 6, 5, 0, 1, 2, 4], 0), (1, [3, 6, 5, 0, 1, 2, 4], 127),
  (1, [3, 6, 5, 0, 2, 4, 1], 61), (1, [3, 6, 5, 0, 2, 4, 1], 66), (1, [4, 0, 5, 1, 6, 2, 3], 45),
  (1, [4, 0, 5, 1, 6, 2, 3], 82), (1, [4, 0, 5, 1, 6, 3, 2], 61), (1, [4, 0, 5, 1, 6, 3, 2], 66),
  (1, [4, 0, 5, 6, 1, 3, 2], 0), (1, [4, 0, 5, 6, 1, 3, 2], 127), (1, [4, 0, 6, 1, 2, 3, 5], 45),
  (1, [4, 0, 6, 1, 2, 3, 5], 82), (1, [4, 0, 6, 1, 3, 2, 5], 18), (1, [4, 0, 6, 1, 3, 2, 5], 109),
  (1, [4, 0, 6, 2, 1, 3, 5], 55), (1, [4, 0, 6, 2, 1, 3, 5], 72), (1, [4, 0, 6, 5, 1, 2, 3], 0),
  (1, [4, 0, 6, 5, 1, 2, 3], 127), (1, [4, 0, 6, 5, 1, 3, 2], 0), (1, [4, 0, 6, 5, 1, 3, 2], 127),
  (1, [4, 3, 5, 0, 6, 2, 1], 18), (1, [4, 3, 5, 0, 6, 2, 1], 109), (1, [4, 3, 5, 6, 0, 2, 1], 53),
  (1, [4, 3, 5, 6, 0, 2, 1], 74), (1, [4, 3, 6, 0, 1, 2, 5], 0), (1, [4, 3, 6, 0, 1, 2, 5], 127),
  (1, [4, 3, 6, 1, 0, 2, 5], 0), (1, [4, 3, 6, 1, 0, 2, 5], 127), (1, [4, 3, 6, 5, 0, 1, 2], 42),
  (1, [4, 3, 6, 5, 0, 1, 2], 85), (1, [4, 3, 6, 5, 0, 2, 1], 55), (1, [4, 3, 6, 5, 0, 2, 1], 72),
  (1, [4, 3, 6, 5, 1, 0, 2], 34), (1, [4, 3, 6, 5, 1, 0, 2], 93), (1, [4, 5, 0, 2, 6, 1, 3], 25),
  (1, [4, 5, 0, 2, 6, 1, 3], 102), (1, [4, 5, 0, 6, 1, 2, 3], 0), (1, [4, 5, 0, 6, 1, 2, 3], 127),
  (1, [4, 5, 0, 6, 2, 1, 3], 0), (1, [4, 5, 0, 6, 2, 1, 3], 127), (1, [4, 5, 1, 0, 6, 2, 3], 0),
  (1, [4, 5, 1, 0, 6, 2, 3], 127), (1, [4, 5, 1, 6, 2, 0, 3], 37), (1, [4, 5, 1, 6, 2, 0, 3], 90),
  (1, [4, 5, 6, 0, 1, 2, 3], 0), (1, [4, 5, 6, 0, 1, 2, 3], 127), (1, [4, 5, 6, 0, 1, 3, 2], 0),
  (1, [4, 5, 6, 0, 1, 3, 2], 127), (1, [4, 5, 6, 0, 2, 1, 3], 0), (1, [4, 5, 6, 0, 2, 1, 3], 127),
  (1, [4, 5, 6, 0, 3, 2, 1], 0), (1, [4, 5, 6, 0, 3, 2, 1], 127), (1, [4, 5, 6, 1, 0, 2, 3], 0),
  (1, [4, 5, 6, 1, 0, 2, 3], 127), (1, [4, 5, 6, 1, 0, 3, 2], 0), (1, [4, 5, 6, 1, 0, 3, 2], 127),
  (1, [4, 5, 6, 1, 3, 0, 2], 50), (1, [4, 5, 6, 1, 3, 0, 2], 77), (1, [4, 5, 6, 2, 0, 3, 1], 53),
  (1, [4, 5, 6, 2, 0, 3, 1], 74), (1, [4, 5, 6, 2, 1, 0, 3], 0), (1, [4, 5, 6, 2, 1, 0, 3], 127),
  (1, [4, 6, 0, 1, 3, 2, 5], 43), (1, [4, 6, 0, 1, 3, 2, 5], 84), (1, [4, 6, 0, 5, 1, 3, 2], 0),
  (1, [4, 6, 0, 5, 1, 3, 2], 127), (1, [4, 6, 1, 0, 3, 2, 5], 59), (1, [4, 6, 1, 0, 3, 2, 5], 68),
  (1, [4, 6, 1, 5, 0, 2, 3], 51), (1, [4, 6, 1, 5, 0, 2, 3], 76), (1, [4, 6, 1, 5, 0, 3, 2], 40),
  (1, [4, 6, 1, 5, 0, 3, 2], 87), (1, [4, 6, 5, 0, 1, 2, 3], 0), (1, [4, 6, 5, 0, 1, 2, 3], 127),
  (1, [4, 6, 5, 0, 2, 3, 1], 0), (1, [4, 6, 5, 0, 2, 3, 1], 127), (1, [4, 6, 5, 0, 3, 1, 2], 0),
  (1, [4, 6, 5, 0, 3, 1, 2], 127), (1, [4, 6, 5, 0, 3, 2, 1], 0), (1, [4, 6, 5, 0, 3, 2, 1], 127),
  (1, [4, 6, 5, 1, 0, 2, 3], 0), (1, [4, 6, 5, 1, 0, 2, 3], 127), (1, [4, 6, 5, 1, 3, 0, 2], 20),
  (1, [4, 6, 5, 1, 3, 0, 2], 107), (1, [4, 6, 5, 2, 0, 3, 1], 61), (1, [4, 6, 5, 2, 0, 3, 1], 66),
  (1, [5, 0, 4, 6, 1, 2, 3], 38), (1, [5, 0, 4, 6, 1, 2, 3], 89), (1, [5, 0, 4, 6, 1, 3, 2], 61),
  (1, [5, 0, 4, 6, 1, 3, 2], 66), (1, [5, 0, 4, 6, 2, 1, 3], 20), (1, [5, 0, 4, 6, 2, 1, 3], 107),
  (1, [5, 0, 6, 2, 1, 3, 4], 53), (1, [5, 0, 6, 2, 1, 3, 4], 74), (1, [5, 0, 6, 2, 1, 4, 3], 34),
  (1, [5, 0, 6, 2, 1, 4, 3], 93), (1, [5, 3, 0, 6, 1, 4, 2], 40), (1, [5, 3, 0, 6, 1, 4, 2], 87),
  (1, [5, 3, 1, 2, 6, 0, 4], 33), (1, [5, 3, 1, 2, 6, 0, 4], 47), (1, [5, 3, 1, 2, 6, 0, 4], 80),
  (1, [5, 3, 1, 2, 6, 0, 4], 94), (1, [5, 3, 4, 2, 6, 0, 1], 33)
  ]

def censo7f : List (ℕ × List ℕ × ℕ) := [
  (1, [5, 3, 4, 2, 6, 0, 1], 47), (1, [5, 3, 4, 2, 6, 0, 1], 80), (1, [5, 3, 4, 2, 6, 0, 1], 94),
  (1, [5, 3, 6, 0, 1, 4, 2], 42), (1, [5, 3, 6, 0, 1, 4, 2], 85), (1, [5, 3, 6, 1, 0, 2, 4], 0),
  (1, [5, 3, 6, 1, 0, 2, 4], 127), (1, [5, 3, 6, 1, 0, 4, 2], 10), (1, [5, 3, 6, 1, 0, 4, 2], 117),
  (1, [5, 4, 0, 2, 6, 1, 3], 10), (1, [5, 4, 0, 2, 6, 1, 3], 117), (1, [5, 4, 0, 6, 1, 2, 3], 0),
  (1, [5, 4, 0, 6, 1, 2, 3], 127), (1, [5, 4, 1, 6, 2, 0, 3], 33), (1, [5, 4, 1, 6, 2, 0, 3], 94),
  (1, [5, 4, 6, 0, 1, 2, 3], 0), (1, [5, 4, 6, 0, 1, 2, 3], 127), (1, [5, 4, 6, 0, 1, 3, 2], 0),
  (1, [5, 4, 6, 0, 1, 3, 2], 127), (1, [5, 4, 6, 1, 2, 0, 3], 0), (1, [5, 4, 6, 1, 2, 0, 3], 127),
  (1, [5, 4, 6, 1, 3, 0, 2], 33), (1, [5, 4, 6, 1, 3, 0, 2], 94), (1, [5, 4, 6, 2, 0, 1, 3], 0),
  (1, [5, 4, 6, 2, 0, 1, 3], 127), (1, [5, 4, 6, 2, 0, 3, 1], 10), (1, [5, 4, 6, 2, 0, 3, 1], 117),
  (1, [5, 4, 6, 2, 1, 0, 3], 0), (1, [5, 4, 6, 2, 1, 0, 3], 127), (1, [5, 6, 0, 2, 1, 4, 3], 42),
  (1, [5, 6, 0, 2, 1, 4, 3], 85), (1, [5, 6, 1, 0, 3, 2, 4], 21), (1, [5, 6, 1, 0, 3, 2, 4], 106),
  (1, [5, 6, 4, 0, 2, 1, 3], 0), (1, [5, 6, 4, 0, 2, 1, 3], 127), (1, [5, 6, 4, 2, 3, 0, 1], 33),
  (1, [5, 6, 4, 2, 3, 0, 1], 61), (1, [5, 6, 4, 2, 3, 0, 1], 66), (1, [5, 6, 4, 2, 3, 0, 1], 94),
  (1, [6, 0, 1, 5, 3, 4, 2], 5), (1, [6, 0, 1, 5, 3, 4, 2], 61), (1, [6, 0, 1, 5, 3, 4, 2], 66),
  (1, [6, 0, 1, 5, 3, 4, 2], 122), (1, [6, 0, 4, 2, 3, 1, 5], 33), (1, [6, 0, 4, 2, 3, 1, 5], 61),
  (1, [6, 0, 4, 2, 3, 1, 5], 66), (1, [6, 0, 4, 2, 3, 1, 5], 94), (1, [6, 0, 4, 5, 2, 3, 1], 20),
  (1, [6, 0, 4, 5, 2, 3, 1], 40), (1, [6, 0, 4, 5, 2, 3, 1], 87), (1, [6, 0, 4, 5, 2, 3, 1], 107),
  (1, [6, 0, 4, 5, 3, 1, 2], 33), (1, [6, 0, 4, 5, 3, 1, 2], 61), (1, [6, 0, 4, 5, 3, 1, 2], 66),
  (1, [6, 0, 4, 5, 3, 1, 2], 94), (1, [6, 0, 5, 2, 3, 4, 1], 20), (1, [6, 0, 5, 2, 3, 4, 1], 40),
  (1, [6, 0, 5, 2, 3, 4, 1], 87), (1, [6, 0, 5, 2, 3, 4, 1], 107), (1, [6, 3, 1, 2, 0, 4, 5], 33),
  (1, [6, 3, 1, 2, 0, 4, 5], 47), (1, [6, 3, 1, 2, 0, 4, 5], 80), (1, [6, 3, 1, 2, 0, 4, 5], 94),
  (1, [6, 3, 4, 1, 2, 0, 5], 10), (1, [6, 3, 4, 1, 2, 0, 5], 20), (1, [6, 3, 4, 1, 2, 0, 5], 107),
  (1, [6, 3, 4, 1, 2, 0, 5], 117), (1, [6, 3, 4, 2, 0, 1, 5], 33), (1, [6, 3, 4, 2, 0, 1, 5], 47),
  (1, [6, 3, 4, 2, 0, 1, 5], 80), (1, [6, 3, 4, 2, 0, 1, 5], 94), (1, [6, 3, 4, 5, 2, 0, 1], 10),
  (1, [6, 3, 4, 5, 2, 0, 1], 20), (1, [6, 3, 4, 5, 2, 0, 1], 107), (1, [6, 3, 4, 5, 2, 0, 1], 117),
  (1, [6, 3, 5, 0, 1, 2, 4], 19), (1, [6, 3, 5, 0, 1, 2, 4], 108), (1, [6, 3, 5, 0, 2, 1, 4], 33),
  (1, [6, 3, 5, 0, 2, 1, 4], 94), (1, [6, 3, 5, 1, 0, 2, 4], 10), (1, [6, 3, 5, 1, 0, 2, 4], 117),
  (1, [6, 4, 0, 5, 1, 2, 3], 41), (1, [6, 4, 0, 5, 1, 2, 3], 86), (1, [6, 4, 0, 5, 1, 3, 2], 40),
  (1, [6, 4, 0, 5, 1, 3, 2], 87), (1, [6, 4, 0, 5, 2, 1, 3], 33), (1, [6, 4, 0, 5, 2, 1, 3], 94),
  (1, [6, 4, 1, 2, 3, 0, 5], 10), (1, [6, 4, 1, 2, 3, 0, 5], 20), (1, [6, 4, 1, 2, 3, 0, 5], 107),
  (1, [6, 4, 1, 2, 3, 0, 5], 117), (1, [6, 4, 5, 0, 2, 1, 3], 0), (1, [6, 4, 5, 0, 2, 1, 3], 127),
  (1, [6, 4, 5, 2, 3, 0, 1], 10), (1, [6, 4, 5, 2, 3, 0, 1], 20), (1, [6, 4, 5, 2, 3, 0, 1], 107),
  (1, [6, 4, 5, 2, 3, 0, 1], 117), (1, [6, 5, 0, 1, 2, 4, 3], 41), (1, [6, 5, 0, 1, 2, 4, 3], 86),
  (1, [6, 5, 0, 2, 1, 4, 3], 9), (1, [6, 5, 0, 2, 1, 4, 3], 118), (1, [6, 5, 1, 0, 2, 3, 4], 37),
  (1, [6, 5, 1, 0, 2, 3, 4], 90), (1, [6, 5, 1, 0, 2, 4, 3], 36), (1, [6, 5, 1, 0, 2, 4, 3], 91),
  (1, [6, 5, 1, 0, 3, 2, 4], 17), (1, [6, 5, 1, 0, 3, 2, 4], 110), (1, [6, 5, 4, 0, 1, 2, 3], 0),
  (1, [6, 5, 4, 0, 1, 2, 3], 127), (1, [6, 5, 4, 0, 2, 1, 3], 0), (1, [6, 5, 4, 0, 2, 1, 3], 127)
  ]

def censo6 : List (ℕ × List ℕ × ℕ) := censo6a ++ censo6b

def censo7 : List (ℕ × List ℕ × ℕ) :=
    censo7a ++
    censo7b ++
    censo7c ++
    censo7d ++
    censo7e ++
    censo7f

theorem all_censo6a : censo6a.all (passes 6) = true := by decide +kernel

theorem all_censo6b : censo6b.all (passes 6) = true := by decide +kernel

theorem all_censo7a : censo7a.all (passes 7) = true := by decide +kernel

theorem all_censo7b : censo7b.all (passes 7) = true := by decide +kernel

theorem all_censo7c : censo7c.all (passes 7) = true := by decide +kernel

theorem all_censo7d : censo7d.all (passes 7) = true := by decide +kernel

theorem all_censo7e : censo7e.all (passes 7) = true := by decide +kernel

theorem all_censo7f : censo7f.all (passes 7) = true := by decide +kernel

theorem censo6_length : censo6.length = 168 := by decide +kernel

theorem censo7_length : censo7.length = 676 := by decide +kernel

theorem censo6_nodup : censo6.Nodup := by decide +kernel

theorem censo7_nodup : censo7.Nodup := by decide +kernel

theorem censo6_passes : ∀ d ∈ censo6, passes 6 d = true := by
  intro d hd
  simp only [censo6, List.mem_append] at hd
  rcases hd with hd | hd
  · exact List.all_eq_true.1 all_censo6a d hd
  · exact List.all_eq_true.1 all_censo6b d hd

theorem censo7_passes : ∀ d ∈ censo7, passes 7 d = true := by
  intro d hd
  simp only [censo7, List.mem_append] at hd
  rcases hd with ((((hd | hd) | hd) | hd) | hd) | hd
  · exact List.all_eq_true.1 all_censo7a d hd
  · exact List.all_eq_true.1 all_censo7b d hd
  · exact List.all_eq_true.1 all_censo7c d hd
  · exact List.all_eq_true.1 all_censo7d d hd
  · exact List.all_eq_true.1 all_censo7e d hd
  · exact List.all_eq_true.1 all_censo7f d hd

end TMENudos.Puente

#print axioms TMENudos.Puente.pasan_3
#print axioms TMENudos.Puente.pasan_4
#print axioms TMENudos.Puente.pasan_5
#print axioms TMENudos.Puente.censo6_passes
#print axioms TMENudos.Puente.censo7_passes
