/- MODELO VIGENTE (2026-09-30). Sustituye a 06_modelo_de_consistencia.lean (34 axiomas, que queda como registro histórico). Copia de aquel con una extensión al final del namespace Model: los axiomas jones2, jones2_connected_sum, jones2_trefoil y jones2_mirror_trefoil que la Opción 1 añadió a Schubert.lean (ver Procesos/20260929_2247_diseno_integracion_knot.md), y la derivación de granny_distinct_from_square a partir de ellos. Cubre los 38 axiomas actuales de Reidemeister (11), Schubert (25) y Bridge (2); su fidelidad se comprueba comparando el volcado de tipos de esta sección final con el de 06e_tipos_originales.lean. -/
/- MODELO DE CONSISTENCIA RELATIVA (2026-09-29).
Interpretación concreta (namespace `Model`) de los 34 axiomas de Reidemeister.lean (11), Schubert.lean (21) y
Bridge.lean (2), en la que todos valen como teoremas (o son definiciones del tipo declarado). Solo depende de
propext, Classical.choice y Quot.sound (ver `#print axioms` al final). Solo importa TMENudos.Basic (para
`RationalConfiguration`), no Reidemeister ni Schubert.

IDEA. `apply_R1/R2` (sorry en el original) se definen: agregar = añadir cruces de razón 0 (posiciones antiguas
por castSucc); quitar = retirar el último cruce retrayendo posiciones. `apply_R3` = involución dentro de la fibra
{K' | inv K' = inv K} usando una enumeración sobreyectiva de la fibra (dependiente solo de (n, inv K)).
Invariante `inv K` = multiconjunto de razones no nulas. Teorema clave `equiv_iff_inv`:
  reidemeister_equivalent K₁ K₂ ↔ inv K₁ = inv K₂.
Luego `Knot` se incrusta inyectivamente en `Multiset ℚ` (`Finv`, `Finv_inj`) con sección `S`; Schubert se
transporta: # = suma de multiconjuntos, unknot ↦ 0, primos = singletones (`is_prime_iff`), trefoil = {1},
figure_eight = {2}, cinquefoil = {3}, mirror = negar razones; el resto de constantes son triviales.

TABLA (axioma original -> objeto del modelo; d = def, t = theorem)
 Reidemeister: topologically_equivalent d | topo_equiv_refl/symm/trans t | R1/R2/R3_preserves_isotopy t
               R1_inverse, R2_inverse, R3_inverse t | reidemeister_completeness t   (mismo nombre en `Model`)
 Schubert:     connected_sum d | connected_sum_comm/assoc/unknot t | trefoil, figure_eight, cinquefoil d
               trefoil_is_prime, figure_eight_is_prime t | schubert_existence_axiom t | schubert_uniqueness t
               knot_genus, bridge_number, knot_complement, knot_group, manifold_connected_sum d
               knot_primality_in_NP t | mirror, alexander_polynomial, ThreeManifold, JSJ_decomposition d
 Bridge:       rational_to_diagram d | rational_equivalence_preserves_isotopy t
FIDELIDAD: la sección final vuelca tipos/valores; `06e_tipos_originales.lean` vuelca los originales. Comparación:
  lake env lean 06_modelo...lean | grep '^TYPE\|^VALUE' | sort  vs  lake env lean 06e...lean | grep ... | sort
(diff vacío al momento de escribir, tras quitar prefijos de namespace).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Topology.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import TMENudos.Basic

namespace Model

/-! ## Copia fiel de las definiciones no axiomáticas de Reidemeister.lean -/

structure Crossing (n : ℕ) where
  over_pos : Fin n
  under_pos : Fin n
  ratio_val : ℚ
  deriving DecidableEq

structure KnotConfig (n : ℕ) : Type 0 where
  crossings : Fin n → Crossing n
  deriving DecidableEq

structure Strand where
  start_pos : ℕ
  end_pos : ℕ
  deriving DecidableEq

inductive CrossingSign
  | Positive
  | Negative
  deriving DecidableEq, Repr

structure R1Move where
  strand : Strand
  sign : CrossingSign
  add_twist : Bool
  deriving DecidableEq

structure R2Move where
  strand1 : Strand
  strand2 : Strand
  adjacent : Bool
  add_crossings : Bool
  deriving DecidableEq

structure R3Move where
  strand : Strand
  crossing1 : ℕ
  crossing2 : ℕ
  triangle_config : Bool
  deriving DecidableEq

/-! ## Modelo: invariante y movimientos -/

/-- Invariante: multiconjunto de razones no nulas. -/
def inv {n : ℕ} (K : KnotConfig n) : Multiset ℚ :=
  Multiset.filter (· ≠ 0) (↑(List.ofFn fun i => (K.crossings i).ratio_val) : Multiset ℚ)

/-- Añade un cruce de razón 0 (posiciones antiguas via castSucc). -/
def growOne {n : ℕ} (K : KnotConfig n) : KnotConfig (n + 1) where
  crossings i :=
    if h : i.val < n then
      ⟨(K.crossings ⟨i.val, h⟩).over_pos.castSucc, (K.crossings ⟨i.val, h⟩).under_pos.castSucc,
        (K.crossings ⟨i.val, h⟩).ratio_val⟩
    else ⟨0, 0, 0⟩

/-- Retracción de posiciones a `Fin (n-1)`. -/
def retr {n : ℕ} (p : Fin n) (j : Fin (n - 1)) : Fin (n - 1) :=
  if h : p.val < n - 1 then ⟨p.val, h⟩ else ⟨0, j.pos⟩

/-- Quita el último cruce. -/
def shrinkOne {n : ℕ} (K : KnotConfig n) : KnotConfig (n - 1) where
  crossings j :=
    let c := K.crossings ⟨j.val, by have := j.isLt; omega⟩
    ⟨retr c.over_pos j, retr c.under_pos j, c.ratio_val⟩

def R1aux {n : ℕ} : (b : Bool) → KnotConfig n → KnotConfig (if b then n + 1 else n - 1)
  | true, K => growOne K
  | false, K => shrinkOne K

def R2aux {n : ℕ} : (b : Bool) → KnotConfig n → KnotConfig (if b then n + 2 else n - 2)
  | true, K => growOne (growOne K)
  | false, K => shrinkOne (shrinkOne K)

noncomputable def apply_R1 {n : ℕ} (K : KnotConfig n) (move : R1Move) :
    KnotConfig (if move.add_twist then n + 1 else n - 1) :=
  R1aux move.add_twist K

noncomputable def apply_R2 {n : ℕ} (K : KnotConfig n) (move : R2Move) :
    KnotConfig (if move.add_crossings then n + 2 else n - 2) :=
  R2aux move.add_crossings K

instance (n : ℕ) : Countable (KnotConfig n) := by
  refine Function.Injective.countable
    (f := fun K : KnotConfig n => List.ofFn fun i =>
      ((K.crossings i).over_pos, (K.crossings i).under_pos, (K.crossings i).ratio_val)) ?_
  intro K L h
  have h1 := List.ofFn_injective h
  have key : ∀ x y : Crossing n,
      (x.over_pos, x.under_pos, x.ratio_val) = (y.over_pos, y.under_pos, y.ratio_val) → x = y := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simpa using h
  obtain ⟨cK⟩ := K
  obtain ⟨cL⟩ := L
  congr 1
  funext i
  exact key _ _ (congrFun h1 i)

open Classical in
noncomputable def enumM (n : ℕ) (m : Multiset ℚ) : ℕ → KnotConfig n :=
  if h : ∃ K : KnotConfig n, inv K = m then
    haveI : Nonempty {K : KnotConfig n // inv K = m} :=
      ⟨⟨h.choose, h.choose_spec⟩⟩
    fun a => (Classical.choose (exists_surjective_nat {K : KnotConfig n // inv K = m}) a).1
  else fun _ => ⟨fun i => ⟨i, i, 0⟩⟩

theorem enumM_inv {n : ℕ} (m : Multiset ℚ) (h : ∃ K : KnotConfig n, inv K = m) (a : ℕ) :
    inv (enumM n m a) = m := by
  haveI : Nonempty {K : KnotConfig n // inv K = m} := ⟨⟨h.choose, h.choose_spec⟩⟩
  unfold enumM
  rw [dif_pos h]
  exact (Classical.choose (exists_surjective_nat {K : KnotConfig n // inv K = m}) a).2

theorem enumM_surj {n : ℕ} (K : KnotConfig n) : ∃ a, enumM n (inv K) a = K := by
  have h : ∃ K' : KnotConfig n, inv K' = inv K := ⟨K, rfl⟩
  haveI : Nonempty {K' : KnotConfig n // inv K' = inv K} := ⟨⟨K, rfl⟩⟩
  have hs := Classical.choose_spec (exists_surjective_nat {K' : KnotConfig n // inv K' = inv K})
  obtain ⟨a, ha⟩ := hs ⟨K, rfl⟩
  refine ⟨a, ?_⟩
  unfold enumM
  rw [dif_pos h]
  exact congrArg Subtype.val ha

noncomputable def apply_R3 {n : ℕ} (K : KnotConfig n) (move : R3Move) : KnotConfig n :=
  if K = enumM n (inv K) move.crossing1 then enumM n (inv K) move.crossing2
  else if K = enumM n (inv K) move.crossing2 then enumM n (inv K) move.crossing1
  else K

theorem inv_R3 {n : ℕ} (K : KnotConfig n) (move : R3Move) : inv (apply_R3 K move) = inv K := by
  have h : ∃ K' : KnotConfig n, inv K' = inv K := ⟨K, rfl⟩
  unfold apply_R3
  split_ifs
  · exact enumM_inv _ h _
  · exact enumM_inv _ h _
  · rfl


/-! ## Relación de equivalencia (copia literal) -/

inductive reidemeister_equivalent : {n m : ℕ} → KnotConfig n → KnotConfig m → Prop where
  | refl {n : ℕ} (K : KnotConfig n) : reidemeister_equivalent K K
  | symm {n m : ℕ} {K₁ : KnotConfig n} {K₂ : KnotConfig m} :
      reidemeister_equivalent K₁ K₂ → reidemeister_equivalent K₂ K₁
  | trans {n m p : ℕ} {K₁ : KnotConfig n} {K₂ : KnotConfig m} {K₃ : KnotConfig p} :
      reidemeister_equivalent K₁ K₂ → reidemeister_equivalent K₂ K₃ →
      reidemeister_equivalent K₁ K₃
  | R1 {n : ℕ} (K : KnotConfig n) (move : R1Move) :
      move.add_twist = true → reidemeister_equivalent K (apply_R1 K move)
  | R2 {n : ℕ} (K : KnotConfig n) (move : R2Move) :
      move.add_crossings = true → reidemeister_equivalent K (apply_R2 K move)
  | R3 {n : ℕ} (K : KnotConfig n) (move : R3Move) :
      reidemeister_equivalent K (apply_R3 K move)

/-! ## Lemas del modelo -/

theorem inv_grow {n : ℕ} (K : KnotConfig n) : inv (growOne K) = inv K := by
  unfold inv
  have : (List.ofFn fun i : Fin (n + 1) => ((growOne K).crossings i).ratio_val) =
      (List.ofFn fun i : Fin n => (K.crossings i).ratio_val) ++ [0] := by
    rw [List.ofFn_succ']
    simp [growOne, List.concat_eq_append]
  rw [this]
  simp

theorem shrink_grow {n : ℕ} (K : KnotConfig n) : shrinkOne (growOne K) = K := by
  cases K with
  | mk cr =>
    have key : ∀ j : Fin n, (shrinkOne (growOne (KnotConfig.mk cr))).crossings j = cr j := by
      intro j
      have hj : j.val < n := j.isLt
      have ho : (cr j).over_pos.val < n := (cr j).over_pos.isLt
      have hu : (cr j).under_pos.val < n := (cr j).under_pos.isLt
      simp [shrinkOne, growOne, retr, hj, ho, hu, Crossing.mk.injEq, Fin.ext_iff]
    show KnotConfig.mk _ = KnotConfig.mk cr
    congr 1
    funext j
    exact key j

theorem inv_R1 {n : ℕ} (K : KnotConfig n) (move : R1Move) (h : move.add_twist = true) :
    inv (apply_R1 K move) = inv K := by
  obtain ⟨s, sg, b⟩ := move
  simp only at h
  subst h
  exact inv_grow K

theorem inv_R2 {n : ℕ} (K : KnotConfig n) (move : R2Move) (h : move.add_crossings = true) :
    inv (apply_R2 K move) = inv K := by
  obtain ⟨s1, s2, a, b⟩ := move
  simp only at h
  subst h
  exact (inv_grow (growOne K)).trans (inv_grow K)

theorem equiv_imp_inv {n m : ℕ} {K₁ : KnotConfig n} {K₂ : KnotConfig m}
    (h : reidemeister_equivalent K₁ K₂) : inv K₁ = inv K₂ := by
  induction h with
  | refl K => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | R1 K move hmove => exact (inv_R1 K move hmove).symm
  | R2 K move hmove => exact (inv_R2 K move hmove).symm
  | R3 K move => exact (inv_R3 K move).symm

theorem inv_imp_equiv_same {n : ℕ} (K K₂ : KnotConfig n) (h : inv K = inv K₂) :
    reidemeister_equivalent K K₂ := by
  obtain ⟨a, ha⟩ := enumM_surj K
  obtain ⟨b, hb⟩ := enumM_surj K₂
  rw [← h] at hb
  let move : R3Move := ⟨⟨0, 0⟩, a, b, true⟩
  have hm : apply_R3 K move = K₂ := by
    unfold apply_R3
    simp only [move]
    rw [if_pos ha.symm]
    exact hb
  have := reidemeister_equivalent.R3 K move
  rwa [hm] at this

theorem inv_imp_equiv_aux : ∀ (d n m : ℕ) (_ : n + d = m) (K : KnotConfig n) (K₂ : KnotConfig m),
    inv K = inv K₂ → reidemeister_equivalent K K₂ := by
  intro d
  induction d with
  | zero =>
    intro n m hd K K₂ h
    obtain rfl : n = m := by omega
    exact inv_imp_equiv_same K K₂ h
  | succ d ih =>
    intro n m hd K K₂ h
    let move : R1Move := ⟨⟨0, 0⟩, CrossingSign.Positive, true⟩
    have h1 : reidemeister_equivalent K (growOne K) :=
      reidemeister_equivalent.R1 K move rfl
    have h2 := ih (n + 1) m (by omega) (growOne K) K₂ ((inv_grow K).trans h)
    exact h1.trans h2

theorem equiv_iff_inv {n m : ℕ} (K₁ : KnotConfig n) (K₂ : KnotConfig m) :
    reidemeister_equivalent K₁ K₂ ↔ inv K₁ = inv K₂ := by
  refine ⟨equiv_imp_inv, fun h => ?_⟩
  rcases le_total n m with hnm | hmn
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
    exact inv_imp_equiv_aux d n m hd.symm K₁ K₂ h
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
    exact (inv_imp_equiv_aux d m n hd.symm K₂ K₁ h.symm).symm

/-! ## Propiedades R1/R2/R3 inverse -/

theorem R1_inverse {n : ℕ} (K : KnotConfig n) (move : R1Move)
    (h : move.add_twist = true) :
    let move_inv : R1Move := { move with add_twist := !move.add_twist }
    HEq (apply_R1 (apply_R1 K move) move_inv) K := by
  obtain ⟨s, sg, b⟩ := move
  simp only at h
  subst h
  intro move_inv
  exact heq_of_eq (shrink_grow K)

theorem R2_inverse {n : ℕ} (K : KnotConfig n) (move : R2Move)
    (h : move.add_crossings = true) :
    let move_inv : R2Move := { move with add_crossings := !move.add_crossings }
    HEq (apply_R2 (apply_R2 K move) move_inv) K := by
  obtain ⟨s1, s2, a, b⟩ := move
  simp only at h
  subst h
  intro move_inv
  refine heq_of_eq ?_
  show shrinkOne (shrinkOne (growOne (growOne K))) = K
  exact (congrArg (fun X => shrinkOne X) (shrink_grow (growOne K))).trans (shrink_grow K)

theorem apply_R3_of_inv {n : ℕ} (K K' : KnotConfig n) (move : R3Move) (h : inv K' = inv K) :
    apply_R3 K' move =
      if K' = enumM n (inv K) move.crossing1 then enumM n (inv K) move.crossing2
      else if K' = enumM n (inv K) move.crossing2 then enumM n (inv K) move.crossing1
      else K' := by
  unfold apply_R3; rw [h]

theorem R3_inverse {n : ℕ} (K : KnotConfig n) (move : R3Move) :
    apply_R3 (apply_R3 K move) move = K := by
  rw [apply_R3_of_inv K (apply_R3 K move) move (inv_R3 K move)]
  have e := apply_R3_of_inv K K move rfl
  by_cases hc1 : K = enumM n (inv K) move.crossing1
  · have a1 : apply_R3 K move = enumM n (inv K) move.crossing2 := by rw [e, if_pos hc1]
    rw [a1]
    by_cases h21 : enumM n (inv K) move.crossing2 = enumM n (inv K) move.crossing1
    · rw [if_pos h21, h21]; exact hc1.symm
    · rw [if_neg h21, if_pos rfl]; exact hc1.symm
  · by_cases hc2 : K = enumM n (inv K) move.crossing2
    · have a2 : apply_R3 K move = enumM n (inv K) move.crossing1 := by
        rw [e, if_neg hc1, if_pos hc2]
      rw [a2, if_pos rfl]; exact hc2.symm
    · have a3 : apply_R3 K move = K := by rw [e, if_neg hc1, if_neg hc2]
      rw [a3, if_neg hc1, if_neg hc2]


theorem perm_get_equiv {α : Type*} {l l' : List α} (h : l.Perm l') :
    ∃ σ : Fin l.length ≃ Fin l'.length, ∀ i, l.get i = l'.get (σ i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => i.elim0⟩
  | @cons x l₁ l₂ _ ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr σ).trans (finSuccEquiv _).symm), fun i => ?_⟩
    cases i using Fin.cases with
    | zero =>
      have e : ((finSuccEquiv _).trans ((Equiv.optionCongr σ).trans (finSuccEquiv _).symm)) 0 = 0 := by
        simp [Equiv.trans_apply]
      exact (congrArg (fun t => (x :: l₂).get t) e).symm
    | succ j => simpa using hσ j
  | swap x y l =>
    refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, fun i => ?_⟩
    cases i using Fin.cases with
    | zero =>
      have e : Equiv.swap (0 : Fin (l.length + 2)) 1 0 = 1 := Equiv.swap_apply_left _ _
      exact (congrArg (fun t => (x :: y :: l).get t) e).symm
    | succ j =>
      cases j using Fin.cases with
      | zero =>
        have e : Equiv.swap (0 : Fin (l.length + 2)) 1 (Fin.succ 0) = 0 := Equiv.swap_apply_right _ _
        exact (congrArg (fun t => (x :: y :: l).get t) e).symm
      | succ k =>
        have h0 : (Fin.succ (Fin.succ k) : Fin (l.length + 2)) ≠ 0 := Fin.succ_ne_zero _
        have h1 : (Fin.succ (Fin.succ k) : Fin (l.length + 2)) ≠ 1 := by
          intro h; have := Fin.succ_injective _ (h.trans (Fin.succ_zero_eq_one).symm); exact Fin.succ_ne_zero _ this
        have e : Equiv.swap (0 : Fin (l.length + 2)) 1 (Fin.succ (Fin.succ k)) = Fin.succ (Fin.succ k) :=
          Equiv.swap_apply_of_ne_of_ne h0 h1
        exact (congrArg (fun t => (x :: y :: l).get t) e).symm
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ, hσ⟩ := ih1
    obtain ⟨τ, hτ⟩ := ih2
    exact ⟨σ.trans τ, fun i => (hσ i).trans (hτ (σ i))⟩

/-! ## Reidemeister.lean: los 11 axiomas como definición / teoremas del modelo -/

/-- (axioma `topologically_equivalent`) interpretado como la equivalencia de Reidemeister. -/
def topologically_equivalent {n m : ℕ} : KnotConfig n → KnotConfig m → Prop :=
  reidemeister_equivalent

theorem topo_equiv_refl {n : ℕ} (K : KnotConfig n) :
    topologically_equivalent K K :=
  reidemeister_equivalent.refl K

theorem topo_equiv_symm {n m : ℕ} {K₁ : KnotConfig n} {K₂ : KnotConfig m} :
    topologically_equivalent K₁ K₂ → topologically_equivalent K₂ K₁ :=
  reidemeister_equivalent.symm

theorem topo_equiv_trans {n m p : ℕ}
    {K₁ : KnotConfig n} {K₂ : KnotConfig m} {K₃ : KnotConfig p} :
    topologically_equivalent K₁ K₂ →
    topologically_equivalent K₂ K₃ →
    topologically_equivalent K₁ K₃ :=
  reidemeister_equivalent.trans

theorem R1_preserves_isotopy {n : ℕ} (K : KnotConfig n) (move : R1Move) :
    move.add_twist = true → topologically_equivalent K (apply_R1 K move) :=
  reidemeister_equivalent.R1 K move

theorem R2_preserves_isotopy {n : ℕ} (K : KnotConfig n) (move : R2Move) :
    move.add_crossings = true → topologically_equivalent K (apply_R2 K move) :=
  reidemeister_equivalent.R2 K move

theorem R3_preserves_isotopy {n : ℕ} (K : KnotConfig n) (move : R3Move) :
    topologically_equivalent K (apply_R3 K move) :=
  reidemeister_equivalent.R3 K move

theorem reidemeister_completeness {n m : ℕ}
    (K₁ : KnotConfig n) (K₂ : KnotConfig m) :
    topologically_equivalent K₁ K₂ → reidemeister_equivalent K₁ K₂ :=
  id

/-! ## Diagram, Knot (copia literal de Reidemeister.lean / Schubert.lean) -/

structure Diagram where
  n : ℕ
  config : KnotConfig n

def diagram_equiv (d1 d2 : Diagram) : Prop :=
  reidemeister_equivalent d1.config d2.config

theorem diagram_equiv_refl (d : Diagram) : diagram_equiv d d :=
  reidemeister_equivalent.refl d.config

theorem diagram_equiv_symm {d1 d2 : Diagram} : diagram_equiv d1 d2 → diagram_equiv d2 d1 :=
  reidemeister_equivalent.symm

theorem diagram_equiv_trans {d1 d2 d3 : Diagram} :
    diagram_equiv d1 d2 → diagram_equiv d2 d3 → diagram_equiv d1 d3 :=
  reidemeister_equivalent.trans

instance DiagramSetoid : Setoid Diagram where
  r := diagram_equiv
  iseqv := { refl := diagram_equiv_refl, symm := diagram_equiv_symm, trans := diagram_equiv_trans }

def Knot := Quotient DiagramSetoid

def knot_isotopic (K₁ K₂ : Knot) : Prop := K₁ = K₂

infix:50 " ≅ " => knot_isotopic

noncomputable def unknot : Knot :=
  Quotient.mk DiagramSetoid { n := 0, config := { crossings := fun x => x.elim0 } }

/-! ## Transporte: Knot ↪ Multiset ℚ (inyectivo) y sección -/

/-- Invariante completo de `Knot`: el multiconjunto de razones no nulas. -/
noncomputable def Finv : Knot → Multiset ℚ :=
  Quotient.lift (s := DiagramSetoid) (fun d => inv d.config)
    (fun _ _ h => equiv_imp_inv (h : reidemeister_equivalent _ _))

theorem Finv_mk (d : Diagram) : Finv (Quotient.mk DiagramSetoid d) = inv d.config := rfl

theorem Finv_inj : Function.Injective Finv := by
  intro K L h
  obtain ⟨a, rfl⟩ := Quotient.exists_rep (s := DiagramSetoid) K
  obtain ⟨b, rfl⟩ := Quotient.exists_rep (s := DiagramSetoid) L
  exact Quotient.sound ((equiv_iff_inv a.config b.config).2 h)

theorem Finv_nz (K : Knot) : ∀ x ∈ Finv K, x ≠ 0 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep (s := DiagramSetoid) K
  intro x hx
  exact (Multiset.mem_filter.mp (show x ∈ inv a.config from hx)).2

theorem Finv_unknot : Finv unknot = 0 := rfl

def diagOfList (l : List ℚ) : Diagram := ⟨l.length, ⟨fun i => ⟨i, i, l.get i⟩⟩⟩

/-- Sección: cualquier multiconjunto (filtrando ceros) se realiza como nudo. -/
noncomputable def S (m : Multiset ℚ) : Knot :=
  Quotient.mk DiagramSetoid (diagOfList m.toList)

theorem Finv_S (m : Multiset ℚ) : Finv (S m) = m.filter (· ≠ 0) := by
  show inv (diagOfList m.toList).config = _
  unfold inv diagOfList
  have h : (List.ofFn fun i : Fin m.toList.length => m.toList[i.val]) = m.toList := List.ofFn_getElem
  conv_rhs => rw [← Multiset.coe_toList m]
  simp [Multiset.filter_coe]
  refine List.Perm.of_eq (congrArg _ ?_)
  apply List.ext_getElem <;> simp

theorem Finv_S_nz (m : Multiset ℚ) (h : ∀ x ∈ m, x ≠ 0) : Finv (S m) = m := by
  rw [Finv_S]; exact Multiset.filter_eq_self.mpr h

theorem Finv_S_single (q : ℚ) (hq : q ≠ 0) : Finv (S {q}) = {q} :=
  Finv_S_nz _ (by simpa using hq)

theorem S_Finv (K : Knot) : S (Finv K) = K :=
  Finv_inj (Finv_S_nz _ (Finv_nz K))

/-! ## Schubert.lean: los 21 axiomas -/

/-- (axioma `connected_sum`) suma de multiconjuntos. -/
noncomputable def connected_sum : Knot → Knot → Knot :=
  fun K₁ K₂ => S (Finv K₁ + Finv K₂)

infixl:65 " # " => connected_sum

theorem Finv_cs (K₁ K₂ : Knot) : Finv (K₁ # K₂) = Finv K₁ + Finv K₂ := by
  apply Finv_S_nz
  intro x hx
  rcases Multiset.mem_add.mp hx with h | h
  · exact Finv_nz K₁ x h
  · exact Finv_nz K₂ x h

def is_prime (K : Knot) : Prop :=
  K ≠ unknot ∧
  ∀ K₁ K₂ : Knot, K ≅ connected_sum K₁ K₂ → (K₁ ≅ unknot ∨ K₂ ≅ unknot)

theorem connected_sum_comm (K₁ K₂ : Knot) : K₁ # K₂ ≅ K₂ # K₁ := by
  show K₁ # K₂ = K₂ # K₁
  apply Finv_inj
  rw [Finv_cs, Finv_cs, add_comm]

theorem connected_sum_assoc (K₁ K₂ K₃ : Knot) :
    (K₁ # K₂) # K₃ ≅ K₁ # (K₂ # K₃) := by
  show (K₁ # K₂) # K₃ = K₁ # (K₂ # K₃)
  apply Finv_inj
  rw [Finv_cs, Finv_cs, Finv_cs, Finv_cs, add_assoc]

theorem connected_sum_unknot (K : Knot) : K # unknot ≅ K := by
  show K # unknot = K
  apply Finv_inj
  rw [Finv_cs, Finv_unknot, add_zero]

noncomputable def trefoil : Knot := S {1}
noncomputable def figure_eight : Knot := S {2}
noncomputable def cinquefoil : Knot := S {3}

theorem is_prime_iff (K : Knot) : is_prime K ↔ Multiset.card (Finv K) = 1 := by
  constructor
  · rintro ⟨hne, hp⟩
    have hc0 : Multiset.card (Finv K) ≠ 0 := by
      intro h0
      apply hne
      apply Finv_inj
      rw [Finv_unknot]
      exact Multiset.card_eq_zero.mp h0
    by_contra hc1
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card (Finv K))
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
    have hcard : Multiset.card t + 1 = Multiset.card (Finv K) := by
      rw [ht, Multiset.card_cons]
    have hta : ∀ x ∈ t, x ≠ 0 := fun x hx =>
      Finv_nz K x (by rw [ht]; exact Multiset.mem_cons_of_mem hx)
    have ha0 : a ≠ 0 := Finv_nz K a ha
    have hK : K ≅ S {a} # S t := by
      show K = S {a} # S t
      apply Finv_inj
      rw [Finv_cs, Finv_S_single a ha0, Finv_S_nz t hta, Multiset.singleton_add, ← ht]
    rcases hp _ _ hK with h | h
    · have := congrArg Finv (h : S {a} = unknot)
      rw [Finv_S_single a ha0, Finv_unknot] at this
      exact Multiset.singleton_ne_zero a this
    · have := congrArg Finv (h : S t = unknot)
      rw [Finv_S_nz t hta, Finv_unknot] at this
      subst this
      simp at hcard
      omega
  · intro hc
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg Finv h
      rw [Finv_unknot] at this
      rw [this] at hc
      simp at hc
    · intro K₁ K₂ hK
      have h := congrArg Finv (hK : K = K₁ # K₂)
      rw [Finv_cs] at h
      have hcd := congrArg Multiset.card h
      rw [hc, Multiset.card_add] at hcd
      have : Multiset.card (Finv K₁) = 0 ∨ Multiset.card (Finv K₂) = 0 := by omega
      rcases this with h0 | h0
      · left
        show K₁ = unknot
        apply Finv_inj
        rw [Finv_unknot]
        exact Multiset.card_eq_zero.mp h0
      · right
        show K₂ = unknot
        apply Finv_inj
        rw [Finv_unknot]
        exact Multiset.card_eq_zero.mp h0

theorem trefoil_is_prime : is_prime trefoil := by
  rw [is_prime_iff]; unfold trefoil; rw [Finv_S_single 1 one_ne_zero]; simp

theorem figure_eight_is_prime : is_prime figure_eight := by
  rw [is_prime_iff]; unfold figure_eight; rw [Finv_S_single 2 two_ne_zero]; simp

theorem Finv_foldl (l : List Knot) (k : Knot) :
    Finv (l.foldl (· # ·) k) = Finv k + (l.map Finv).sum := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, Finv_cs, List.map_cons, List.sum_cons, add_assoc]

theorem schubert_existence_axiom (K : Knot) :
    ∃ primes : List Knot,
      (∀ P ∈ primes, is_prime P) ∧ K ≅ primes.foldl (· # ·) unknot := by
  refine ⟨(Finv K).toList.map (fun q => S {q}), ?_, ?_⟩
  · intro P hP
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hP
    have hq' : q ≠ 0 := Finv_nz K q (Multiset.mem_toList.mp hq)
    rw [is_prime_iff, Finv_S_single q hq']
    simp
  · show K = _
    apply Finv_inj
    rw [Finv_foldl, Finv_unknot, zero_add, List.map_map]
    have hc : (Finv K).toList.map (Finv ∘ fun q => S {q}) =
        (Finv K).toList.map (fun q => ({q} : Multiset ℚ)) := by
      apply List.map_congr_left
      intro q hq
      exact Finv_S_single q (Finv_nz K q (Multiset.mem_toList.mp hq))
    rw [hc]
    have := Multiset.sum_map_singleton (Finv K)
    conv_lhs at this => rw [← Multiset.coe_toList (Finv K)]
    rw [Multiset.map_coe, Multiset.sum_coe] at this
    exact this.symm

/-- Etiqueta racional de un nudo primo (su único elemento). -/
noncomputable def phi (P : Knot) : ℚ := (Finv P).sum

theorem Finv_prime (P : Knot) (h : is_prime P) : Finv P = {phi P} := by
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp ((is_prime_iff P).mp h)
  unfold phi
  rw [ha]; simp

theorem Finv_foldl_primes (l : List Knot) (h : ∀ P ∈ l, is_prime P) :
    (l.map Finv).sum = ((l.map phi : List ℚ) : Multiset ℚ) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun P hP => h P (List.mem_cons_of_mem _ hP)),
      Finv_prime x (h x (by simp)), List.map_cons, Multiset.singleton_add, Multiset.cons_coe]

theorem schubert_uniqueness (K : Knot)
    (primes₁ primes₂ : List Knot)
    (h₁ : ∀ P ∈ primes₁, is_prime P)
    (h₂ : ∀ P ∈ primes₂, is_prime P)
    (hK₁ : K ≅ primes₁.foldl (· # ·) unknot)
    (hK₂ : K ≅ primes₂.foldl (· # ·) unknot) :
    ∃ (σ : Fin primes₁.length ≃ Fin primes₂.length),
      ∀ i : Fin primes₁.length,
        primes₁.get i ≅ primes₂.get (σ i) := by
  have e₁ := congrArg Finv (hK₁ : K = _)
  have e₂ := congrArg Finv (hK₂ : K = _)
  rw [Finv_foldl, Finv_unknot, zero_add, Finv_foldl_primes _ h₁] at e₁
  rw [Finv_foldl, Finv_unknot, zero_add, Finv_foldl_primes _ h₂] at e₂
  have hperm := Multiset.coe_eq_coe.mp (e₁.symm.trans e₂)
  obtain ⟨τ, hτ⟩ := perm_get_equiv hperm
  have hl₁ : (primes₁.map phi).length = primes₁.length := List.length_map _
  have hl₂ : (primes₂.map phi).length = primes₂.length := List.length_map _
  refine ⟨(finCongr hl₁.symm).trans (τ.trans (finCongr hl₂)), fun i => ?_⟩
  have := hτ (finCongr hl₁.symm i)
  simp only [List.get_eq_getElem, List.getElem_map] at this
  show primes₁.get i = primes₂.get _
  apply Finv_inj
  rw [Finv_prime _ (h₁ _ (List.get_mem _ _)), Finv_prime _ (h₂ _ (List.get_mem _ _))]
  simpa using this

noncomputable def knot_genus : Knot → ℕ := fun _ => 0
noncomputable def bridge_number : Knot → ℕ := fun _ => 1
def knot_complement : Knot → Type := fun _ => PUnit
def knot_group : Knot → Type := fun _ => PUnit
def manifold_connected_sum : Type → Type → Type := fun _ _ => PUnit
noncomputable def mirror : Knot → Knot := fun K => S (Multiset.map (fun q => -q) (Finv K))
noncomputable def alexander_polynomial : Knot → Polynomial ℤ := fun _ => 1
def ThreeManifold : Type := PUnit
def JSJ_decomposition : ThreeManifold → List ThreeManifold := fun _ => []

open Classical in
theorem knot_primality_in_NP :
    ∃ (verifier : Knot → Bool),
      ∀ K : Knot, verifier K = true ↔ is_prime K :=
  ⟨fun K => decide (is_prime K), fun K => by simp⟩

/-! ## Bridge.lean: los 2 axiomas -/

def rational_to_diagram {n : ℕ} (rc : TMENudos.RationalConfiguration n) : Diagram :=
  ⟨0, ⟨fun x => x.elim0⟩⟩

noncomputable def rational_to_knot {n : ℕ} (rc : TMENudos.RationalConfiguration n) : Knot :=
  Quotient.mk DiagramSetoid (rational_to_diagram rc)

theorem rational_equivalence_preserves_isotopy {n m : ℕ}
  {rc₁ : TMENudos.RationalConfiguration n} {rc₂ : TMENudos.RationalConfiguration m} :
  HEq rc₁ rc₂ → rational_to_knot rc₁ ≅ rational_to_knot rc₂ :=
  fun _ => rfl


/-! ## Comprobaciones de no trivialidad del modelo (adversariales) -/

/-- El trébol no es el nudo trivial. -/
theorem trefoil_ne_unknot : trefoil ≠ unknot := by
  intro h
  have := congrArg Finv h
  unfold trefoil at this
  rw [Finv_S_single 1 one_ne_zero, Finv_unknot] at this
  exact Multiset.singleton_ne_zero _ this

/-- Trébol y figura ocho son distintos. -/
theorem trefoil_ne_figure_eight : trefoil ≠ figure_eight := by
  intro h
  have := congrArg Finv h
  unfold trefoil figure_eight at this
  rw [Finv_S_single 1 one_ne_zero, Finv_S_single 2 two_ne_zero] at this
  have := Multiset.singleton_inj.mp this
  norm_num at this

/-- La suma conexa no es idempotente: `trefoil # trefoil ≠ trefoil`. -/
theorem trefoil_sq_ne_trefoil : trefoil # trefoil ≠ trefoil := by
  intro h
  have := congrArg (fun K => Multiset.card (Finv K)) h
  simp only [Finv_cs] at this
  unfold trefoil at this
  rw [Finv_S_single 1 one_ne_zero] at this
  simp at this

/-- `mirror` no es la identidad en el modelo. -/
theorem mirror_trefoil_ne_trefoil : mirror trefoil ≠ trefoil := by
  intro h
  have h1 : Finv trefoil = {1} := Finv_S_single 1 one_ne_zero
  have h2 : Finv (S (Multiset.map (fun q : ℚ => -q) {1})) = {-1} := by
    have := Finv_S_nz (Multiset.map (fun q : ℚ => -q) {1})
      (by intro x hx; simp at hx; rw [hx]; norm_num)
    simpa using this
  have h3 := congrArg Finv h
  unfold mirror at h3
  rw [h1, h2] at h3
  have h4 := Multiset.singleton_inj.mp h3
  norm_num at h4

/-- La relación de equivalencia del modelo NO es total: dos configuraciones de un cruce con
    razones distintas (1 y 2) no son equivalentes. -/
theorem equiv_not_total :
    ¬ reidemeister_equivalent
      (KnotConfig.mk (n := 1) fun i => ⟨i, i, 1⟩)
      (KnotConfig.mk (n := 1) fun i => ⟨i, i, 2⟩) := by
  intro h
  have := (equiv_iff_inv _ _).1 h
  simp [inv] at this


/-! ### EXTENSIÓN (2026-09-30): el axioma `jones2` de la Opción 1

Comprueba que añadir a la capa abstracta un invariante `jones2 : Knot → ℚ` con su especificación
mínima es CONSISTENTE con los 34 axiomas anteriores. En el modelo, `jones2 K` es el producto sobre
los elementos `q` de `Finv K` de un factor `f q`, con `f 1 = 4111/65536` (Jones del trébol derecho
en A = 2), `f (-1) = -61424` (el del izquierdo) y `f q = 1` en otro caso. Es multiplicativo porque
`Finv` convierte la suma conexa en suma de multiconjuntos. -/

noncomputable def jones2 : Knot → ℚ := fun K =>
  ((Finv K).map (fun q => if q = 1 then (4111 / 65536 : ℚ) else if q = -1 then (-61424 : ℚ) else 1)).prod

/-- Especificación 1: el invariante es multiplicativo bajo la suma conexa. -/
theorem jones2_connected_sum (K₁ K₂ : Knot) : jones2 (K₁ # K₂) = jones2 K₁ * jones2 K₂ := by
  unfold jones2
  rw [Finv_cs, Multiset.map_add, Multiset.prod_add]

/-- Especificación 2: el nudo trivial vale 1. -/
theorem jones2_unknot : jones2 unknot = 1 := by
  unfold jones2
  rw [Finv_unknot]
  simp

/-- Especificación 3: valor en el trébol (derecho). -/
theorem jones2_trefoil : jones2 trefoil = 4111 / 65536 := by
  unfold jones2 trefoil
  rw [Finv_S_single 1 one_ne_zero]
  simp

theorem Finv_mirror_trefoil : Finv (mirror trefoil) = {-1} := by
  unfold mirror trefoil
  rw [Finv_S_single 1 one_ne_zero]
  rw [Finv_S_nz]
  · simp
  · intro x hx
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hx
    rw [hx]; norm_num

/-- Especificación 4: valor en la imagen especular del trébol (el izquierdo). -/
theorem jones2_mirror_trefoil : jones2 (mirror trefoil) = -61424 := by
  unfold jones2
  rw [Finv_mirror_trefoil]
  norm_num

/-- **Lo que se deriva de la especificación**: nudo de la abuela ≠ nudo cuadrado. Solo usa las
    cuatro especificaciones de arriba (multiplicatividad y los valores en `trefoil` y en
    `mirror trefoil`), no la estructura interna del modelo. -/
theorem granny_distinct_from_square_derived :
    ¬ (trefoil # trefoil ≅ trefoil # mirror trefoil) := by
  intro h
  have h' : trefoil # trefoil = trefoil # mirror trefoil := h
  have := congrArg jones2 h'
  rw [jones2_connected_sum, jones2_connected_sum, jones2_trefoil, jones2_mirror_trefoil] at this
  norm_num at this

#print axioms jones2_connected_sum
#print axioms jones2_unknot
#print axioms jones2_trefoil
#print axioms jones2_mirror_trefoil
#print axioms granny_distinct_from_square_derived


end Model

/-! ## CERTIFICADO: `#print axioms` de los 34 (más los lemas de no trivialidad) -/

-- Reidemeister (11)
#print axioms Model.topologically_equivalent
#print axioms Model.topo_equiv_refl
#print axioms Model.topo_equiv_symm
#print axioms Model.topo_equiv_trans
#print axioms Model.R1_preserves_isotopy
#print axioms Model.R2_preserves_isotopy
#print axioms Model.R3_preserves_isotopy
#print axioms Model.R1_inverse
#print axioms Model.R2_inverse
#print axioms Model.R3_inverse
#print axioms Model.reidemeister_completeness
-- Schubert (21)
#print axioms Model.connected_sum
#print axioms Model.connected_sum_comm
#print axioms Model.connected_sum_assoc
#print axioms Model.connected_sum_unknot
#print axioms Model.trefoil
#print axioms Model.figure_eight
#print axioms Model.cinquefoil
#print axioms Model.trefoil_is_prime
#print axioms Model.figure_eight_is_prime
#print axioms Model.schubert_existence_axiom
#print axioms Model.schubert_uniqueness
#print axioms Model.knot_genus
#print axioms Model.bridge_number
#print axioms Model.knot_complement
#print axioms Model.knot_group
#print axioms Model.manifold_connected_sum
#print axioms Model.knot_primality_in_NP
#print axioms Model.mirror
#print axioms Model.alexander_polynomial
#print axioms Model.ThreeManifold
#print axioms Model.JSJ_decomposition
-- Bridge (2)
#print axioms Model.rational_to_diagram
#print axioms Model.rational_equivalence_preserves_isotopy
-- Extras (no trivialidad, caracterización)
#print axioms Model.equiv_iff_inv
#print axioms Model.is_prime_iff
#print axioms Model.trefoil_ne_unknot
#print axioms Model.trefoil_ne_figure_eight
#print axioms Model.trefoil_sq_ne_trefoil
#print axioms Model.mirror_trefoil_ne_trefoil
#print axioms Model.equiv_not_total

/-! ## Volcado de tipos para comparar con los originales (ver 06d_tipos_originales.lean) -/

section Fidelidad
open Lean Meta Elab Command

def strip (s : String) : String :=
  ["TMENudos.Reidemeister.ReidemeisterMoves.", "TMENudos.Reidemeister.",
   "TMENudos.SchubertTheorems.", "TMENudos.Bridge.", "Model."].foldl (fun s p => s.replace p "") s

def typeNames : List String := [
  "Crossing.mk", "KnotConfig.mk", "Strand.mk", "R1Move.mk", "R2Move.mk", "R3Move.mk",
  "CrossingSign.Positive", "CrossingSign.Negative",
  "reidemeister_equivalent", "reidemeister_equivalent.refl", "reidemeister_equivalent.symm",
  "reidemeister_equivalent.trans", "reidemeister_equivalent.R1", "reidemeister_equivalent.R2",
  "reidemeister_equivalent.R3", "apply_R1", "apply_R2", "apply_R3",
  "Diagram.mk", "diagram_equiv", "DiagramSetoid", "Knot", "knot_isotopic", "unknot", "is_prime",
  "topologically_equivalent", "topo_equiv_refl", "topo_equiv_symm", "topo_equiv_trans",
  "R1_preserves_isotopy", "R2_preserves_isotopy", "R3_preserves_isotopy",
  "R1_inverse", "R2_inverse", "R3_inverse", "reidemeister_completeness",
  "connected_sum", "connected_sum_comm", "connected_sum_assoc", "connected_sum_unknot",
  "trefoil", "figure_eight", "cinquefoil", "trefoil_is_prime", "figure_eight_is_prime",
  "schubert_existence_axiom", "schubert_uniqueness", "knot_genus", "bridge_number",
  "knot_complement", "knot_group", "manifold_connected_sum", "knot_primality_in_NP", "mirror",
  "alexander_polynomial", "ThreeManifold", "JSJ_decomposition",
  "rational_to_diagram", "rational_to_knot", "rational_equivalence_preserves_isotopy",
  "jones2", "jones2_connected_sum", "jones2_trefoil", "jones2_mirror_trefoil"]

def valueNames : List String :=
  ["Knot", "knot_isotopic", "unknot", "is_prime", "diagram_equiv", "DiagramSetoid"]

def findConst (env : Environment) (short : String) : Option ConstantInfo :=
  ["Model.", "TMENudos.Reidemeister.ReidemeisterMoves.", "TMENudos.Reidemeister.",
   "TMENudos.SchubertTheorems.", "TMENudos.Bridge."].findSome? fun p =>
    env.find? (p ++ short).toName

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
#eval show MetaM Unit from do
  let env ← getEnv
  for s in typeNames do
    match findConst env s with
    | none => IO.println s!"TYPE {s} :: NOT FOUND"
    | some ci =>
      let f ← ppExpr ci.type
      IO.println s!"TYPE {s} :: {strip (f.pretty 100000)}"
  for s in valueNames do
    match findConst env s with
    | some ci =>
      match ci.value? with
      | some v =>
        let f ← ppExpr v
        IO.println s!"VALUE {s} :: {strip (f.pretty 100000)}"
      | none => IO.println s!"VALUE {s} :: (sin valor)"
    | none => IO.println s!"VALUE {s} :: NOT FOUND"

end Fidelidad
