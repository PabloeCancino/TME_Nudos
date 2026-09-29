-- KN_Examples.lean
-- Ejemplos Concretos de Configuraciones Kₙ

import TMENudos.KN_General

/-!
# Ejemplos de Configuraciones Kₙ

Este archivo demuestra el uso del framework general `KN_General.lean` con
ejemplos concretos de nudos de 3, 4 y 5 cruces.

## Contenido

1. **Nudos K₃** (3 cruces): Trébol y su espejo
2. **Nudos K₄** (4 cruces): k_4_1 y k_4_2 desde BD_Nudos
3. **Helpers**: Funciones para construir configuraciones desde listas

-/

open KnotTheory.General

/-! ## Funciones Helper -/

/-- Crea un OrderedPairN desde dos valores naturales (módulo 2n) -/
def mkPairN (n : ℕ) (a b : ℕ) (hab : ((a : ZMod (2 * n)) ≠ (b : ZMod (2 * n)))) :
    OrderedPairN n :=
  ⟨(a : ZMod (2 * n)), (b : ZMod (2 * n)), hab⟩

/-- Criterio decidible de partición: cada elemento aparece en exactamente un par. -/
theorem partition_of_card {n : ℕ} (S : Finset (OrderedPairN n))
    (h : ∀ i : ZMod (2 * n), (S.filter (fun p => i = p.fst ∨ i = p.snd)).card = 1) :
    ∀ i : ZMod (2 * n), ∃! p ∈ S, i = p.fst ∨ i = p.snd := by
  intro i
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (h i)
  have hmem : ∀ p, p ∈ S ∧ (i = p.fst ∨ i = p.snd) ↔ p = a := by
    intro p
    have := Finset.ext_iff.mp ha p
    simpa using this
  refine ⟨a, ?_, ?_⟩
  · exact (hmem a).mpr rfl
  · intro q hq
    exact (hmem q).mp hq

/-! ## Ejemplos K₃: Nudos de 3 Cruces -/

section K3_Examples

/-- Trébol derecho: configuración [[1,4],[5,2],[3,0]] en Z/6Z

    DME = [3,-3,-3]
    Quiralidad: RightHanded
-/
def example_k3_trefoil_right : K3Config :=
  ⟨{mkPairN 3 1 4 (by decide), mkPairN 3 5 2 (by decide), mkPairN 3 3 0 (by decide)},
   by decide, partition_of_card _ (by decide)⟩

/-- Trébol izquierdo: espejo del trébol derecho

    DME = [-3,3,3]
    Quiralidad: LeftHanded
-/
def example_k3_trefoil_left : K3Config := KnConfig.swap example_k3_trefoil_right

end K3_Examples

/-! ## Ejemplos K₄: Nudos de 4 Cruces -/

section K4_Examples

/-- k_4_1: configuración [[1,4],[7,2],[3,6],[5,0]] en Z/8Z

    Según BD_Nudos/configuraciones_nudos.json:
    - num_cruces: 4
    - configuracion_Racional: [[1,4],[7,2],[3,6],[5,0]]
    - DME_reportado: [3,3,3,3]
-/
def k_4_1 : K4Config :=
  ⟨{mkPairN 4 1 4 (by decide), mkPairN 4 7 2 (by decide),
    mkPairN 4 3 6 (by decide), mkPairN 4 5 0 (by decide)},
   by decide, partition_of_card _ (by decide)⟩

/-- k_4_2: configuración [[4,1],[2,7],[6,3],[0,5]] en Z/8Z

    Según BD_Nudos/configuraciones_nudos.json:
    - num_cruces: 4
    - configuracion_racional: [[4,1],[2,7],[6,3],[0,5]]
    - DME_reportado: [5,5,5,5]

    **Nota:** Esta es la configuración espejo de k_4_1
-/
def k_4_2 : K4Config :=
  ⟨{mkPairN 4 4 1 (by decide), mkPairN 4 2 7 (by decide),
    mkPairN 4 6 3 (by decide), mkPairN 4 0 5 (by decide)},
   by decide, partition_of_card _ (by decide)⟩

/-- Verificación: k_4_2 es el espejo de k_4_1 -/
example : k_4_2 = KnConfig.swap k_4_1 := by decide

end K4_Examples

/-! ## Tests de Invariantes -/

section Invariant_Tests

-- Verificar DME de k_4_1
#check k_4_1.dme
example : k_4_1.dme.length = 4 := by
  simp only [KnConfig.dme, KnConfig.pairsList, List.length_map, Finset.length_toList]
  exact k_4_1.card_eq

-- Verificar Writhe
#check k_4_1.writhe
example : k_4_1.writhe ≠ 0 := by
  have h : k_4_1.writhe = (k_4_1.pairs.toList.map
      (fun p => KnConfig.adjustDeltaN 4 (KnConfig.pairDelta p))).sum := by
    unfold KnConfig.writhe KnConfig.dme KnConfig.pairsList
    rw [List.sum_eq_foldl]
  rw [h, Finset.sum_map_toList]
  decide  -- Confirma quiralidad

-- CAMBIO DE ENUNCIADO (auditoría):
-- antes:   `(swap K).ime = K.ime` como igualdad de listas (sorry; no demostrable porque
--          `dme` usa `Finset.toList`, que no fija un orden).
-- después: igualdad como multiconjunto (independiente del orden de `toList`).
/-- `adjustDeltaN` es impar (para |δ| < 2n). -/
private lemma adjustDeltaN_neg (n : ℕ) (δ : ℤ) (h : |δ| < 2 * n) :
    KnConfig.adjustDeltaN n (-δ) = -KnConfig.adjustDeltaN n δ := by
  unfold KnConfig.adjustDeltaN
  rw [abs_lt] at h
  dsimp only
  split_ifs <;> omega

/-- IME (como multiconjunto) es invariante bajo el espejo de `KN_General` (swap over/under). -/
theorem ime_swap_multiset {n : ℕ} [NeZero n] (K : KnConfig n) :
    ((KnConfig.swap K).ime : Multiset ℕ) = (K.ime : Multiset ℕ) := by
  have hinj : Set.InjOn OrderedPairN.reverse (K.pairs : Set (OrderedPairN n)) := by
    intro x _ y _ hxy
    calc x = x.reverse.reverse := (OrderedPairN.reverse_involutive x).symm
         _ = y.reverse.reverse := by rw [hxy]
         _ = y := OrderedPairN.reverse_involutive y
  have hval : ∀ K' : KnConfig n, ((K'.ime : List ℕ) : Multiset ℕ) =
      K'.pairs.val.map (fun p => (KnConfig.adjustDeltaN n (KnConfig.pairDelta p)).natAbs) := by
    intro K'
    unfold KnConfig.ime KnConfig.dme KnConfig.pairsList
    rw [List.map_map, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  rw [hval, hval]
  have hm : (KnConfig.swap K).pairs.val = K.pairs.val.map OrderedPairN.reverse :=
    Finset.image_val_of_injOn hinj
  rw [hm, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp]
  have hlt : |KnConfig.pairDelta p| < 2 * (n : ℤ) := by
    unfold KnConfig.pairDelta
    have h1 := ZMod.val_lt p.fst
    have h2 := ZMod.val_lt p.snd
    rw [abs_lt]; push_cast at h1 h2 ⊢; omega
  have : KnConfig.pairDelta p.reverse = -KnConfig.pairDelta p := by
    unfold KnConfig.pairDelta OrderedPairN.reverse; ring
  rw [this, adjustDeltaN_neg n _ hlt, Int.natAbs_neg]

example (K : K4Config) :
    ((KnConfig.swap K).ime : Multiset ℕ) = (K.ime : Multiset ℕ) :=
  ime_swap_multiset K

end Invariant_Tests

/-! ## Verificación de Compilación -/

#check K3Config  -- Tipo: Type := KnConfig 3
#check K4Config  -- Tipo: Type := KnConfig 4
#check K5Config  -- Tipo: Type := KnConfig 5

#check @KnConfig.dme     -- Funciona para cualquier n
#check @KnConfig.swap  -- Funciona para cualquier n
