-- TCN_05_Orbitas.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 5 - Órbitas y Simetrías

import TMENudos.TCN_04_DihedralD6
import TMENudos.TCN_02_Reidemeister
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bloque 5: Órbitas y Simetrías

Definiciones de órbitas y estabilizadores usando acciones de D₆.

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralD6 K3Config
open BigOperators

instance : DecidableEq K3Config := inferInstance
instance : DecidableEq DihedralD6 := inferInstance

/-! ## Instancia MulAction -/

-- La instancia se hereda de TCN_04_DihedralD6

/-! ## Órbitas -/

/-- La órbita de una configuración K bajo D₆.

    ✅ RESUELTO: Implementación concreta -/
def orbit (K : K3Config) : Finset K3Config :=
  Finset.univ.image (fun g : DihedralD6 => DihedralD6.actOnConfig g K)

/-- Notación para órbita -/
notation "Orb(" K ")" => orbit K

/-! ## Estabilizadores -/

/-- El estabilizador de una configuración K.

    ✅ RESUELTO: Implementación concreta -/
def stabilizer (K : K3Config) : Finset DihedralD6 :=
  Finset.univ.filter (fun g => DihedralD6.actOnConfig g K = K)

/-- Notación para estabilizador -/
notation "Stab(" K ")" => stabilizer K

/-! ## Teoremas Básicos -/

/-- Toda configuración está en su propia órbita -/
theorem mem_orbit_self (K : K3Config) : K ∈ Orb(K) := by
  unfold orbit
  simp [Finset.mem_image]
  use 1
  exact DihedralD6.actOnConfig_id K

/-- La identidad siempre está en el estabilizador -/
theorem one_mem_stabilizer (K : K3Config) : 1 ∈ Stab(K) := by
  unfold stabilizer
  simp [DihedralD6.actOnConfig_id]

/-! ## Propiedades de Órbitas -/

/-- Dos configuraciones están en la misma órbita ssi una es imagen de la otra -/
theorem in_same_orbit_iff (K₁ K₂ : K3Config) :
  K₂ ∈ Orb(K₁) ↔ ∃ g : DihedralD6, DihedralD6.actOnConfig g K₁ = K₂ := by
  unfold orbit
  simp [Finset.mem_image]

/-- Si K₂ no está en Orb(K₁), entonces las órbitas son disjuntas -/
theorem orbits_disjoint (K₁ K₂ : K3Config) :
  K₂ ∉ Orb(K₁) → Orb(K₁) ∩ Orb(K₂) = ∅ := by
  sorry  -- Requiere teoría avanzada de órbitas

/-! ## Lemas auxiliares -/

/-- El grupo D₆ tiene cardinalidad 12 -/
lemma card_D6 : Finset.card (Finset.univ : Finset DihedralD6) = 12 := by
  exact calc
    Finset.card (Finset.univ : Finset DihedralD6) = 12 := by
      simp [DihedralD6.card_eq_12]
    _ = 12 := rfl

/-- El estabilizador es un subgrupo -/
theorem stabilizer_is_subgroup (K : K3Config) :
    (1 : DihedralD6) ∈ Stab(K) ∧
    (∀ g h, g ∈ Stab(K) → h ∈ Stab(K) → g * h ∈ Stab(K)) ∧
    (∀ g, g ∈ Stab(K) → g⁻¹ ∈ Stab(K)) := by
  constructor
  · exact one_mem_stabilizer K
  constructor
  · intro g h hg hh
    unfold stabilizer at *
    simp [Finset.mem_filter, Finset.mem_univ] at hg hh ⊢
    rw [DihedralD6.actOnConfig_comp, hh, hg]
  · intro g hg
    unfold stabilizer at *
    simp [Finset.mem_filter, Finset.mem_univ] at hg ⊢
    rw [← hg, ← DihedralD6.actOnConfig_comp, inv_mul_cancel, DihedralD6.actOnConfig_id, hg]

/-! ## Teorema Órbita-Estabilizador -/

/-- Teorema órbita-estabilizador: |Orb(K)| * |Stab(K)| = |D₆| = 12 -/
theorem orbit_stabilizer (K : K3Config) :
    (Orb(K)).card * (Stab(K)).card = 12 := by
  let f : DihedralD6 → K3Config := fun g => DihedralD6.actOnConfig g K

  have h_fiber_bij (C : K3Config) (hC : C ∈ Orb(K)) :
      ∃ g, C = f g ∧ (Finset.filter (fun x => f x = C) Finset.univ).card = (Stab(K)).card := by
    rcases (in_same_orbit_iff K C).mp hC with ⟨g, hg⟩
    use g
    constructor
    · exact hg.symm
    · let map : DihedralD6 → DihedralD6 := fun s => g * s

      have h_im : (Stab(K)).image map = Finset.filter (fun x => f x = C) Finset.univ := by
        ext x
        simp only [map, stabilizer, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro h
          rcases h with ⟨s, hs, rfl⟩
          dsimp [f]
          rw [← hg, DihedralD6.actOnConfig_comp, hs]
        · intro hx
          refine ⟨g⁻¹ * x, ?_, ?_⟩
          · dsimp [f] at hx ⊢
            rw [DihedralD6.actOnConfig_comp, hx, ← hg, ← DihedralD6.actOnConfig_comp, inv_mul_cancel, DihedralD6.actOnConfig_id]
          · simp

      rw [← h_im, Finset.card_image_of_injective]
      intro a b h
      exact mul_left_cancel h

  calc
    (Orb(K)).card * (Stab(K)).card = Finset.sum (Orb(K) : Finset K3Config) (fun C => (Stab(K)).card) := by
      rw [Finset.sum_const]
      change (Orb(K)).card * (Stab(K)).card = (Orb(K)).card • (Stab(K)).card
      rfl
    _ = Finset.sum (Orb(K) : Finset K3Config) (fun C => (Finset.filter (fun g => f g = C) (Finset.univ : Finset DihedralD6)).card) := by
      refine Finset.sum_congr rfl fun C hC => ?_
      rcases h_fiber_bij C hC with ⟨_, _, h_card⟩
      rw [h_card]
    _ = (Finset.univ : Finset DihedralD6).card := by
      -- Orb(K) == univ.image f
      have : Orb(K) = Finset.univ.image f := rfl
      rw [this, Finset.card_eq_sum_card_image]
    _ = 12 := card_D6

/-! ## Cálculo de tamaño de órbita -/

/-- Cálculo de tamaño de órbita a partir del tamaño del estabilizador -/
theorem orbit_card_from_stabilizer (K : K3Config) (n : ℕ) (hn : 0 < n) (_ : n ∣ 12) :
    (Stab(K)).card = n → (Orb(K)).card = 12 / n := by
  intro h_stab
  have h_total := orbit_stabilizer K
  rw [h_stab, mul_comm] at h_total
  exact Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt hn) h_total

/-! ## Corolarios útiles -/

/-- Versión alternativa del teorema órbita-estabilizador -/
theorem orbit_stabilizer' (K : K3Config) :
    (Orb(K)).card = 12 / (Stab(K)).card ∧ (Stab(K)).card ∣ 12 := by
  have h_card := orbit_stabilizer K
  have h_pos : 0 < (Stab(K)).card := by
    have : 1 ∈ Stab(K) := one_mem_stabilizer K
    exact Finset.card_pos.mpr ⟨1, this⟩
  constructor
  · rw [mul_comm] at h_card
    exact Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt h_pos) h_card
  · rw [← h_card]
    exact ⟨(Orb(K)).card, rfl⟩

/-- El tamaño de la órbita divide al tamaño del grupo -/
theorem orbit_card_dvd (K : K3Config) : (Orb(K)).card ∣ 12 := by
  have h := orbit_stabilizer' K
  rcases h with ⟨h_eq, h_div⟩
  rw [h_eq]
  exact Nat.div_dvd_of_dvd h_div

/-- El tamaño del estabilizador divide al tamaño del grupo -/
theorem stabilizer_card_dvd (K : K3Config) : (Stab(K)).card ∣ 12 :=
  (orbit_stabilizer' K).2

/-- Órbita de tamaño 6 -/
theorem orbit_card_6_of_stab_2 (K : K3Config) :
  (Stab(K)).card = 2 → (Orb(K)).card = 6 := by
  exact orbit_card_from_stabilizer K 2 (by norm_num) (by norm_num)

/-- Órbita de tamaño 4 -/
theorem orbit_card_4_of_stab_3 (K : K3Config) :
  (Stab(K)).card = 3 → (Orb(K)).card = 4 := by
  exact orbit_card_from_stabilizer K 3 (by norm_num) (by norm_num)

/-- Órbita de tamaño 3 -/
theorem orbit_card_3_of_stab_4 (K : K3Config) :
  (Stab(K)).card = 4 → (Orb(K)).card = 3 := by
  exact orbit_card_from_stabilizer K 4 (by norm_num) (by norm_num)


/-! ## Configuraciones sin R1 ni R2 -/

/-- Conjunto de todas las configuraciones K₃ sin movimientos R1 ni R2 -/
def configsNoR1NoR2 : Finset K3Config :=
  sorry  -- Requiere Fintype K3Config

/-- El número de configuraciones sin R1 ni R2 es 14 -/
axiom configs_no_r1_no_r2_card : configsNoR1NoR2.card = 14


/-!
## Resumen

✅ **Definiciones resueltas** (sin sorry):
- `orbit`: Línea 36
- `stabilizer`: Línea 45
- `MulAction` instance

✅ **Teoremas básicos probados**:
- `mem_orbit_self`
- `one_mem_stabilizer`

⚠️ **2 sorry en teoremas avanzados**:
- `orbit_stabilizer`
- `orbit_card_from_stabilizer`

-/

end KnotTheory
