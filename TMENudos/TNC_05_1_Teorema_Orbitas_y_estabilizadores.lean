-- TCN_05_Orbitas_Sustento.lean
-- Sustento para los teoremas avanzados de órbitas

import TMENudos.TCN_05_Orbitas

namespace KnotTheory

open DihedralD6 K3Config

/-! ## Lemas auxiliares -/

/-- El grupo D₆ tiene cardinalidad 12 -/
lemma card_D6 : Finset.card (Finset.univ : Finset DihedralD6) = 12 := by
  exact calc
    Finset.card (Finset.univ : Finset DihedralD6) = 12 := by
      simp [DihedralD6.card_eq_12]
    _ = 12 := rfl

/-- La acción de grupo induce una biyección entre clases laterales y elementos de la órbita -/
private lemma orbit_bijection (K : K3Config) (g : DihedralD6) :
    (fun (h : DihedralD6) => h * g) ⁻¹' Stab(K) = Stab(DihedralD6.actOnConfig g K) := by
  ext x
  simp [stabilizer, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rw [← h]
    simp [DihedralD6.actOnConfig_comp, mul_assoc]
  · intro h
    have : DihedralD6.actOnConfig (x * g) K = DihedralD6.actOnConfig g K := by
      rw [h]
    calc
      DihedralD6.actOnConfig (x * g) K = DihedralD6.actOnConfig g K := this
      _ = DihedralD6.actOnConfig g (DihedralD6.actOnConfig (g⁻¹ * g) K) := by
        simp [DihedralD6.actOnConfig_comp]
      _ = DihedralD6.actOnConfig (g * g⁻¹ * g) K := by
        simp [DihedralD6.actOnConfig_comp, mul_assoc]
      _ = DihedralD6.actOnConfig (1 * g) K := by simp
      _ = DihedralD6.actOnConfig g K := by simp

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
    rw [DihedralD6.actOnConfig_comp, hg, hh]
  · intro g hg
    unfold stabilizer at *
    simp [Finset.mem_filter, Finset.mem_univ] at hg ⊢
    rw [← DihedralD6.actOnConfig_id K, ← DihedralD6.actOnConfig_comp]
    have : g⁻¹ * g = 1 := by simp
    rw [this, DihedralD6.actOnConfig_id]
    exact hg

/-! ## Teorema Órbita-Estabilizador -/

/-- Teorema órbita-estabilizador: |Orb(K)| * |Stab(K)| = |D₆| = 12 -/
theorem orbit_stabilizer (K : K3Config) :
    (Orb(K)).card * (Stab(K)).card = 12 := by
  -- Usamos que D₆ actúa transitivamente sobre cada órbita
  -- y que hay una biyección entre D₆/Stab(K) y Orb(K)
  let f : DihedralD6 → K3Config := fun g => DihedralD6.actOnConfig g K
  
  -- f es sobreyectiva sobre Orb(K)
  have h_surj : ∀ C ∈ Orb(K), ∃ g : DihedralD6, f g = C := by
    intro C hC
    rcases (in_same_orbit_iff K C).mp hC with ⟨g, hg⟩
    exact ⟨g, hg⟩
  
  -- Las fibras de f son las clases laterales de Stab(K)
  have h_fibers : ∀ g h : DihedralD6, f g = f h ↔ h⁻¹ * g ∈ Stab(K) := by
    intro g h
    constructor
    · intro h_eq
      unfold stabilizer
      simp [Finset.mem_filter, Finset.mem_univ]
      rw [← h_eq]
      simp [DihedralD6.actOnConfig_comp]
    · intro h_stab
      calc
        f g = DihedralD6.actOnConfig (h * (h⁻¹ * g)) K := by simp [mul_assoc]
        _ = DihedralD6.actOnConfig h (DihedralD6.actOnConfig (h⁻¹ * g) K) := by
          rw [DihedralD6.actOnConfig_comp]
        _ = DihedralD6.actOnConfig h K := by
          rw [show DihedralD6.actOnConfig (h⁻¹ * g) K = K from h_stab]
        _ = f h := rfl
  
  -- Contamos el número de elementos en cada fibra
  have h_card_fiber : ∀ g : DihedralD6, (Finset.filter (fun h => f h = f g) Finset.univ).card = (Stab(K)).card := by
    intro g
    calc
      (Finset.filter (fun h => f h = f g) Finset.univ).card
          = (Finset.image (fun s => s * g) (Stab(K))).card := by
        refine Finset.card_congr (fun h _ => h * g) ?_ ?_ ?_
        · intro h hh
          simp [stabilizer, Finset.mem_filter, Finset.mem_univ] at hh ⊢
          exact h_fibers (h * g) g |>.mpr (by simp [hh])
        · intro h₁ h₂ h₁_in h₂_in h_eq
          apply_fun (fun x => x * g⁻¹) at h_eq
          simp at h_eq
          exact h_eq
        · intro h hh
          rcases Finset.mem_image.mp hh with ⟨s, hs, rfl⟩
          exact ⟨s, hs, rfl⟩
      _ = (Stab(K)).card := by
        refine Finset.card_image_of_injective (Stab(K)) ?_
        exact mul_left_injective g
  
  -- Aplicamos el principio de conteo
  calc
    (Orb(K)).card * (Stab(K)).card = (Finset.univ : Finset DihedralD6).card := by
      rw [card_D6]
      exact calc
        (Orb(K)).card * (Stab(K)).card
            = (∑ C in Orb(K), 1) * (Stab(K)).card := by simp
        _ = ∑ C in Orb(K), (Stab(K)).card := by
          rw [Finset.mul_sum]
        _ = ∑ C in Orb(K), (Finset.filter (fun g => f g = C) Finset.univ).card := by
          refine Finset.sum_congr rfl fun C hC => ?_
          rcases h_surj C hC with ⟨g, rfl⟩
          rw [h_card_fiber g]
        _ = (Finset.univ : Finset DihedralD6).card := by
          rw [Finset.card_eq_sum_card_fiberwise f]
    _ = 12 := card_D6

/-! ## Cálculo de tamaño de órbita -/

/-- Cálculo de tamaño de órbita a partir del tamaño del estabilizador -/
theorem orbit_card_from_stabilizer (K : K3Config) (n : ℕ) (hn : 0 < n) (hdiv : n ∣ 12) :
    (Stab(K)).card = n → (Orb(K)).card = 12 / n := by
  intro h_stab
  have h_total := orbit_stabilizer K
  rw [h_stab] at h_total
  
  -- Usamos que n divide a 12 y es positivo
  have h_div : 12 / n * n = 12 - (12 % n) := by
    exact Nat.div_mul_eq_sub_mod 12 n
  
  have h_mod : 12 % n = 0 := by
    exact Nat.mod_eq_zero_of_dvd hdiv
  
  rw [h_mod] at h_div
  simp at h_div
  
  -- Resolvemos para |Orb(K)|
  have h_eq : (Orb(K)).card * n = 12 := by
    rwa [h_stab] at h_total
    
  apply Nat.eq_of_mul_eq_mul_right hn
  rw [h_eq, Nat.mul_div_cancel]
  · rfl
  · exact Nat.pos_of_dvd_of_pos hdiv (by norm_num)
  
  -- Alternativamente, usando división exacta
  have : n ∣ (Orb(K)).card * n := ⟨(Orb(K)).card, rfl⟩
  have : n ∣ 12 := by rwa [← h_eq]
  exact Nat.div_eq_of_eq_mul_dvd (by linarith) hdiv

/-! ## Corolarios útiles -/

/-- Versión alternativa del teorema órbita-estabilizador -/
theorem orbit_stabilizer' (K : K3Config) :
    (Orb(K)).card = 12 / (Stab(K)).card ∧ (Stab(K)).card ∣ 12 := by
  have h_card := orbit_stabilizer K
  have h_pos : 0 < (Stab(K)).card := by
    have : 1 ∈ Stab(K) := one_mem_stabilizer K
    exact Finset.one_lt_card.mpr ⟨1, this⟩
  constructor
  · apply Nat.eq_div_of_mul_eq h_pos h_card
  · rw [← h_card]
    exact ⟨(Orb(K)).card, rfl⟩

/-- El tamaño de la órbita divide al tamaño del grupo -/
theorem orbit_card_dvd (K : K3Config) : (Orb(K)).card ∣ 12 := by
  have h := orbit_stabilizer' K
  rcases h with ⟨h_eq, h_div⟩
  rw [h_eq]
  exact Nat.div_dvd_div h_div (by rfl)

/-- El tamaño del estabilizador divide al tamaño del grupo -/
theorem stabilizer_card_dvd (K : K3Config) : (Stab(K)).card ∣ 12 :=
  (orbit_stabilizer' K).2

end KnotTheory