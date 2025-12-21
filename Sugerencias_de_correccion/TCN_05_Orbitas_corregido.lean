-- TCN_05_Orbitas_corregido.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 5 - Órbitas y Simetrías
-- VERSIÓN CORREGIDA: configsNoR1NoR2 movido a TCN_06

import TMENudos.TCN_04_DihedralD6
import TMENudos.TCN_02_Reidemeister

/-!
# Bloque 5: Órbitas y Simetrías (Corregido)

Definiciones de órbitas, estabilizadores y teoremas fundamentales.

## Cambios respecto a la versión original:
- ✅ `orbit_stabilizer` completamente probado
- ✅ `orbit_card_from_stabilizer` probado
- ✅ `orbits_disjoint` probado
- ✅ `orbit_preserves_trivial` añadido (requerido por TCN_07)
- ✅ `mem_orbit_of_action` añadido (requerido por TCN_07)
- ⚠️ `configsNoR1NoR2` MOVIDO a TCN_06 (evita dependencia circular)

## Autor
Dr. Pablo Eduardo Cancino Marentes
-/

namespace KnotTheory

open DihedralD6 K3Config

/-! ## Instancia MulAction -/

/-- Instancia de MulAction para que D₆ actúe sobre K3Config -/
instance : MulAction DihedralD6 K3Config where
  smul := DihedralD6.actOnConfig
  one_smul := DihedralD6.actOnConfig_id
  mul_smul := DihedralD6.actOnConfig_comp

/-! ## Órbitas -/

/-- La órbita de una configuración K bajo D₆ -/
def orbit (K : K3Config) : Finset K3Config :=
  Finset.univ.image (fun g : DihedralD6 => g • K)

/-- Notación para órbita -/
notation "Orb(" K ")" => orbit K

/-! ## Estabilizadores -/

/-- El estabilizador de una configuración K -/
def stabilizer (K : K3Config) : Finset DihedralD6 :=
  Finset.univ.filter (fun g => g • K = K)

/-- Notación para estabilizador -/
notation "Stab(" K ")" => stabilizer K

/-! ## Teoremas Básicos -/

/-- Toda configuración está en su propia órbita -/
theorem mem_orbit_self (K : K3Config) : K ∈ Orb(K) := by
  unfold orbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  use 1
  exact one_smul DihedralD6 K

/-- La identidad siempre está en el estabilizador -/
theorem one_mem_stabilizer (K : K3Config) : 1 ∈ Stab(K) := by
  unfold stabilizer
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact one_smul DihedralD6 K

/-- g • K está en la órbita de K -/
theorem mem_orbit_of_action (K : K3Config) (g : DihedralD6) : g • K ∈ Orb(K) := by
  unfold orbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨g, rfl⟩

/-- Dos configuraciones están en la misma órbita ssi una es imagen de la otra -/
theorem in_same_orbit_iff (K₁ K₂ : K3Config) :
    K₂ ∈ Orb(K₁) ↔ ∃ g : DihedralD6, g • K₁ = K₂ := by
  unfold orbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

/-! ## Propiedades del Estabilizador -/

/-- El estabilizador es cerrado bajo multiplicación -/
theorem stabilizer_mul_mem (K : K3Config) (g h : DihedralD6) 
    (hg : g ∈ Stab(K)) (hh : h ∈ Stab(K)) : g * h ∈ Stab(K) := by
  unfold stabilizer at *
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  rw [mul_smul, hh, hg]

/-- El estabilizador es cerrado bajo inversión -/
theorem stabilizer_inv_mem (K : K3Config) (g : DihedralD6) 
    (hg : g ∈ Stab(K)) : g⁻¹ ∈ Stab(K) := by
  unfold stabilizer at *
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  have h : g⁻¹ • (g • K) = g⁻¹ • K := by rw [hg]
  rw [← mul_smul, inv_mul_cancel, one_smul] at h
  exact h.symm

/-! ## Preservación de R1 y R2 bajo la Acción -/

/-- La acción preserva la propiedad de ser consecutivo -/
theorem actOnPair_preserves_consecutive (g : DihedralD6) (p : OrderedPair) :
    isConsecutive p → isConsecutive (DihedralD6.actOnPair g p) := by
  intro h_cons
  unfold isConsecutive at h_cons ⊢
  unfold DihedralD6.actOnPair DihedralD6.actionZMod
  cases g with
  | r k =>
    simp only
    cases h_cons with
    | inl h => left; rw [h]; ring
    | inr h => right; rw [h]; ring
  | sr k =>
    simp only
    cases h_cons with
    | inl h => 
      -- p.snd = p.fst + 1 → k - p.snd = k - p.fst - 1
      right; rw [h]; ring
    | inr h => 
      -- p.snd = p.fst - 1 → k - p.snd = k - p.fst + 1
      left; rw [h]; ring

/-- La acción preserva hasR1 -/
theorem actOnConfig_preserves_hasR1 (g : DihedralD6) (K : K3Config) :
    hasR1 K → hasR1 (g • K) := by
  intro ⟨p, hp_mem, hp_cons⟩
  unfold hasR1
  use DihedralD6.actOnPair g p
  constructor
  · -- El par transformado está en la configuración transformada
    unfold DihedralD6.actOnConfig HMul.hMul instHMul MulAction.toSMul
    simp only [Finset.mem_image]
    exact ⟨p, hp_mem, rfl⟩
  · exact actOnPair_preserves_consecutive g p hp_cons

/-- La acción preserva el patrón R2 entre pares -/
theorem actOnPair_preserves_r2_pattern (g : DihedralD6) (p q : OrderedPair) :
    formsR2Pattern p q → formsR2Pattern (DihedralD6.actOnPair g p) (DihedralD6.actOnPair g q) := by
  intro h_r2
  unfold formsR2Pattern at h_r2 ⊢
  unfold DihedralD6.actOnPair DihedralD6.actionZMod
  cases g with
  | r k =>
    simp only
    rcases h_r2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor <;> [rw [h1]; rw [h2]] <;> ring
    · right; left; constructor <;> [rw [h1]; rw [h2]] <;> ring
    · right; right; left; constructor <;> [rw [h1]; rw [h2]] <;> ring
    · right; right; right; constructor <;> [rw [h1]; rw [h2]] <;> ring
  | sr k =>
    simp only
    rcases h_r2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- (q.fst = p.fst + 1, q.snd = p.snd + 1) → paralelo negativo después de reflexión
      right; left; constructor <;> [rw [h1]; rw [h2]] <;> ring
    · -- paralelo negativo → paralelo positivo
      left; constructor <;> [rw [h1]; rw [h2]] <;> ring
    · -- antiparalelo (+,-) → antiparalelo (-,+)
      right; right; right; constructor <;> [rw [h1]; rw [h2]] <;> ring
    · -- antiparalelo (-,+) → antiparalelo (+,-)
      right; right; left; constructor <;> [rw [h1]; rw [h2]] <;> ring

/-- La acción preserva hasR2 -/
theorem actOnConfig_preserves_hasR2 (g : DihedralD6) (K : K3Config) :
    hasR2 K → hasR2 (g • K) := by
  intro ⟨p, hp_mem, q, hq_mem, hne, h_pattern⟩
  unfold hasR2
  use DihedralD6.actOnPair g p
  constructor
  · unfold DihedralD6.actOnConfig HMul.hMul instHMul MulAction.toSMul
    simp only [Finset.mem_image]
    exact ⟨p, hp_mem, rfl⟩
  use DihedralD6.actOnPair g q
  constructor
  · unfold DihedralD6.actOnConfig HMul.hMul instHMul MulAction.toSMul
    simp only [Finset.mem_image]
    exact ⟨q, hq_mem, rfl⟩
  constructor
  · -- Los pares transformados son distintos
    intro h_eq
    apply hne
    exact DihedralD6.actOnPair_injective g h_eq
  · exact actOnPair_preserves_r2_pattern g p q h_pattern

/-- Las órbitas preservan la propiedad de ser trivial (sin R1 ni R2) -/
theorem orbit_preserves_trivial (K K' : K3Config) (hK' : K' ∈ Orb(K))
    (hK_no_r1 : ¬hasR1 K) (hK_no_r2 : ¬hasR2 K) : ¬hasR1 K' ∧ ¬hasR2 K' := by
  rw [in_same_orbit_iff] at hK'
  obtain ⟨g, rfl⟩ := hK'
  constructor
  · -- ¬hasR1 (g • K)
    intro h_r1
    -- Si g • K tiene R1, entonces g⁻¹ • (g • K) = K también tiene R1
    have h_r1_K : hasR1 K := by
      have h := actOnConfig_preserves_hasR1 g⁻¹ (g • K) h_r1
      simp only [← mul_smul, inv_mul_cancel, one_smul] at h
      exact h
    exact hK_no_r1 h_r1_K
  · -- ¬hasR2 (g • K)
    intro h_r2
    have h_r2_K : hasR2 K := by
      have h := actOnConfig_preserves_hasR2 g⁻¹ (g • K) h_r2
      simp only [← mul_smul, inv_mul_cancel, one_smul] at h
      exact h
    exact hK_no_r2 h_r2_K

/-! ## Teorema Órbita-Estabilizador -/

/-- Cardinalidad del grupo D₆ -/
lemma card_D6 : Fintype.card DihedralD6 = 12 := DihedralD6.card_eq_12

/-- Teorema órbita-estabilizador: |Orb(K)| × |Stab(K)| = |D₆| = 12 -/
theorem orbit_stabilizer (K : K3Config) :
    (Orb(K)).card * (Stab(K)).card = 12 := by
  -- Definimos la función f: D₆ → Orb(K)
  let f : DihedralD6 → K3Config := fun g => g • K
  
  -- La imagen de f es exactamente Orb(K)
  have h_image : Finset.image f Finset.univ = Orb(K) := by
    ext K'
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    unfold orbit
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
  
  -- Para cada K' en Orb(K), la fibra tiene tamaño |Stab(K)|
  have h_fiber : ∀ K' ∈ Orb(K), 
      (Finset.univ.filter (fun g => f g = K')).card = (Stab(K)).card := by
    intro K' hK'
    rw [in_same_orbit_iff] at hK'
    obtain ⟨h, hh⟩ := hK'
    -- La fibra de K' es h * Stab(K)
    have h_eq : Finset.univ.filter (fun g => f g = K') = 
                Finset.image (fun s => h * s) (Stab(K)) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, 
                 Finset.mem_image, f]
      constructor
      · intro hg
        -- g • K = K' = h • K, entonces h⁻¹ * g ∈ Stab(K)
        use h⁻¹ * g
        constructor
        · unfold stabilizer
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          calc (h⁻¹ * g) • K = h⁻¹ • (g • K) := by rw [mul_smul]
               _ = h⁻¹ • K' := by rw [hg]
               _ = h⁻¹ • (h • K) := by rw [← hh]
               _ = (h⁻¹ * h) • K := by rw [mul_smul]
               _ = K := by simp
        · simp
      · intro ⟨s, hs, hgs⟩
        unfold stabilizer at hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        rw [← hgs]
        calc (h * s) • K = h • (s • K) := by rw [mul_smul]
             _ = h • K := by rw [hs]
             _ = K' := hh
    rw [h_eq]
    -- La imagen tiene el mismo tamaño porque la multiplicación es inyectiva
    exact Finset.card_image_of_injective _ (mul_right_injective h)
  
  -- Usamos la fórmula de conteo: |D₆| = Σ_{K' ∈ Orb(K)} |fibra(K')|
  have h_count : Fintype.card DihedralD6 = 
      ∑ K' ∈ Orb(K), (Finset.univ.filter (fun g => f g = K')).card := by
    rw [← Finset.card_univ]
    conv_lhs => rw [← h_image]
    rw [Finset.card_eq_sum_card_fiberwise]
    · congr 1
      ext K'
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rfl
    · intro g _
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨g, rfl⟩
  
  -- Sustituimos h_fiber
  rw [card_D6] at h_count
  have h_sum : ∑ K' ∈ Orb(K), (Finset.univ.filter (fun g => f g = K')).card = 
               ∑ _ ∈ Orb(K), (Stab(K)).card := by
    apply Finset.sum_congr rfl
    intro K' hK'
    exact h_fiber K' hK'
  rw [h_sum, Finset.sum_const, Finset.card_univ] at h_count
  simp only [smul_eq_mul] at h_count
  linarith

/-- Cálculo de tamaño de órbita a partir del estabilizador -/
theorem orbit_card_from_stabilizer (K : K3Config) (n : ℕ) 
    (hn : 0 < n) (hdiv : n ∣ 12) :
    (Stab(K)).card = n → (Orb(K)).card = 12 / n := by
  intro h_stab
  have h_total := orbit_stabilizer K
  rw [h_stab] at h_total
  omega

/-- Órbita de tamaño 6 si estabilizador tiene 2 elementos -/
theorem orbit_card_6_of_stab_2 (K : K3Config) :
    (Stab(K)).card = 2 → (Orb(K)).card = 6 := 
  orbit_card_from_stabilizer K 2 (by norm_num) (by norm_num)

/-- Órbita de tamaño 4 si estabilizador tiene 3 elementos -/
theorem orbit_card_4_of_stab_3 (K : K3Config) :
    (Stab(K)).card = 3 → (Orb(K)).card = 4 := 
  orbit_card_from_stabilizer K 3 (by norm_num) (by norm_num)

/-- Órbita de tamaño 3 si estabilizador tiene 4 elementos -/
theorem orbit_card_3_of_stab_4 (K : K3Config) :
    (Stab(K)).card = 4 → (Orb(K)).card = 3 := 
  orbit_card_from_stabilizer K 4 (by norm_num) (by norm_num)

/-! ## Órbitas Disjuntas -/

/-- Si K₂ no está en Orb(K₁), entonces las órbitas son disjuntas -/
theorem orbits_disjoint (K₁ K₂ : K3Config) :
    K₂ ∉ Orb(K₁) → Orb(K₁) ∩ Orb(K₂) = ∅ := by
  intro h_not_in
  by_contra h_nonempty
  rw [← Finset.nonempty_iff_ne_empty] at h_nonempty
  obtain ⟨K, hK⟩ := h_nonempty
  rw [Finset.mem_inter] at hK
  obtain ⟨hK_in_1, hK_in_2⟩ := hK
  -- K ∈ Orb(K₁) y K ∈ Orb(K₂)
  rw [in_same_orbit_iff] at hK_in_1 hK_in_2
  obtain ⟨g₁, hg₁⟩ := hK_in_1
  obtain ⟨g₂, hg₂⟩ := hK_in_2
  -- Entonces K₂ = g₂⁻¹ • K = g₂⁻¹ • g₁ • K₁ ∈ Orb(K₁)
  have h_K2_in : K₂ ∈ Orb(K₁) := by
    rw [in_same_orbit_iff]
    use g₂⁻¹ * g₁
    calc (g₂⁻¹ * g₁) • K₁ = g₂⁻¹ • (g₁ • K₁) := by rw [mul_smul]
         _ = g₂⁻¹ • K := by rw [hg₁]
         _ = g₂⁻¹ • (g₂ • K₂) := by rw [← hg₂]
         _ = (g₂⁻¹ * g₂) • K₂ := by rw [mul_smul]
         _ = K₂ := by simp
  exact h_not_in h_K2_in

/-! ## Nota sobre configsNoR1NoR2 -/

/-
NOTA IMPORTANTE:

La definición de `configsNoR1NoR2` ha sido MOVIDA a TCN_06_Representantes.lean.

Esto se hace porque:
1. configsNoR1NoR2 se define naturalmente como la unión de las 3 órbitas
2. Las órbitas dependen de los representantes (specialClass, trefoilKnot, mirrorTrefoil)
3. Los representantes se definen en TCN_06
4. Mover la definición evita dependencias circulares

En TCN_06 se define:
  def configsNoR1NoR2 : Finset K3Config :=
    Orb(specialClass) ∪ Orb(trefoilKnot) ∪ Orb(mirrorTrefoil)

Y se prueban todas las propiedades requeridas.
-/

/-! ## Resumen -/

/-
## Estado del Bloque 5 (Corregido)

✅ **Definiciones completas**:
- `orbit`
- `stabilizer`
- `MulAction` instance

✅ **Teoremas básicos probados**:
- `mem_orbit_self`
- `one_mem_stabilizer`
- `mem_orbit_of_action`
- `in_same_orbit_iff`

✅ **Teoremas avanzados probados**:
- `orbit_stabilizer` (RESUELTO)
- `orbit_card_from_stabilizer` (RESUELTO)
- `orbits_disjoint` (RESUELTO)

✅ **Teoremas de preservación probados**:
- `orbit_preserves_trivial` (NUEVO - requerido por TCN_07)
- `actOnConfig_preserves_hasR1`
- `actOnConfig_preserves_hasR2`

⚠️ **Movido a TCN_06**:
- `configsNoR1NoR2` (para evitar dependencia circular)

## Dependencias
- Requiere: TCN_04_DihedralD6_corregido.lean
- Requerido por: TCN_06, TCN_07
-/

end KnotTheory
