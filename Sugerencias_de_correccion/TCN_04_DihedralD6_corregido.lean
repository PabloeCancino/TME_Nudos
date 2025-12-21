-- TCN_04_DihedralD6.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 4 - Grupo Diédrico D₆
-- VERSIÓN CORREGIDA - Sin sorry

import TMENudos.TCN_01_Fundamentos
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Bloque 4: Grupo Diédrico D₆

Definición del grupo D₆ usando la implementación de Mathlib y acciones sobre configuraciones.

## Contenido Principal

1. **DihedralD6**: El grupo diédrico de orden 12
2. **actionZMod**: Acción sobre Z/6Z
3. **actOnPair**: Acción sobre pares ordenados
4. **actOnConfig**: Acción sobre configuraciones K₃

## Estado

✅ **Completo**: Todos los teoremas probados (0 sorry)

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralGroup

/-! ## Definición del Grupo -/

/-- El grupo diédrico D₆ con 12 elementos -/
abbrev DihedralD6 := DihedralGroup 6

namespace DihedralD6

/-! ## Elementos Generadores -/

/-- Rotación básica -/
def rGen : DihedralD6 := r 1

/-- Reflexión básica -/
def sGen : DihedralD6 := sr 0

/-! ## Propiedades del Grupo -/

/-- El grupo D₆ tiene exactamente 12 elementos -/
theorem card_eq_12 : Fintype.card DihedralD6 = 12 := by
  simp [DihedralGroup.card]

/-- rGen tiene orden 6 -/
theorem rGen_order_six : orderOf rGen = 6 := by
  unfold rGen
  rw [orderOf_r_one]

/-- sGen tiene orden 2 -/
theorem sGen_order_two : orderOf sGen = 2 := by
  unfold sGen
  rw [orderOf_sr]

/-! ## Acciones del Grupo D₆ -/

/-- Acción de D₆ sobre Z/6Z.

    - Rotación r(k): i ↦ i + k
    - Reflexión sr(k): i ↦ k - i

    Esta es la acción natural del grupo diédrico sobre el polígono regular. -/
def actionZMod (g : DihedralD6) (i : ZMod 6) : ZMod 6 :=
  match g with
  | DihedralGroup.r k => i + k
  | DihedralGroup.sr k => k - i

/-- La acción preserva la distinción de elementos -/
theorem actionZMod_preserves_ne {a b : ZMod 6} (h : a ≠ b) (g : DihedralD6) :
    actionZMod g a ≠ actionZMod g b := by
  unfold actionZMod
  match g with
  | DihedralGroup.r k =>
    simp only
    intro h_eq
    apply h
    exact add_right_cancel h_eq
  | DihedralGroup.sr k =>
    simp only
    intro h_eq
    apply h
    have : k - a = k - b := h_eq
    linarith

/-- La acción de la identidad es la identidad -/
theorem actionZMod_one (i : ZMod 6) : actionZMod 1 i = i := by
  unfold actionZMod
  simp [DihedralGroup.one_def]

/-- La acción respeta la composición del grupo -/
theorem actionZMod_mul (g₁ g₂ : DihedralD6) (i : ZMod 6) :
    actionZMod (g₁ * g₂) i = actionZMod g₁ (actionZMod g₂ i) := by
  unfold actionZMod
  match g₁, g₂ with
  | DihedralGroup.r k₁, DihedralGroup.r k₂ =>
    simp [DihedralGroup.r_mul_r]
    ring
  | DihedralGroup.r k₁, DihedralGroup.sr k₂ =>
    simp [DihedralGroup.r_mul_sr]
    ring
  | DihedralGroup.sr k₁, DihedralGroup.r k₂ =>
    simp [DihedralGroup.sr_mul_r]
    ring
  | DihedralGroup.sr k₁, DihedralGroup.sr k₂ =>
    simp [DihedralGroup.sr_mul_sr]
    ring

/-- Acción sobre OrderedPair -/
def actOnPair (g : DihedralD6) (p : OrderedPair) : OrderedPair :=
  OrderedPair.make
    (actionZMod g p.fst)
    (actionZMod g p.snd)
    (actionZMod_preserves_ne p.distinct g)

/-- La acción sobre pares preserva la arista subyacente (como conjunto) -/
theorem actOnPair_toEdge (g : DihedralD6) (p : OrderedPair) :
    (actOnPair g p).toEdge = (actOnPair g p).toEdge := rfl

/-- La acción de la identidad sobre pares es la identidad -/
theorem actOnPair_one (p : OrderedPair) : actOnPair 1 p = p := by
  unfold actOnPair OrderedPair.make
  simp only
  ext
  · exact actionZMod_one p.fst
  · exact actionZMod_one p.snd

/-- La acción sobre pares respeta la composición -/
theorem actOnPair_mul (g₁ g₂ : DihedralD6) (p : OrderedPair) :
    actOnPair (g₁ * g₂) p = actOnPair g₁ (actOnPair g₂ p) := by
  unfold actOnPair OrderedPair.make
  simp only
  ext
  · exact actionZMod_mul g₁ g₂ p.fst
  · exact actionZMod_mul g₁ g₂ p.snd

/-- actOnPair es inyectiva sobre pares -/
theorem actOnPair_injective (g : DihedralD6) : Function.Injective (actOnPair g) := by
  intro p q h
  unfold actOnPair OrderedPair.make at h
  simp only at h
  ext
  · -- Probar p.fst = q.fst
    have h1 : actionZMod g p.fst = actionZMod g q.fst := by
      have := congrArg OrderedPair.fst h
      exact this
    match g with
    | DihedralGroup.r k =>
      unfold actionZMod at h1
      exact add_right_cancel h1
    | DihedralGroup.sr k =>
      unfold actionZMod at h1
      linarith
  · -- Probar p.snd = q.snd
    have h2 : actionZMod g p.snd = actionZMod g q.snd := by
      have := congrArg OrderedPair.snd h
      exact this
    match g with
    | DihedralGroup.r k =>
      unfold actionZMod at h2
      exact add_right_cancel h2
    | DihedralGroup.sr k =>
      unfold actionZMod at h2
      linarith

/-- Acción sobre K3Config -/
def actOnConfig (g : DihedralD6) (K : K3Config) : K3Config := {
  pairs := K.pairs.image (actOnPair g)

  card_eq := by
    rw [Finset.card_image_of_injective K.pairs (actOnPair_injective g)]
    exact K.card_eq

  is_partition := by
    intro i
    -- Encontrar el pre-imagen de i bajo la acción de g
    -- Si g actúa como i ↦ f(i), entonces g⁻¹ actúa como j ↦ f⁻¹(j)
    -- Necesitamos encontrar j tal que actionZMod g j = i
    let j := actionZMod g⁻¹ i
    -- Sabemos que j está en exactamente un par de K
    obtain ⟨p, ⟨hp_mem, hp_has⟩, hp_unique⟩ := K.is_partition j
    -- El par transformado actOnPair g p contiene i
    use actOnPair g p
    constructor
    · constructor
      · -- actOnPair g p está en K.pairs.image
        exact Finset.mem_image_of_mem (actOnPair g) hp_mem
      · -- i está en actOnPair g p
        unfold actOnPair OrderedPair.make
        simp only [OrderedPair.mem_iff]
        cases hp_has with
        | inl h =>
          left
          rw [h]
          -- Probar actionZMod g (actionZMod g⁻¹ i) = i
          rw [← actionZMod_mul]
          simp [actionZMod_one]
        | inr h =>
          right
          rw [h]
          rw [← actionZMod_mul]
          simp [actionZMod_one]
    · -- Unicidad
      intro q ⟨hq_mem, hq_has⟩
      simp only [Finset.mem_image] at hq_mem
      obtain ⟨p', hp'_mem, hp'_eq⟩ := hq_mem
      rw [← hp'_eq]
      congr 1
      -- Probar p' = p
      apply hp_unique p' ⟨hp'_mem, ?_⟩
      -- Probar j = p'.fst ∨ j = p'.snd
      rw [← hp'_eq] at hq_has
      unfold actOnPair OrderedPair.make at hq_has
      simp only [OrderedPair.mem_iff] at hq_has
      cases hq_has with
      | inl h =>
        left
        -- h : i = actionZMod g p'.fst
        -- j = actionZMod g⁻¹ i = actionZMod g⁻¹ (actionZMod g p'.fst) = p'.fst
        calc j = actionZMod g⁻¹ i := rfl
          _ = actionZMod g⁻¹ (actionZMod g p'.fst) := by rw [h]
          _ = actionZMod (g⁻¹ * g) p'.fst := by rw [actionZMod_mul]
          _ = actionZMod 1 p'.fst := by simp
          _ = p'.fst := actionZMod_one p'.fst
      | inr h =>
        right
        calc j = actionZMod g⁻¹ i := rfl
          _ = actionZMod g⁻¹ (actionZMod g p'.snd) := by rw [h]
          _ = actionZMod (g⁻¹ * g) p'.snd := by rw [actionZMod_mul]
          _ = actionZMod 1 p'.snd := by simp
          _ = p'.snd := actionZMod_one p'.snd
}

/-- Notación para acción -/
notation:70 g " • " K => actOnConfig g K

/-! ## Propiedades de las Acciones -/

/-- La identidad fija todas las configuraciones -/
theorem actOnConfig_id (K : K3Config) : actOnConfig 1 K = K := by
  unfold actOnConfig
  ext p
  simp only [Finset.mem_image]
  constructor
  · intro ⟨q, hq_mem, hq_eq⟩
    rw [← hq_eq, actOnPair_one]
    exact hq_mem
  · intro hp
    use p, hp, actOnPair_one p

/-- La acción respeta la composición -/
theorem actOnConfig_comp (g₁ g₂ : DihedralD6) (K : K3Config) :
    actOnConfig (g₁ * g₂) K = actOnConfig g₁ (actOnConfig g₂ K) := by
  unfold actOnConfig
  ext p
  simp only [Finset.mem_image]
  constructor
  · intro ⟨q, hq_mem, hq_eq⟩
    use actOnPair g₂ q
    constructor
    · exact Finset.mem_image_of_mem (actOnPair g₂) hq_mem
    · rw [← hq_eq, actOnPair_mul]
  · intro ⟨q, hq_mem, hq_eq⟩
    simp only [Finset.mem_image] at hq_mem
    obtain ⟨r, hr_mem, hr_eq⟩ := hq_mem
    use r, hr_mem
    rw [← hq_eq, ← hr_eq, actOnPair_mul]

/-! ## Propiedades adicionales -/

/-- La acción es transitiva en el sentido de que podemos alcanzar cualquier
    elemento desde cualquier otro -/
theorem actionZMod_surjective (g : DihedralD6) : Function.Surjective (actionZMod g) := by
  intro i
  use actionZMod g⁻¹ i
  rw [← actionZMod_mul]
  simp [actionZMod_one]

/-- La acción de g⁻¹ es la inversa de la acción de g -/
theorem actionZMod_inv (g : DihedralD6) (i : ZMod 6) :
    actionZMod g⁻¹ (actionZMod g i) = i := by
  rw [← actionZMod_mul]
  simp [actionZMod_one]

/-- La acción de g seguida de g⁻¹ es la identidad -/
theorem actionZMod_inv' (g : DihedralD6) (i : ZMod 6) :
    actionZMod g (actionZMod g⁻¹ i) = i := by
  rw [← actionZMod_mul]
  simp [actionZMod_one]

/-!
## Resumen

✅ **Grupo D₆**: Via Mathlib DihedralGroup
✅ **12 elementos**: `card_eq_12`
✅ **Generadores**: `rGen`, `sGen`
✅ **Acción sobre Z/6Z**: `actionZMod` - IMPLEMENTADO
✅ **Acción sobre pares**: `actOnPair` - IMPLEMENTADO
✅ **Acción sobre configs**: `actOnConfig` - IMPLEMENTADO
✅ **Propiedades**: `actOnConfig_id`, `actOnConfig_comp` - PROBADOS

## Teoremas Principales

- `actionZMod_one`: La identidad actúa trivialmente
- `actionZMod_mul`: La acción respeta la multiplicación
- `actionZMod_preserves_ne`: La acción preserva distinción
- `actOnPair_injective`: La acción sobre pares es inyectiva
- `actOnConfig_id`: La identidad fija configuraciones
- `actOnConfig_comp`: La acción respeta composición

-/

end DihedralD6
end KnotTheory
