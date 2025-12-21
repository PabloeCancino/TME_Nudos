-- TCN_04_DihedralD6.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 4 - Grupo Diédrico D₆

import TMENudos.TCN_01_Fundamentos
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Bloque 4: Grupo Diédrico D₆

Definición del grupo D₆ usando la implementación de Mathlib y acciones sobre configuraciones.

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralGroup
open ZMod
open Finset

/-! ## Definición del Grupo -/

/-- El grupo diédrico D₆ con 12 elementos -/
abbrev DihedralD6 := DihedralGroup 6

namespace DihedralD6

/-! ## Elementos Generadores -/

/-- Rotación básica -/
def rGen : DihedralD6 := DihedralGroup.r 1

/-- Reflexión básica -/
def sGen : DihedralD6 := DihedralGroup.sr 0

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

    La acción estándar del grupo diédrico D₆ sobre los vértices de un hexágono,
    indexados por Z/6Z. Para un elemento g ∈ D₆ representado como r^i * s^j,
    donde r es rotación y s es reflexión:
    - r^i actúa por suma: x + i
    - sr i actúa por: - (x + i) (reflexión de la rotación) -/
def actionZMod (g : DihedralD6) (x : ZMod 6) : ZMod 6 :=
  match g with
  | DihedralGroup.r i => x + i
  | DihedralGroup.sr i => - (x + i)  -- Reflexión seguida de rotación

/-- Teorema: La identidad actúa trivialmente -/
@[simp]
theorem actionZMod_one (x : ZMod 6) : actionZMod (1 : DihedralD6) x = x := by
  rw [DihedralGroup.one_def]
  simp [actionZMod]

/-- Teorema: La acción es homogénea respecto a la multiplicación del grupo -/
theorem actionZMod_mul (g₁ g₂ : DihedralD6) (x : ZMod 6) :
    actionZMod (g₁ * g₂) x = actionZMod g₁ (actionZMod g₂ x) := by
  cases g₁ <;> cases g₂
  · simp [actionZMod, add_assoc, add_comm, add_left_comm]
  · simp [actionZMod, sub_eq_add_neg]
    ring
  · simp [actionZMod, sub_eq_add_neg]
    ring
  · simp [actionZMod, sub_eq_add_neg]
    ring

/-- actionZMod es inyectiva para cada g fijo -/
theorem actionZMod_injective (g : DihedralD6) : Function.Injective (actionZMod g) := by
  intro a b h
  rcases g with (i | i)
  · -- Caso r i: actionZMod es suma por i, que es inyectiva
    simpa [actionZMod] using h
  · -- Caso sr i: actionZMod es i - x, que es inyectiva
    simpa [actionZMod] using h

/-- actionZMod preserva la desigualdad -/
theorem actionZMod_preserves_ne (g : DihedralD6) (a b : ZMod 6) (h : a ≠ b) :
    actionZMod g a ≠ actionZMod g b :=
  Function.Injective.ne (actionZMod_injective g) h

/-- Acción sobre OrderedPair preservando la desigualdad -/
def actOnPair (g : DihedralD6) (p : OrderedPair) : OrderedPair :=
  OrderedPair.mk
    (actionZMod g p.fst)
    (actionZMod g p.snd)
    (actionZMod_preserves_ne g p.fst p.snd p.distinct)

/-- Propiedad de actOnPair para fst -/
@[simp]
theorem actOnPair_fst (g : DihedralD6) (p : OrderedPair) :
    (actOnPair g p).fst = actionZMod g p.fst :=
  rfl

/-- Propiedad de actOnPair para snd -/
@[simp]
theorem actOnPair_snd (g : DihedralD6) (p : OrderedPair) :
    (actOnPair g p).snd = actionZMod g p.snd :=
  rfl

/-- actOnPair es inyectiva para cada g fijo -/
theorem actOnPair_injective (g : DihedralD6) : Function.Injective (actOnPair g) := by
  intro p₁ p₂ h
  -- Usar cases para analizar la estructura OrderedPair (sin @[ext])
  cases' p₁ with fst₁ snd₁ distinct₁
  cases' p₂ with fst₂ snd₂ distinct₂
  -- Simplificar usando las definiciones
  simp [actOnPair] at h ⊢
  -- Obtener las dos igualdades de h
  obtain ⟨h_fst, h_snd⟩ := h
  -- Usar inyectividad de actionZMod
  have h1 : fst₁ = fst₂ := actionZMod_injective g h_fst
  have h2 : snd₁ = snd₂ := actionZMod_injective g h_snd
  exact And.intro h1 h2

@[simp]
theorem actOnPair_one (p : OrderedPair) : actOnPair (1 : DihedralD6) p = p := by
  cases p; simp [actOnPair, actionZMod_one]

/-- La imagen de actOnPair tiene la misma cardinalidad que el original -/
theorem card_image_actOnPair (g : DihedralD6) (s : Finset OrderedPair) :
    (s.image (actOnPair g)).card = s.card :=
  Finset.card_image_of_injective s (actOnPair_injective g)

/-- Acción sobre K3Config -/
def actOnConfig (g : DihedralD6) (K : K3Config) : K3Config :=
  {
    pairs := K.pairs.image (actOnPair g)
    card_eq := by
      rw [card_image_actOnPair]
      exact K.card_eq
    is_partition := by
      intro x
      let y := actionZMod g⁻¹ x
      have hxy : x = actionZMod g y := by
        simp [y, ← actionZMod_mul, mul_inv_cancel, actionZMod_one]
      rcases K.is_partition y with ⟨p, ⟨hp_mem, hy⟩, h_uniq⟩
      refine ⟨actOnPair g p, ?_⟩
      constructor
      · constructor
        · exact Finset.mem_image.mpr ⟨p, hp_mem, rfl⟩
        · simp only [actOnPair_fst, actOnPair_snd]
          rw [hxy]
          rcases hy with (hy | hy)
          · rw [hy]; left; rfl
          · rw [hy]; right; rfl
      · intro q hq
        rcases hq with ⟨hq_mem, hq_x⟩
        rcases Finset.mem_image.mp hq_mem with ⟨p', hp'_mem, rfl⟩
        congr
        apply h_uniq p'
        constructor
        · exact hp'_mem
        · simp only [actOnPair_fst, actOnPair_snd] at hq_x
          rw [hxy] at hq_x
          rcases hq_x with (hx | hx)
          · left; apply actionZMod_injective g; exact hx
          · right; apply actionZMod_injective g; exact hx
  }

/-- Notación para acción -/
notation:70 g " • " K => actOnConfig g K

/-! ## Propiedades de las Acciones -/

/-- La identidad fija todas las configuraciones -/
theorem actOnConfig_id (K : K3Config) : actOnConfig (1 : DihedralD6) K = K := by
  cases K
  simp only [actOnConfig]
  congr
  have : actOnPair (1 : DihedralD6) = id := by
    funext x
    simp [actOnPair_one]
  rw [this, Finset.image_id]

/-- La acción respeta la composición -/
theorem actOnConfig_comp (g₁ g₂ : DihedralD6) (K : K3Config) :
    actOnConfig (g₁ * g₂) K = actOnConfig g₁ (actOnConfig g₂ K) := by
  simp only [actOnConfig]
  congr 1
  ext p
  simp only [Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨q, hq, rfl⟩
    refine ⟨actOnPair g₂ q, ?_, ?_⟩
    · refine ⟨q, hq, rfl⟩
    · simp [actOnPair, actionZMod_mul]
  · intro h
    rcases h with ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨q, hq, ?_⟩
    simp [actOnPair, actionZMod_mul]

/-- La acción de D₆ sobre K3Config es una acción de grupo -/
instance : MulAction DihedralD6 K3Config where
  smul := actOnConfig
  one_smul := actOnConfig_id
  mul_smul := actOnConfig_comp

/-!
## Resumen

✅ **Grupo D₆**: Via Mathlib
✅ **12 elementos**: `card_eq_12`
✅ **Generadores**: `rGen`, `sGen`
✅ **Acciones**: Completamente implementadas
✅ **Propiedades**:
    - `actionZMod`: Acción sobre ZMod 6
    - `actOnPair`: Acción sobre pares ordenados
    - `actOnConfig`: Acción sobre configuraciones K₃
    - Instancia `MulAction`: Verifica que es una acción de grupo válida

## Teoremas Principales

1. `actionZMod_one`: La identidad actúa trivialmente
2. `actionZMod_mul`: La acción es homogénea
3. `actOnConfig_id`: La identidad fija configuraciones
4. `actOnConfig_comp`: Compatibilidad con composición

## Próximos Pasos

La implementación está completa y lista para usarse en el estudio de simetrías
de configuraciones K₃ bajo el grupo diédrico D₆.
-/

end DihedralD6
end KnotTheory
