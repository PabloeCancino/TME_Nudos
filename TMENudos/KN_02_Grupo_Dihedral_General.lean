-- KN_02_Grupo_Dihedral_General.lean
-- Acción del Grupo Dihedral D_2n sobre Configuraciones K_n
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Enero 9, 2026

import TMENudos.KN_00_Fundamentos_General
import Mathlib.GroupTheory.GroupAction.Defs

namespace KnotTheory.General

/-!
# Acción del Grupo Dihedral D₂ₙ

Este módulo define la acción del grupo Dihedral de orden 4n (D₂ₙ) sobre
las configuraciones K_n.
-/

namespace OrderedPair

variable {n : ℕ}

/-- Reflexión geométrica de un par (i ↦ -i) -/
def mirror (p : OrderedPair n) : OrderedPair n :=
  ⟨-p.fst, -p.snd, by
    intro h
    have : p.fst = p.snd := by
      rw [neg_inj] at h
      exact h
    exact p.distinct this⟩

/-- La reflexión geométrica es involutiva -/
@[simp]
theorem mirror_mirror (p : OrderedPair n) : p.mirror.mirror = p := by
  cases p
  simp [mirror]

/-- La reflexión no afecta la "distancia" pero invierte el signo de la razón -/
theorem ratio_mirror (p : OrderedPair n) : p.mirror.ratio = -p.ratio := by
  unfold mirror ratio
  simp
  ring

attribute [ext] OrderedPair

theorem mirror_rotate (p : OrderedPair n) (k : ZMod (2 * n)) :
    (p.rotate k).mirror = p.mirror.rotate (-k) := by
  ext <;> simp [rotate, mirror, add_comm]

end OrderedPair

namespace KnConfig

variable {n : ℕ}

/-- Reflexión geométrica de una configuración -/
def mirror (K : KnConfig n) : KnConfig n where
  pairs := K.pairs.image OrderedPair.mirror
  card_eq := by
    rw [Finset.card_image_of_injective]
    · exact K.card_eq
    · intro p₁ p₂ h
      cases p₁; cases p₂
      simp only [OrderedPair.mirror] at h
      injection h with h1 h2
      rw [neg_inj] at h1 h2
      subst h1; subst h2
      rfl
  coverage := by
    intro i
    obtain ⟨p, hp, h⟩ := K.coverage (-i)
    use p.mirror
    constructor
    · exact Finset.mem_image_of_mem _ hp
    · cases h with
      | inl h => left; simp [OrderedPair.mirror, h]
      | inr h => right; simp [OrderedPair.mirror, h]

/-- La reflexión geométrica es involutiva -/
@[simp]
theorem mirror_mirror (K : KnConfig n) : K.mirror.mirror = K := by
  rw [ext_iff]
  simp only [mirror]
  ext p
  simp only [Finset.mem_image]
  constructor
  · intro ⟨q, ⟨r, hr, hrq⟩, hqp⟩
    rw [← hrq, OrderedPair.mirror_mirror] at hqp
    rw [← hqp]
    exact hr
  · intro hp
    exact ⟨p.mirror, ⟨p, hp, rfl⟩, OrderedPair.mirror_mirror p⟩

theorem mirror_rotate_mirror (K : KnConfig n) (k : ZMod (2 * n)) :
    (K.rotate k).mirror = (K.mirror).rotate (-k) := by
  rw [ext_iff]
  simp only [rotate, mirror]
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro p _
  exact OrderedPair.mirror_rotate p k

theorem mirror_rotate_eq_rotate_neg_mirror (K : KnConfig n) (k : ZMod (2 * n)) :
    (K.rotate k).mirror = (K.mirror).rotate (-k) := mirror_rotate_mirror K k

end KnConfig

end KnotTheory.General
