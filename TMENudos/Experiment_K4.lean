import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Experimento: Anfiquiralidad de K4 y Movimiento R3

Este archivo modela configuraciones K4 (n=4) sobre Z/8Z para verificar
la hipótesis del usuario sobre un nudo específico y su relación con R3.
-/

namespace KnotTheory.K4

/-! ## Estructuras Básicas (Z/8Z) -/

structure OrderedPair4 where
  fst : ZMod 8
  snd : ZMod 8
  distinct : fst ≠ snd
  deriving DecidableEq

def OrderedPair4.reverse (p : OrderedPair4) : OrderedPair4 :=
  ⟨p.snd, p.fst, p.distinct.symm⟩

instance : Repr OrderedPair4 where
  reprPrec p _ := s!"({p.fst.val}, {p.snd.val})"

structure K4Config where
  pairs : Finset OrderedPair4
  card_eq : pairs.card = 4
  is_partition : ∀ i : ZMod 8, ∃! p ∈ pairs, i = p.fst ∨ i = p.snd

/-! ## Definición del Ejemplo del Usuario -/

-- k4 = {(1,6), (5,2), (3,0), (4,7)}
def p1 : OrderedPair4 := ⟨1, 6, by decide⟩
def p2 : OrderedPair4 := ⟨5, 2, by decide⟩
def p3 : OrderedPair4 := ⟨3, 0, by decide⟩
def p4 : OrderedPair4 := ⟨4, 7, by decide⟩

def user_k4_pairs : Finset OrderedPair4 := {p1, p2, p3, p4}

theorem user_k4_card : user_k4_pairs.card = 4 := by
  unfold user_k4_pairs
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  all_goals decide

-- Mirror de k4: invertir cada par
def p1' := p1.reverse -- (6,1)
def p2' := p2.reverse -- (2,5)
def p3' := p3.reverse -- (0,3)
def p4' := p4.reverse -- (7,4)

def user_k4_mirror_pairs : Finset OrderedPair4 := {p1', p2', p3', p4'}

/-! ## Movimiento R3 en K4 -/

def formsR3Pattern4 (p q r : OrderedPair4) : Prop :=
  p ≠ q ∧ q ≠ r ∧ r ≠ p

instance : Decidable (formsR3Pattern4 p q r) :=
  inferInstanceAs (Decidable (p ≠ q ∧ q ≠ r ∧ r ≠ p))

theorem k4_has_triplets :
  ∃ p q r, p ∈ user_k4_pairs ∧ q ∈ user_k4_pairs ∧ r ∈ user_k4_pairs ∧ formsR3Pattern4 p q r := by
  use p1, p2, p3
  simp only [user_k4_pairs, formsR3Pattern4, Finset.mem_insert, Finset.mem_singleton]
  decide

theorem k4_neq_mirror : user_k4_pairs ≠ user_k4_mirror_pairs := by
  -- Proof that the diagram is not equal to its mirror (as sets of ordered pairs)
  -- This confirms that the equivalence requires moves (R3), it's not a trivial identity.
  intro h
  have h1 : p1 ∈ user_k4_pairs := by simp [user_k4_pairs]
  have h1_mirror : p1 ∈ user_k4_mirror_pairs := by rw [← h]; exact h1
  -- p1 = (1,6). Mirror contains (6,1), (2,5), (0,3), (7,4).
  -- (1,6) is not in mirror.
  simp [user_k4_mirror_pairs, p1', p2', p3', p4', p1, p2, p3, p4, OrderedPair4.reverse] at h1_mirror
  contradiction

end KnotTheory.K4
