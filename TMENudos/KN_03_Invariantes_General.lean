-- KN_03_Invariantes_General.lean
import TMENudos.KN_00_Fundamentos_General

namespace KnotTheory.General
namespace OrderedPair
variable {n : ℕ}

def gap (p : OrderedPair n) : ℕ := (p.snd - p.fst).val - 1

/-- Predicado: x está estrictamente en el arco u → v -/
def encompasses (p : OrderedPair n) (x : ZMod (2 * n)) : Prop :=
  (x - p.fst).val > 0 ∧ (x - p.fst).val < (p.snd - p.fst).val

instance (p : OrderedPair n) (x : ZMod (2*n)) : Decidable (p.encompasses x) :=
  inferInstance

/-- Signo del par: +1 si la "longitud" (ratio) es impar, -1 si es par. -/
def sign (p : OrderedPair n) : Int :=
  if p.ratio.val % 2 == 1 then 1 else -1

/-- Dos pares están entrelazados si sus extremos se alternan. -/
def isInterlaced (p q : OrderedPair n) : Prop :=
  (p.encompasses q.fst ∧ ¬p.encompasses q.snd) ∨
  (¬p.encompasses q.fst ∧ p.encompasses q.snd)

instance : DecidableRel (@isInterlaced n) :=
  fun p q => inferInstance

end OrderedPair
end KnotTheory.General
