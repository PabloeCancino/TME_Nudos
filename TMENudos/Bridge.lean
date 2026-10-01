import TMENudos.Basic
import TMENudos.Schubert

/-!
# Puente entre Nudos Racionales y Nudos Abstractos

Este archivo conecta las definiciones de nudos racionales (basadas en aritmética modular)
con la teoría general de nudos (basada en diagramas y cocientes).
-/

namespace TMENudos.Bridge

open TMENudos.SchubertTheorems
open TMENudos.Reidemeister.ReidemeisterMoves

/-- **Código de un cruce firmado**: empaqueta (posición superior, posición inferior, signo) en un
    único natural, `(o · 2n + u) · 2 + [pos]`. Es inyectivo (`crossingCode_injective`). -/
def crossingCode {n : ℕ} (c : RationalCrossing n) : ℕ :=
  ((c.over_pos.val * (2 * n) + c.under_pos.val) * 2) + c.pos.toNat

/-- El código de un cruce determina el cruce (posiciones y signo). -/
theorem crossingCode_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (crossingCode (n := n)) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  intro c₁ c₂ h
  have ho₁ : c₁.over_pos.val < 2 * n := ZMod.val_lt _
  have hu₁ : c₁.under_pos.val < 2 * n := ZMod.val_lt _
  have ho₂ : c₂.over_pos.val < 2 * n := ZMod.val_lt _
  have hu₂ : c₂.under_pos.val < 2 * n := ZMod.val_lt _
  unfold crossingCode at h
  have hp : c₁.pos.toNat = c₂.pos.toNat := by
    have h1 : c₁.pos.toNat < 2 := by cases c₁.pos <;> simp
    have h2 : c₂.pos.toNat < 2 := by cases c₂.pos <;> simp
    omega
  have hq : c₁.over_pos.val * (2 * n) + c₁.under_pos.val =
      c₂.over_pos.val * (2 * n) + c₂.under_pos.val := by omega
  have hdiv : c₁.over_pos.val = c₂.over_pos.val := by
    have e1 := Nat.add_mul_div_right c₁.under_pos.val c₁.over_pos.val (by omega : 0 < 2 * n)
    have e2 := Nat.add_mul_div_right c₂.under_pos.val c₂.over_pos.val (by omega : 0 < 2 * n)
    have d1 : c₁.under_pos.val / (2 * n) = 0 := Nat.div_eq_of_lt hu₁
    have d2 : c₂.under_pos.val / (2 * n) = 0 := Nat.div_eq_of_lt hu₂
    have := congrArg (· / (2 * n)) hq
    simp only [Nat.add_comm (c₁.over_pos.val * (2 * n)),
      Nat.add_comm (c₂.over_pos.val * (2 * n))] at this
    rw [e1, e2, d1, d2] at this
    omega
  have hmod : c₁.under_pos.val = c₂.under_pos.val := by
    rw [hdiv] at hq
    omega
  have hb : c₁.pos = c₂.pos := by
    cases h1 : c₁.pos <;> cases h2 : c₂.pos <;> simp_all
  exact RationalCrossing.ext (ZMod.val_injective _ hdiv) (ZMod.val_injective _ hmod) hb

/--
**Construcción de diagramas (ahora una DEFINICIÓN, antes un axioma)**

Convierte una configuración racional en un diagrama del tipo abstracto `Diagram`
(`⟨n, KnotConfig n⟩`). El cruce `i` se guarda en la posición `i` (tanto superior como inferior,
pues `Reidemeister.Crossing n` solo admite posiciones `Fin n`, que no alcanzan a `ZMod (2n)`) y
su información completa (posiciones y signo) se empaqueta, de forma inyectiva, en el campo
`ratio_val : ℚ` con `crossingCode`.

ALCANCE (honesto): esto es una CODIFICACIÓN fiel de los datos (`rational_to_diagram_injective`),
NO una afirmación de que respete los movimientos de Reidemeister: `Reidemeister.apply_R*` siguen
abiertos y esta función no los interpreta. La traducción con significado geométrico
(palabra de Gauss firmada, corchete de Kauffman) vive en la capa paralela `Etapa1_Bridge`.
-/
def rational_to_diagram {n : ℕ} (rc : RationalConfiguration n) : Diagram :=
  ⟨n, ⟨fun i => ⟨i, i, (crossingCode (rc.crossings i) : ℚ)⟩⟩⟩

/-- La codificación es inyectiva: dos configuraciones con el mismo diagrama son iguales. -/
theorem rational_to_diagram_injective {n : ℕ} :
    Function.Injective (rational_to_diagram (n := n)) := by
  intro rc₁ rc₂ h
  have hd := Diagram.mk.inj h
  have hk : (fun i : Fin n => (⟨i, i, (crossingCode (rc₁.crossings i) : ℚ)⟩ :
      Reidemeister.Crossing n)) = fun i => ⟨i, i, (crossingCode (rc₂.crossings i) : ℚ)⟩ := by
    have := hd.2
    simpa [eq_comm] using congrArg Reidemeister.KnotConfig.crossings (eq_of_heq this)
  apply RationalConfiguration.ext
  funext i
  have hi := congrFun hk i
  have hc : (crossingCode (rc₁.crossings i) : ℚ) = (crossingCode (rc₂.crossings i) : ℚ) := by
    simpa using congrArg Reidemeister.Crossing.ratio_val hi
  exact crossingCode_injective i.pos (by exact_mod_cast hc)

/--
**Inyección al Espacio de Nudos**

Todo nudo racional corresponde a un nudo abstracto bien definido (su clase de equivalencia).
-/
noncomputable def rational_to_knot {n : ℕ} (rc : RationalConfiguration n) : Knot :=
  Quotient.mk DiagramSetoid (rational_to_diagram rc)

/--
**Teorema de Consistencia (Axiomático)**

ESTADO (tras definir `rational_to_diagram`): sigue siendo axioma. Con la hipótesis `HEq` el enunciado
es VERDADERO (en el modelo pretendido `HEq rc₁ rc₂` fuerza `n = m` y `rc₁ = rc₂`, y la conclusión es
`refl`), pero Lean no permite deducir `n = m` de la igualdad de tipos `RationalConfiguration n =
RationalConfiguration m` sin un argumento de cardinalidad que no se ha formalizado. Las
equivalencias racionales con contenido (rotación) NO se pueden probar aquí, pues `rotate` no es un
movimiento de `reidemeister_equivalent`.

Si dos configuraciones racionales son equivalentes bajo movimientos de nudos racionales
(que aún no están formalizados como tales en Basic.lean, pero se asumen en la teoría),
entonces sus nudos abstractos correspondientes son isotópicos.
-/
axiom rational_equivalence_preserves_isotopy {n m : ℕ}
  {rc₁ : RationalConfiguration n} {rc₂ : RationalConfiguration m} :
  HEq rc₁ rc₂ → rational_to_knot rc₁ ≅ rational_to_knot rc₂

end TMENudos.Bridge
