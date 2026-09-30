/-
09b_r3_hipotesis.lean -- (b) Las hipotesis de `bracket_r3` no son vacias:
  * `validR3` es satisfacible y exactamente 48 de los 64 patrones (o, s) lo cumplen;
  * `tri` recibe un diagrama concreto (el trebol, 6 letras) y tres aristas distintas
    (`e = ![0, 2, 4]`, inyectiva), y `bracket_r3` se aplica a ese caso.
-/
import TMENudos.Etapa1_R3

open TMENudos.Invariancia TMENudos.Invariancia.R3

-- validR3 satisfacible / rechaza las alturas ciclicas
example : validR3 false false false false false true = true := by decide
example : validR3 false true true true false true = true := by decide
example : validR3 true true true true false false = true := by decide
example : validR3 false false false false false false = false := by decide
example : validR3 true true true true true true = false := by decide

-- exactamente 48 de 64 patrones
example : ((List.finRange 64).filter fun n =>
    validR3 (n.val % 2 == 1) (n.val / 2 % 2 == 1) (n.val / 4 % 2 == 1)
      (n.val / 8 % 2 == 1) (n.val / 16 % 2 == 1) (n.val / 32 % 2 == 1)).length = 48 := by decide

/-- El trebol como `GDiag (Fin 6)`: palabra `1 2 3 1 2 3` con `1,3,5` arriba (alternante). -/
def trebol : GDiag (Fin 6) where
  next := Equiv.addRight 1
  partner i := i + 3
  ovr i := i.val % 2 == 0
  sign _ := true
  partner_partner := by decide
  partner_ne := by decide
  ovr_partner := by decide
  sign_partner := by decide
  free := 0

/-- Tres aristas distintas del trebol. -/
def e3 : Fin 3 → Fin 6 := ![0, 2, 4]

theorem e3_inj : Function.Injective e3 := by decide

theorem instancia (A : ℚ) (hA : A ≠ 0) (ovc : Fin 3 → Bool) :
    (GDiag.tri trebol e3 e3_inj ![false, true, false] ovc ![true, false, false]).bracket A =
    (GDiag.tri trebol e3 e3_inj (fun i => !(![false, true, false] : Fin 3 → Bool) i) ovc
      ![true, false, false]).bracket A :=
  GDiag.bracket_r3 trebol e3 e3_inj _ ovc _ A hA (by decide)
