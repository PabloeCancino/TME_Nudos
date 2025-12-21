-- KN_Examples.lean
-- Ejemplos Concretos de Configuraciones Kₙ

import TMENudos.KN_General

/-!
# Ejemplos de Configuraciones Kₙ

Este archivo demuestra el uso del framework general `KN_General.lean` con
ejemplos concretos de nudos de 3, 4 y 5 cruces.

## Contenido

1. **Nudos K₃** (3 cruces): Trébol y su espejo
2. **Nudos K₄** (4 cruces): k_4_1 y k_4_2 desde BD_Nudos
3. **Helpers**: Funciones para constructorstruir configuraciones desde listas

-/

open KnotTheory.General

/-! ## Funciones Helper -/

/-- Crea un OrderedPairN desde dos valores explícitos -/
def mkPairN (n : ℕ) (a b : Fin (2 * n)) (ha b : a.val ≠ b.val) : OrderedPairN n :=
  let za : ZMod (2 * n) := ⟨a.val, by
    have : a.val < 2 * n := a.isLt
    exact this⟩
  let zb : ZMod (2 * n) := ⟨b.val, by
    have : b.val < 2 * n := b.isLt
    exact this⟩
  ⟨za, zb, by
    intro heq
    have : a.val = b.val := by
      have ha_eq : za.val = a.val := rfl
      have hb_eq : zb.val = b.val := rfl
      calc a.val = za.val := ha_eq.symm
           _ = zb.val := by rw [heq]
           _ = b.val := hb_eq
    exact hab this⟩

/-! ## Ejemplos K₃: Nudos de 3 Cruces -/

section K3_Examples

/-- Trébol derecho: configuración [[1,4],[5,2],[3,0]] en Z/6Z

    DME = [3,-3,-3]
    Quiralidad: RightHanded
-/
example_k3_trefoil_right : K3Config := sorry
  -- TODO: Implementar constructor desde pares ordenados

/-- Trébol izquierdo: espejo del trébol derecho

    DME = [-3,3,3]
    Quiralidad: LeftHanded
-/
example : K3Config := KnConfig.mirror example_k3_trefoil_right

end K3_Examples

/-! ## Ejemplos K₄: Nudos de 4 Cruces -/

section K4_Examples

/-- k_4_1: configuración [[1,4],[7,2],[3,6],[5,0]] en Z/8Z

    Según BD_Nudos/configuraciones_nudos.json:
    - num_cruces: 4
    - configuracion_Racional: [[1,4],[7,2],[3,6],[5,0]]
    - DME_reportado: [3,3,3,3]
-/
def k_4_1 : K4Config := sorry
  -- TODO: Construir desde la configuración JSON

/-- k_4_2: configuración [[4,1],[2,7],[6,3],[0,5]] en Z/8Z

    Según BD_Nudos/configuraciones_nudos.json:
    - num_cruces: 4
    - configuracion_racional: [[4,1],[2,7],[6,3],[0,5]]
    - DME_reportado: [5,5,5,5]

    **Nota:** Esta es la configuración espejo de k_4_1
-/
def k_4_2 : K4Config := sorry
  -- TODO: Construir desde la configuración JSON

/-- Verificación: k_4_2 es el espejo de k_4_1 -/
example : k_4_2 = KnConfig.mirror k_4_1 := by sorry

end K4_Examples

/-! ## Tests de Invariantes -/

section Invariant_Tests

-- Verificar DME de k_4_1
#check k_4_1.dme
example_ k_4_1_dme : k_4_1.dme.length = 4 := by sorry

-- Verificar Writhe
#check k_4_1.writhe
example : k_4_1.writhe ≠ 0 := by sorry  -- Confirma quiralidad

-- Verificar IME es invariante bajo mirror
example (K : K4Config) : (KnConfig.mirror K).ime = K.ime := by sorry

end Invariant_Tests

/-! ## Verificación de Compilación -/

#check K3Config  -- Tipo: Type := KnConfig 3
#check K4Config  -- Tipo: Type := KnConfig 4
#check K5Config  -- Tipo: Type := KnConfig 5

#check @KnConfig.dme     -- Funciona para cualquier n
#check @KnConfig.mirror  -- Funciona para cualquier n
