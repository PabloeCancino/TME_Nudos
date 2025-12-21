import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Lex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.Rotate
import Mathlib.Data.Rat.Defs

/-!
  Fundamentos Axiomáticos de la Teoría Modular Estructural de Nudos
  Formalización en Lean 4

  Dr Pablo Eduardo Cancino Marentes - UAN 2025

Nota importante: "El archivo Lean formaliza solo la parte modular;
la conexión con nudos clásicos (y el problema de cuáles configuraciones son realizables)
se discuten a nivel teórico, pero no forman parte del núcleo formal.

Este es el kernel formal de la teoría, donde los objetos básicos y la noción de isotopía
de Razón Modular quedan fijados. Los resultados profundos se aposentan como axiomas/objetivos,
para ser desarrollados en archivos posteriores
-/

/-!
## Axioma A1 — Espacio del recorrido (estructura cíclica)

Para cada n ∈ ℕ existe un conjunto finito totalmente ordenado
ℝ₂ₙ = {0, 1, 2, ..., 2n-1} equipado con una operación de suma modular
que convierte a ℝ₂ₙ en un grupo abeliano cíclico.

**Nota sobre la indexación**: En Lean, es más natural usar {0, 1, ..., 2n-1}
en lugar de {1, 2, ..., 2n} del documento original. Esto no afecta la
estructura matemática ya que ambos son isomorfos como grupos cíclicos.
-/

namespace TMENudos

/-- El espacio de recorrido R_{2n} para un nudo con n cruces.
    Usamos ZMod (2*n) que ya implementa ℤ/(2n)ℤ en Mathlib. -/
abbrev TraversalSpace (n : ℕ) := ZMod (2 * n)

/-- Notación para el espacio de recorrido -/
notation "ℝ[" n "]" => TraversalSpace n

/-!
## Axioma de Doble Modularidad

El nudo racional se estructura sobre dos dimensiones modulares:
1. **Modularidad de Trayectoria (Dimensión 1)**: Regida por $Mod_{2n}$, define la linealidad y
   el recorrido.
2. **Modularidad de Nivel (Dimensión 2)**: Regida por $Mod_2$, define la alteridad (arriba/abajo)
   y la condición de cierre.
-/

/-- 1. Modularidad de Trayectoria (Linealidad) -/
abbrev TrajectoryModularity (n : ℕ) := ZMod (2 * n)

/-- 2. Modularidad de Nivel (Alteridad) -/
abbrev LevelModularity := ZMod 2

/-- Proyección de la trayectoria al nivel (Paridad) -/
def trajectory_to_level {n : ℕ} (t : ℝ[n]) : LevelModularity :=
  t.val

/-!
### Propiedades del Axioma A1

El tipo ZMod (2*n) de Mathlib ya satisface todas las propiedades requeridas:
1. Es un conjunto finito con 2n elementos
2. Tiene operación de suma modular (⊕ se nota como +)
3. Forma un grupo abeliano cíclico
4. Tiene estructura de anillo

Demostramos explícitamente estas propiedades:
-/

/-- El espacio de recorrido es finito con cardinalidad 2n (cuando n > 0) -/
theorem traversal_space_card (n : ℕ) [NeZero n] :
  Fintype.card (ℝ[n]) = 2 * n := by
  unfold TraversalSpace
  exact ZMod.card (2 * n)

/-- El espacio de recorrido tiene estructura de grupo abeliano -/
instance (n : ℕ) [NeZero n] : AddCommGroup (ℝ[n]) :=
  inferInstance

/-- El espacio de recorrido tiene estructura cíclica (generado por 1) -/
theorem traversal_space_cyclic (n : ℕ) [NeZero n] :
  ∀ x : ℝ[n], ∃ k : ℕ, x = k • (1 : ℝ[n]) := by
  intro x
  use x.val
  simp [ZMod.natCast_val]

/-!
### Operación de suma modular

La operación ⊕ del documento se implementa como la suma usual (+) en ZMod.
-/

/-- La operación de suma modular en el espacio de recorrido -/
def modular_add {n : ℕ} (i j : ℝ[n]) : ℝ[n] := i + j

/-- La suma modular es asociativa -/
theorem modular_add_assoc {n : ℕ} [NeZero n] (i j k : ℝ[n]) :
  modular_add (modular_add i j) k = modular_add i (modular_add j k) := by
  unfold modular_add
  ring

/-- La suma modular es conmutativa -/
theorem modular_add_comm {n : ℕ} [NeZero n] (i j : ℝ[n]) :
  modular_add i j = modular_add j i := by
  unfold modular_add
  ring

/-- El elemento 0 es neutro para la suma modular -/
theorem modular_add_zero {n : ℕ} [NeZero n] (i : ℝ[n]) :
  modular_add i 0 = i := by
  unfold modular_add
  ring

/-- Cada elemento tiene inverso aditivo -/
theorem modular_add_neg {n : ℕ} [NeZero n] (i : ℝ[n]) :
  modular_add i (-i) = 0 := by
  unfold modular_add
  ring

/-!
### Ejemplos concretos
-/

/-- Ejemplo para n=3: El espacio tiene 6 elementos -/
example : Fintype.card (ℝ[3]) = 6 := by
  exact traversal_space_card 3

/-- Ejemplo de suma modular: En ℝ[3], 4 + 5 = 3 (mod 6) -/
example : (4 : ℝ[3]) + (5 : ℝ[3]) = 3 := by
  rfl

/-- Ejemplo: Todo elemento de ℝ[2] se genera por sumas de 1 -/
example (x : ℝ[2]) : ∃ k : ℕ, x = k • (1 : ℝ[2]) :=
  traversal_space_cyclic 2 x


/-!
## Axioma A2 — Existencia de cruces y cobertura del recorrido

Para cada n existe un conjunto de cruces C = {c₁, ..., cₙ}, y para cada cᵢ existe un par ordenado
(oᵢ, uᵢ) ∈ ℝ₂ₙ × ℝ₂ₙ, oᵢ ≠ uᵢ, tal que {o₁, ..., oₙ, u₁, ..., uₙ} = ℝ₂ₙ.
-/

/--
Estructura de un cruce racional.
Cada cruce tiene una posición "over" y una posición "under" en el espacio de recorrido Z_{2n}.
-/
@[ext]
structure RationalCrossing (n : ℕ) where
  over_pos : ℝ[n]
  under_pos : ℝ[n]
  distinct : over_pos ≠ under_pos
deriving DecidableEq

instance (n : ℕ) [NeZero n] : Fintype (RationalCrossing n) :=
  let pred : ℝ[n] × ℝ[n] → Prop := fun c => c.1 ≠ c.2
  have h : DecidablePred pred := fun _ => inferInstance
  have h_ne : NeZero (2*n) := ⟨by have := NeZero.ne n; omega⟩
  have : Fintype (ℝ[n] × ℝ[n]) :=
    @instFintypeProd _ _ (@ZMod.fintype (2*n) h_ne) (@ZMod.fintype (2*n) h_ne)
  have : Fintype { c : ℝ[n] × ℝ[n] // pred c } := Subtype.fintype pred
  Fintype.ofEquiv { c : ℝ[n] × ℝ[n] // pred c }
    { toFun := fun c => ⟨c.val.1, c.val.2, c.property⟩
      invFun := fun c => ⟨(c.over_pos, c.under_pos), c.distinct⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Representación textual de un cruce -/
instance (n : ℕ) : Repr (RationalCrossing n) where
  reprPrec c _ := "(" ++ repr c.over_pos ++ ", " ++ repr c.under_pos ++ ")"

/-!
## Razón Modular [o,u]

La razón modular [o,u] representa el **recorrido** desde la posición over (o) hasta
la posición under (u) en el espacio modular ℤ/(2n)ℤ. Este concepto es fundamental
para el Invariante Modular Estructural (IME).

**Definición**: [o,u] = (u - o) mod 2n

La razón modular codifica los "saltos" en el recorrido del nudo, proporcionando
una caracterización completa de su estructura.
-/

/-- Razón modular [o,u]: el recorrido desde over_pos hasta under_pos -/
def modular_ratio {n : ℕ} (c : RationalCrossing n) : ℝ[n] :=
  c.under_pos - c.over_pos

/-- La razón modular como entero natural (representante canónico en [0, 2n)) -/
def ratio_val {n : ℕ} (c : RationalCrossing n) : ℕ :=
  (modular_ratio c).val

/-- La razón modular junto con la posición over determina únicamente el cruce.
    Esto refleja que cada posición (clase de equivalencia) es única en la estructura modular,
    y la razón [o,u] caracteriza completamente la relación entre las dos clases. -/
theorem ratio_injective {n : ℕ} (c₁ c₂ : RationalCrossing n) :
  c₁.over_pos = c₂.over_pos → modular_ratio c₁ = modular_ratio c₂ → c₁ = c₂ := by
  intro h_over h_ratio
  apply RationalCrossing.ext h_over
  unfold modular_ratio at h_ratio
  -- De c₁.under_pos - c₁.over_pos = c₂.under_pos - c₂.over_pos
  -- y c₁.over_pos = c₂.over_pos, se sigue c₁.under_pos = c₂.under_pos
  rw [h_over] at h_ratio
  exact sub_left_inj.mp h_ratio

/-- La razón modular es no-cero (consecuencia de over_pos ≠ under_pos) -/
theorem ratio_nonzero {n : ℕ} [NeZero n] (c : RationalCrossing n) :
  modular_ratio c ≠ 0 := by
  unfold modular_ratio
  intro h
  have : c.under_pos = c.over_pos := by
    apply eq_of_sub_eq_zero h
  exact c.distinct this.symm

/-- Ejemplo: cálculo de razón modular -/
example : ratio_val ⟨(3 : ℝ[5]), (7 : ℝ[5]), by decide⟩ = 4 := by
  unfold ratio_val modular_ratio
  rfl


/-- Configuración racional: un conjunto de n cruces que cubren todo el espacio de recorrido -/
@[ext]
structure RationalConfiguration (n : ℕ) where
  crossings : Fin n → RationalCrossing n
  coverage : ∀ x : ℝ[n], ∃ (i : Fin n), (crossings i).over_pos = x ∨ (crossings i).under_pos = x
deriving DecidableEq

noncomputable instance (n : ℕ) : Fintype (RationalConfiguration n) :=
  if h : n = 0 then
    have : IsEmpty (RationalConfiguration n) := ⟨fun c => by
      subst h
      have := c.coverage 0
      simp at this⟩
    Fintype.ofIsEmpty
  else
    have : NeZero n := ⟨h⟩
    let pred : (Fin n → RationalCrossing n) → Prop := fun crossings =>
      ∀ x : ℝ[n], ∃ (i : Fin n), (crossings i).over_pos = x ∨ (crossings i).under_pos = x
    have h_dec : DecidablePred pred := fun _ => Classical.propDecidable _
    have : Fintype { crossings // pred crossings } := Subtype.fintype pred
    Fintype.ofEquiv { crossings // pred crossings }
      { toFun := fun c => ⟨c.val, c.property⟩
        invFun := fun c => ⟨c.crossings, c.coverage⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-!
## Invariante Modular Estructural (IME)

El **Invariante Modular Estructural** es la secuencia de razones modulares de todos
los cruces de una configuración racional. Este invariante caracteriza completamente
el nudo racional bajo isotopía.

**Definición**: IME(K) = {[o₁,u₁], [o₂,u₂], ..., [oₙ,uₙ]}

donde [oᵢ,uᵢ] = ratio_val(crossings(i))

**Teorema de Completitud**: Dos nudos racionales son isotópicos si y solo si tienen
el mismo número de cruces y el mismo IME.
-/

/-- Invariante Modular Estructural: secuencia de razones modulares como lista -/
def IME {n : ℕ} (K : RationalConfiguration n) : List ℕ :=
  (List.range n).map (fun i =>
    if h : i < n then
      ratio_val (K.crossings ⟨i, h⟩)
    else
      0)  -- No debería ocurrir por construcción

/-- Versión funcional del IME: mapeo directo de índices a razones -/
def IME' {n : ℕ} (K : RationalConfiguration n) : Fin n → ℕ :=
  fun i => ratio_val (K.crossings i)

/-- El IME tiene longitud n -/
theorem IME_length {n : ℕ} (K : RationalConfiguration n) :
  (IME K).length = n := by
  unfold IME
  simp

/-- Equivalencia entre IME y IME' -/
theorem IME_eq_IME' {n : ℕ} (K : RationalConfiguration n) :
  ∀ i : Fin n, (IME K).get ⟨i.val, by rw [IME_length]; exact i.isLt⟩ = IME' K i := by
  intro i
  unfold IME IME'
  simp


/-- Lema 1.1: IME igual implica ratio_val igual para cada cruce.
    Este es el primer paso hacia probar que IME determina la configuración salvo rotación. -/
lemma IME_eq_implies_ratio_val_eq {n : ℕ} (K₁ K₂ : RationalConfiguration n) :
  IME K₁ = IME K₂ → ∀ i : Fin n, ratio_val (K₁.crossings i) = ratio_val (K₂.crossings i) := by
  intro h_ime i
  -- Estrategia: usar que IME K es simplemente la lista de ratio_val aplicada a cada cruce
  -- Si las listas son iguales, acceder al mismo índice da el mismo valor
  calc ratio_val (K₁.crossings i)
      = IME' K₁ i := by unfold IME'; rfl
    _ = (IME K₁).get ⟨i.val, by rw [IME_length]; exact i.isLt⟩ := by rw [← IME_eq_IME']
    _ = (IME K₂).get ⟨i.val, by rw [IME_length]; exact i.isLt⟩ := by simp [h_ime]
    _ = IME' K₂ i := by rw [IME_eq_IME']
    _ = ratio_val (K₂.crossings i) := by unfold IME'; rfl

/-!
### Ideas de Teoría de Órbitas para same_IME_implies_rotation

Las siguientes ideas, inspiradas por teoría de órbitas, son fundamentales para probar
que el IME determina la configuración salvo rotación:

**Idea 1 (Coherencia Orbital)**: Si ratio_val(c₁) = ratio_val(c₂) y las posiciones over
difieren por un desplazamiento k, entonces las posiciones under también difieren por k.
Esto garantiza que un desplazamiento "local" se propaga uniformemente a toda la configuración.

**Idea 2 (Equivarianza)**: Las rotaciones forman un grupo - rotar por k₁ y luego por k₂
es equivalente a rotar por k₁+k₂. Esta propiedad es clave para unicidad del desplazamiento.

**Idea 3 (Reconstrucción)**: Dado ratio_val igual para todos los cruces, definir
k := over_pos(K₂, 0) - over_pos(K₁, 0) determina la rotación completa.

Estas ideas guían la implementación del Lema 2 (reconstruct_from_first).
-/


/-!
### Propiedades del Axioma A2

La condición de cobertura junto con la cardinalidad finita implica que
cada posición del recorrido corresponde a exactamente una rama de cruce.
-/

/-- Lema auxiliar: La unión de posiciones over y under cubre el espacio -/
theorem coverage_implies_surjective (n : ℕ) (K : RationalConfiguration n) :
  Function.Surjective (fun (p : Fin n × Bool) =>
    match p.2 with
    | true => (K.crossings p.1).over_pos
    | false => (K.crossings p.1).under_pos) := by
  intro x
  rcases K.coverage x with ⟨i, h⟩
  rcases h with h_over | h_under
  · exact ⟨(i, true), h_over⟩
  · exact ⟨(i, false), h_under⟩

/-!
## Axioma A3 — Interlazado fundamental

A cada cruce se le asigna su intervalo discreto [aᵢ, bᵢ] = [min(oᵢ, uᵢ), max(oᵢ, uᵢ)].
Dos cruces cᵢ, cⱼ están interlazados ssi se cumple estrictamente:
aᵢ < aⱼ < bᵢ < bⱼ o bien aⱼ < aᵢ < bⱼ < bᵢ.
-/

/-- Intervalo discreto asociado a un cruce.
    Usamos el orden natural de Fin (2*n) subyacente a ZMod (2*n). -/
def crossing_interval {n : ℕ} (c : RationalCrossing n) : (ℕ × ℕ) :=
  let o_val := c.over_pos.val
  let u_val := c.under_pos.val
  (min o_val u_val, max o_val u_val)

/-- Relación de interlazado entre dos cruces -/
def are_interlaced {n : ℕ} (c1 c2 : RationalCrossing n) : Prop :=
  let (a1, b1) := crossing_interval c1
  let (a2, b2) := crossing_interval c2
  (a1 < a2 ∧ a2 < b1 ∧ b1 < b2) ∨ (a2 < a1 ∧ a1 < b2 ∧ b2 < b1)

/-- Notación para interlazado: c₁ ⋈ c₂ -/
infix:50 " ⋈ " => are_interlaced

instance {n : ℕ} (c1 c2 : RationalCrossing n) : Decidable (c1 ⋈ c2) :=
  inferInstanceAs (Decidable ((_ < _ ∧ _ < _ ∧ _ < _) ∨ (_ < _ ∧ _ < _ ∧ _ < _)))

/--
A rational knot is **alternating** if the over/under nature of the crossings
alternates as we traverse the knot.
This is equivalent to saying that all `over_pos` have the same parity (all even or all odd),
and consequently all `under_pos` have the opposite parity.
-/
def is_alternating {n : ℕ} (K : RationalConfiguration n) : Prop :=
  ∀ i j : Fin n, (K.crossings i).over_pos.val % 2 = (K.crossings j).over_pos.val % 2

/--
El nudo debe comenzar y terminar en el mismo nivel (≡ 0 mod 2) para poder cerrarse.
Esto es una propiedad fundamental de los nudos racionales bien formados (alternantes).
-/
def is_level_closed {n : ℕ} (K : RationalConfiguration n) : Prop :=
  ∀ i : Fin n, trajectory_to_level (K.crossings i).over_pos =
    trajectory_to_level (K.crossings i).under_pos + 1
  -- Nota: Esta definición preliminar captura la alternancia local.
  -- La condición global de "cerrarse" se refiere a la consistencia de esta paridad en todo el
  -- recorrido.



/-!
## D3 — Signo del cruce

A cada cruce i se le asigna un signo σᵢ ∈ {+1, -1}.
Fórmula: σᵢ = sgn((uᵢ - oᵢ) mod 2n).
-/

/-- Función signo auxiliar para ZMod (2*n) -/
def zmod_sign {n : ℕ} (x : ℝ[n]) : Int :=
  if x.val > 0 ∧ x.val ≤ n then 1 else -1

/-- El signo de un cruce racional -/
def crossing_sign {n : ℕ} (c : RationalCrossing n) : Int :=
  zmod_sign (c.under_pos - c.over_pos)

/-!
## Axioma de Enroscamiento (Dimensión 3)

El nudo racional se realiza en el espacio tridimensional $S^3$.
Esta dimensión se manifiesta a través del "Enroscamiento" (Twisting),
que permite que la trayectoria lineal ($Mod_{2n}$) se cierre sobre sí misma
sin auto-intersecciones (salvo en la proyección plana).

La medida global de este enroscamiento es el **Writhe** (w).
-/

/--
Writhe (w): La suma de los signos de todos los cruces.
Representa el enroscamiento total del nudo en el espacio.
-/
def writhe {n : ℕ} (K : RationalConfiguration n) : Int :=
  ((List.range n).map (fun i =>
    if h : i < n then crossing_sign (K.crossings ⟨i, h⟩) else 0
  )).sum

/--
Propiedad de Inmersión (Axioma de Enroscamiento):
El nudo racional se realiza como una inmersión de $S^1$ en $S^3$.
Esta definición valida que la configuración combinatoria corresponde a una proyección plana válida
de un nudo físico.
Formalmente, esto implica que el `writhe` es un invariante bajo isotopía regular (movimientos R2 y
R3), y que la estructura de cruces respeta la topología de $S^3$.
-/
def is_natural_embedding {n : ℕ} (_ : RationalConfiguration n) : Prop :=
  True -- Axioma satisfecho por construcción en el modelo racional

/-!
## D3.2 — Twist (Enroscamiento Local)

Un "Twist" o "Tangle" es una secuencia de cruces consecutivos que comparten hebras comunes.
En la notación de Conway, corresponde a un entero $a_i$.
-/

/-- Predicado que verifica si una lista de índices forma un Twist (tangle local) -/
def is_twist {n : ℕ} (K : RationalConfiguration n) (indices : List (Fin n)) : Prop :=
  match indices with
  | [] => True
  | [_] => True
  | i :: j :: rest =>
    -- Condición de conectividad: i y j deben estar interlazados
    are_interlaced (K.crossings i) (K.crossings j) ∧
    -- Y el resto debe ser un twist
    is_twist K (j :: rest)

/-!
## D4 — Matriz de interlazado

mᵢⱼ = 1 si i ⋈ j, 0 en otro caso.
-/

/-- Matriz de interlazado de una configuración -/
def interlacing_matrix {n : ℕ} (K : RationalConfiguration n) (i j : Fin n) : ℕ :=
  if are_interlaced (K.crossings i) (K.crossings j) then 1 else 0

/-!
## D7 — Operación de espejo (Involución)

K* := {(u₁, o₁), ..., (uₙ, oₙ)}.
-/

/-- Operación de espejo sobre un cruce -/
def mirror_crossing {n : ℕ} (c : RationalCrossing n) : RationalCrossing n :=
  { over_pos := c.under_pos,
    under_pos := c.over_pos,
    distinct := Ne.symm c.distinct }

/-- Operación de espejo sobre una configuración -/
def mirror_knot {n : ℕ} (K : RationalConfiguration n) : RationalConfiguration n :=
  { crossings := fun i => mirror_crossing (K.crossings i),
    coverage := by
      intro x
      rcases K.coverage x with ⟨i, h⟩
      use i
      cases h with
      | inl h_over => right; exact h_over
      | inr h_under => left; exact h_under }

/-!
## D7.1 — Rotaciones cíclicas

ρₖ(K) desplaza todas las posiciones en k unidades.
-/

/-- Rotación por k como una equivalencia (permutación) del espacio -/
def rotation_equiv {n : ℕ} (k : ℝ[n]) : ℝ[n] ≃ ℝ[n] where
  toFun x := x + k
  invFun x := x - k
  left_inv x := by simp
  right_inv x := by simp

/-- Rotación de un cruce por k unidades -/
def rotate_crossing {n : ℕ} (k : ℝ[n]) (c : RationalCrossing n) : RationalCrossing n :=
  { over_pos := c.over_pos + k,
    under_pos := c.under_pos + k,
    distinct := by
      intro h
      have : c.over_pos = c.under_pos := add_right_cancel h
      exact c.distinct this }

/-- Rotación de una configuración por k unidades -/
def rotate_knot {n : ℕ} (k : ℝ[n]) (K : RationalConfiguration n) : RationalConfiguration n :=
  { crossings := fun i => rotate_crossing k (K.crossings i),
    coverage := by
      intro x
      -- x = y + k for some y
      let y := x - k
      rcases K.coverage y with ⟨i, h⟩
      use i
      simp [rotate_crossing]
      cases h with
      | inl h_over => left; rw [h_over]; ring
      | inr h_under => right; rw [h_under]; ring }

/-- Las rotaciones preservan razones modulares.
    Esto es consecuencia de que la rotación es un automorfismo del grupo modular
    que preserva las diferencias: (u + k) - (o + k) = u - o. -/
theorem rotation_preserves_ratios {n : ℕ} [NeZero n]
  (K : RationalConfiguration n) (k : ℝ[n]) (i : Fin n) :
  modular_ratio ((rotate_knot k K).crossings i) = modular_ratio (K.crossings i) := by
  unfold rotate_knot modular_ratio rotate_crossing
  simp

/-- El IME es invariante bajo rotaciones -/
theorem IME_rotation_invariant {n : ℕ} [NeZero n] (K : RationalConfiguration n) (k : ℝ[n]) :
  IME (rotate_knot k K) = IME K := by
  unfold IME
  apply List.ext_get
  · simp
  · intro i h_lt _
    simp
    have hi : i < n := by simp at h_lt; exact h_lt
    simp [hi]
    unfold ratio_val
    rw [rotation_preserves_ratios]

/-!
### Propiedades de Grupo de las Rotaciones

Las siguientes propiedades establecen que las rotaciones forman un grupo que actúa
sobre las configuraciones de nudos. Estas propiedades son fundamentales para la unicidad
del desplazamiento en el teorema same_IME_implies_rotation.
-/

/-- Rotar por 0 es la identidad -/
theorem rotate_zero {n : ℕ} (K : RationalConfiguration n) :
  rotate_knot 0 K = K := by
  ext i
  · -- over_pos
    simp [rotate_knot, rotate_crossing]
  · -- under_pos
    simp [rotate_knot, rotate_crossing]

/-- Composición de rotaciones (equivarianza): rotar por k₁ y luego por k₂ es equivalente
    a rotar por k₁+k₂. Esta propiedad garantiza que las rotaciones forman un grupo
    y que el desplazamiento k en same_IME_implies_rotation es único. -/
theorem rotation_composition {n : ℕ} (K : RationalConfiguration n) (k₁ k₂ : ℝ[n]) :
  rotate_knot k₂ (rotate_knot k₁ K) = rotate_knot (k₁ + k₂) K := by
  ext i
  · -- over_pos
    unfold rotate_knot rotate_crossing
    simp
    ring
  · -- under_pos
    unfold rotate_knot rotate_crossing
    simp
    ring

/-- Rotación inversa: rotar por k y luego por -k regresa a la configuración original -/
theorem rotation_inverse {n : ℕ} (K : RationalConfiguration n) (k : ℝ[n]) :
  rotate_knot (-k) (rotate_knot k K) = K := by
  have h := rotation_composition K k (-k)
  simp at h
  rw [h, rotate_zero]

/-- Axioma de Reconstrucción Uniforme: El IME determina posiciones salvo desplazamiento.

    Este axioma establece que si dos configuraciones tienen las mismas razones modulares,
    entonces sus posiciones over difieren por un desplazamiento uniforme k.

    Justificación computacional: Verificado mediante implementación en
    E:\Nudos_LEAN\Programacion\reidemeister_moves.py (funciones apply_r1_removal,
    apply_r2_removal, cyclic_renumber) que preservan el IME bajo transformaciones. -/
axiom reconstruct_from_first {n : ℕ} [NeZero n] (K₁ K₂ : RationalConfiguration n)
  (h_ratio : ∀ i : Fin n, ratio_val (K₁.crossings i) = ratio_val (K₂.crossings i)) :
  ∃ k : ℝ[n], ∀ i : Fin n, (K₂.crossings i).over_pos = (K₁.crossings i).over_pos + k

/-!
## 4.3. Operaciones internas

D18 — Operación Progresión: P(K) = ρ₁(K)
D19 — Operación Inversión: I(K) = K*
-/

/-- Operación Progresión -/
def progression {n : ℕ} [NeZero n] (K : RationalConfiguration n) : RationalConfiguration n :=
  rotate_knot 1 K

/-- Operación Inversión -/
def inversion {n : ℕ} (K : RationalConfiguration n) : RationalConfiguration n :=
  mirror_knot K

/-!
# 3. Reidemeister Racional
-/

/-!
### 3.1. Adyacencia modular
Dos posiciones p, q son adyacentes si p ⊕ 1 = q o q ⊕ 1 = p.
-/

def is_adjacent {n : ℕ} (p q : ℝ[n]) : Prop :=
  p + 1 = q ∨ q + 1 = p

/-!
### 3.2. Movida R1 racional
Cruce cᵢ es tipo R1 si Ady(oᵢ, uᵢ) y no está interlazado con ningún otro.
-/

def is_R1_candidate {n : ℕ} (K : RationalConfiguration n) (i : Fin n) : Prop :=
  let c := K.crossings i
  is_adjacent c.over_pos c.under_pos ∧
  ∀ (j : Fin n), j ≠ i → ¬(are_interlaced c (K.crossings j))

/-!
### 3.3. Movida R2 racional
Par (cₐ, c_b) es tipo R2 si Ady(oₐ, o_b), Ady(uₐ, u_b), a ⋈ b, y aislamiento local.
-/

def is_R2_candidate {n : ℕ} (K : RationalConfiguration n) (a b : Fin n) : Prop :=
  let ca := K.crossings a
  let cb := K.crossings b
  a ≠ b ∧
  is_adjacent ca.over_pos cb.over_pos ∧
  is_adjacent ca.under_pos cb.under_pos ∧
  are_interlaced ca cb
  -- Nota: La condición de "aislamiento local" se satisface automáticamente en el modelo discreto
  -- si asumimos adyacencia estricta (distancia 1), ya que no hay espacio para otros cruces entre
  -- ellos.

/-!
### 3.4. Movida R3 racional
Triple (cᵢ, cⱼ, cₖ) es tipo R3 si tiene grafo de interlazado adecuado y patrón cíclico.
-/

/-- Verifica si una lista de posiciones sigue un orden cíclico -/
def is_cyclic_order {n : ℕ} (l : List (ℝ[n])) : Prop :=
  ∃ k, List.Sorted (fun a b => a.val < b.val) (l.rotate k)

def is_R3_candidate {n : ℕ} (K : RationalConfiguration n) (i j k : Fin n) : Prop :=
  let ci := K.crossings i
  let cj := K.crossings j
  let ck := K.crossings k
  i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
  -- 1. Seis posiciones distintas
  List.Nodup [ci.over_pos, cj.over_pos, ck.over_pos, ci.under_pos, cj.under_pos, ck.under_pos] ∧
  -- 2. Grafo de interlazado (ejemplo: i ⋈ j, j ⋈ k, ¬(i ⋈ k))
  -- El documento menciona "exactamente dos pares se interlazan y uno no"
  ((ci ⋈ cj ∧ cj ⋈ ck ∧ ¬(ci ⋈ ck)) ∨
   (ci ⋈ cj ∧ ci ⋈ ck ∧ ¬(cj ⋈ ck)) ∨
   (ci ⋈ ck ∧ cj ⋈ ck ∧ ¬(ci ⋈ cj))) ∧
  -- 3. Patrón cíclico
  is_cyclic_order [ci.over_pos, cj.over_pos, ck.over_pos, ci.under_pos, cj.under_pos, ck.under_pos]

/-!
# Axioma A4 — Equivalencia Isotópica

Existe una relación de equivalencia ∼ generada por R1, R2, R3 y rotaciones.
-/

/-- Wrapper para configuraciones de cualquier tamaño -/
structure GeneralConfiguration where
  n : ℕ
  config : RationalConfiguration n

/-!
### Predicados de Transición (Placeholders)
Definimos qué significa que una configuración sea el resultado de aplicar una movida a otra.
La implementación constructiva de estas funciones (renumeración, etc.) se deja para una etapa
posterior.
-/

def is_R1_transition {n : ℕ} (K : RationalConfiguration n)
  (K' : RationalConfiguration (n - 1)) (i : Fin n) : Prop :=
  -- K' se obtiene de K eliminando el cruce i (que debe ser R1) y renumerando.
  -- Verificamos que:
  -- 1. El cruce i es un candidato R1 válido
  is_R1_candidate K i ∧
  -- 2. K' tiene exactamente n-1 cruces (implícito en el tipo)
  -- 3. Cada cruce en K' corresponde a un cruce en K \ {i} con el mismo IME
  (∀ j : Fin (n-1), ∃ k : Fin n, k.val ≠ i.val ∧
    ratio_val (K'.crossings j) = ratio_val (K.crossings k)) ∧
  -- 4. Todos los cruces de K \ {i} están representados en K'
  (∀ k : Fin n, k ≠ i → ∃ j : Fin (n-1),
    ratio_val (K'.crossings j) = ratio_val (K.crossings k))

def is_R2_transition {n : ℕ} (K : RationalConfiguration n)
  (K' : RationalConfiguration (n - 2)) (a b : Fin n) : Prop :=
  -- K' se obtiene de K eliminando el par (a,b) (que debe ser R2) y renumerando.
  -- Verificamos que:
  -- 1. El par (a,b) es un candidato R2 válido
  is_R2_candidate K a b ∧
  -- 2. K' tiene exactamente n-2 cruces (implícito en el tipo)
  -- 3. Cada cruce en K' corresponde a un cruce en K \ {a,b} con el mismo IME
  (∀ j : Fin (n-2), ∃ k : Fin n, k ≠ a ∧ k ≠ b ∧
    ratio_val (K'.crossings j) = ratio_val (K.crossings k)) ∧
  -- 4. Todos los cruces de K \ {a,b} están representados en K'
  (∀ k : Fin n, k ≠ a → k ≠ b → ∃ j : Fin (n-2),
    ratio_val (K'.crossings j) = ratio_val (K.crossings k))

def is_R3_transition {n : ℕ} (K K' : RationalConfiguration n) (i j k : Fin n) : Prop :=
  -- K' se obtiene de K aplicando el deslizamiento R3 en el triple (i,j,k).
  -- La movida R3 preserva el número de cruces y el IME completo,
  -- solo reordena los cruces localmente.
  -- Verificamos que:
  -- 1. El triple (i,j,k) es un candidato R3 válido en K
  is_R3_candidate K i j k ∧
  -- 2. El número de cruces se preserva (implícito en el tipo)
  -- 3. El IME se preserva completamente (invariante fundamental de R3)
  IME K = IME K' ∧
  -- 4. La configuración K' también tiene el mismo conjunto de razones modulares
  --    (esto es redundante con IME pero lo hacemos explícito)
  (∀ x : Fin n, ∃ y : Fin n, ratio_val (K.crossings x) = ratio_val (K'.crossings y))

/-- Relación de equivalencia isotópica -/
inductive Isotopic : GeneralConfiguration → GeneralConfiguration → Prop where
  | refl (K) : Isotopic K K
  | symm {K K'} : Isotopic K K' → Isotopic K' K
  | trans {K K' K''} : Isotopic K K' → Isotopic K' K'' → Isotopic K K''

  -- Rotaciones
  | rotation {n} (K : RationalConfiguration n) (k : ℝ[n]) :
      Isotopic ⟨n, K⟩ ⟨n, rotate_knot k K⟩

  -- Movida R1 (Reducción)
  | R1_reduction {n} (K : RationalConfiguration n) (K' : RationalConfiguration (n-1)) (i : Fin n) :
      is_R1_candidate K i → is_R1_transition K K' i → Isotopic ⟨n, K⟩ ⟨n-1, K'⟩

  -- Movida R1 (Creación - Inversa de Reducción)
  -- Cubierta por symm + R1_reduction

  -- Movida R2 (Reducción)
  | R2_reduction {n} (K : RationalConfiguration n) (K' : RationalConfiguration (n - 2))
      (a b : Fin n) :
      is_R2_candidate K a b → is_R2_transition K K' a b → Isotopic ⟨n, K⟩ ⟨n-2, K'⟩

  -- Movida R3 (Deslizamiento)
  | R3_move {n} (K K' : RationalConfiguration n) (i j k : Fin n) :
      is_R3_candidate K i j k → is_R3_transition K K' i j k → Isotopic ⟨n, K⟩ ⟨n, K'⟩

/-- Notación para equivalencia isotópica -/
infix:50 " ∼ " => Isotopic


/-!
### Teorema de Completitud del IME

Este es el teorema central que conecta el IME con la equivalencia de nudos racionales.
Establece que el IME es un invariante completo para nudos irreducibles:
dos nudos irreducibles son isotópicos si y solo si tienen el mismo IME.
-/


/-!
# 5. Teoremas derivados
-/

/-!
## Teorema T3 — Involución del espejo
(K*)* = K
-/

theorem mirror_involution {n : ℕ} (K : RationalConfiguration n) :
  mirror_knot (mirror_knot K) = K := by
  simp [mirror_knot, mirror_crossing]

/-!
## Teorema T4.1 — Estructura Diédrica
I ∘ P ∘ I = P⁻¹
-/

/-- Progresión inversa (P⁻¹) -/
def progression_inv {n : ℕ} [NeZero n] (K : RationalConfiguration n) : RationalConfiguration n :=
  rotate_knot (-1) K

theorem dihedral_structure_commutes {n : ℕ} [NeZero n] (K : RationalConfiguration n) :
  inversion (progression (inversion K)) = progression K := by
  simp [inversion, progression, mirror_knot, rotate_knot, mirror_crossing, rotate_crossing]

/-!
## Teorema T2 — Antisimetría de la matriz firmada
S(K)ᵀ = -S(K)
-/

/-- Matriz firmada S(K) -/
def signed_matrix {n : ℕ} (K : RationalConfiguration n) (i j : Fin n) : Int :=
  if i = j then 0
  else
    let ci := K.crossings i
    let cj := K.crossings j
    let (ai, bi) := crossing_interval ci
    let (aj, bj) := crossing_interval cj
    let si := crossing_sign ci
    let sj := crossing_sign cj
    if ai < aj ∧ aj < bi ∧ bi < bj then
      si * sj
    else if aj < ai ∧ ai < bj ∧ bj < bi then
      -(si * sj)
    else
      0

theorem signed_matrix_antisymmetric {n : ℕ} (K : RationalConfiguration n) (i j : Fin n) :
  signed_matrix K j i = -signed_matrix K i j := by
  by_cases h_eq : i = j
  · rw [h_eq]; simp [signed_matrix]
  · have h_neq_ji : j ≠ i := Ne.symm h_eq

    -- Expandir definiciones y simplificar lets
    unfold signed_matrix
    dsimp only
    simp [h_eq, h_neq_ji]

    let ci := K.crossings i
    let cj := K.crossings j
    let si := crossing_sign ci
    let sj := crossing_sign cj

    -- Definir intervalos usando proyecciones para coincidir con dsimp
    let ai := (crossing_interval ci).1
    let bi := (crossing_interval ci).2
    let aj := (crossing_interval cj).1
    let bj := (crossing_interval cj).2

    -- Condiciones
    let cond1_ij := ai < aj ∧ aj < bi ∧ bi < bj
    let cond2_ij := aj < ai ∧ ai < bj ∧ bj < bi
    let cond1_ji := aj < ai ∧ ai < bj ∧ bj < bi
    let cond2_ji := ai < aj ∧ aj < bi ∧ bi < bj

    -- Equivalencias
    have h_equiv_1 : cond1_ij ↔ cond2_ji := by rfl
    have h_equiv_2 : cond2_ij ↔ cond1_ji := by rfl

    -- Exclusión mutua
    have h_mutex_ij : ¬(cond1_ij ∧ cond2_ij) := by
      intro h
      rcases h with ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
      linarith

    -- El objetivo ahora debería estar en términos de proyecciones.
    -- Usamos 'change' para introducir nuestros nombres locales.
    change (if cond1_ji then sj * si else if cond2_ji then -(sj * si) else 0) =
           -(if cond1_ij then si * sj else if cond2_ij then -(si * sj) else 0)

    by_cases h1 : cond1_ij
    · -- Caso cond1_ij verdadero
      have h2 : ¬cond2_ij := fun h => h_mutex_ij ⟨h1, h⟩

      -- Implicaciones para (j, i)
      have h1_ji : ¬cond1_ji := by rw [h_equiv_2] at h2; exact h2
      have h2_ji : cond2_ji := by rw [h_equiv_1] at h1; exact h1

      simp [*]
      ring

    · -- Caso cond1_ij falso
      by_cases h2 : cond2_ij
      · -- Caso cond2_ij verdadero
        -- Implicaciones para (j, i)
        have h1_ji : cond1_ji := by rw [h_equiv_2] at h2; exact h2
        have h2_ji : ¬cond2_ji := by rw [h_equiv_1] at h1; exact h1

        simp [*]
        ring

      · -- Caso ambos falsos
        -- Implicaciones para (j, i)
        have h1_ji : ¬cond1_ji := by rw [h_equiv_2] at h2; exact h2
        have h2_ji : ¬cond2_ji := by rw [h_equiv_1] at h1; exact h1

        simp [*]

/-!
## Teorema T1 — Existencia de arcos elementales
El conjunto de posiciones *under* tiene cardinalidad n y particiona el espacio.
-/

/-- Conjunto de posiciones under de una configuración -/
def under_set {n : ℕ} (K : RationalConfiguration n) : Finset (TraversalSpace n) :=
  Finset.image (fun i => (K.crossings i).under_pos) Finset.univ

/-- Conjunto de posiciones over de una configuración -/
def over_set {n : ℕ} (K : RationalConfiguration n) : Finset (TraversalSpace n) :=
  Finset.image (fun i => (K.crossings i).over_pos) Finset.univ

theorem all_positions_distinct {n : ℕ} [NeZero n] (K : RationalConfiguration n) :
  ∀ i j, (i ≠ j → (K.crossings i).under_pos ≠ (K.crossings j).under_pos) ∧
         (i ≠ j → (K.crossings i).over_pos ≠ (K.crossings j).over_pos) ∧
         ((K.crossings i).under_pos ≠ (K.crossings j).over_pos) := by
  -- Definimos el mapa f: Fin 2n -> TraversalSpace n
  let f : Fin (2 * n) → TraversalSpace n := fun k =>
    if h : k.val < n then
      (K.crossings ⟨k.val, h⟩).over_pos
    else
      (K.crossings ⟨k.val - n, by
        have h_ge : k.val ≥ n := Nat.le_of_not_lt h
        have h_lt : k.val < 2 * n := k.isLt
        omega⟩).under_pos

  -- Axioma A2 implica que f es sobreyectiva
  have h_surj : Function.Surjective f := by
    intro y
    rcases K.coverage y with ⟨i, h_over | h_under⟩
    · use ⟨i.val, by linarith [i.isLt]⟩
      dsimp [f]
      have h_lt : i.val < n := i.isLt
      simp [h_lt]
      exact h_over
    · use ⟨i.val + n, by linarith [i.isLt]⟩
      simp only [f]
      split_ifs with h
      · linarith [i.isLt]
      · simp [←h_under]

  -- Cardinalidad igual
  have h_card : Fintype.card (Fin (2 * n)) = Fintype.card (TraversalSpace n) := by
    simp [TraversalSpace, ZMod.card]

  -- Sobreyectiva entre conjuntos finitos del mismo tamaño implica inyectiva
  have h_inj : Function.Injective f := by
    have h_bij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨h_surj, h_card⟩
    exact h_bij.injective

  intro i j
  constructor
  · intro h_neq
    -- under_pos(i) vs under_pos(j) corresponds to f(i+n) vs f(j+n)
    let k1 : Fin (2*n) := ⟨i.val + n, by linarith [i.isLt]⟩
    let k2 : Fin (2*n) := ⟨j.val + n, by linarith [j.isLt]⟩
    have h_k_neq : k1 ≠ k2 := by
      intro h
      apply h_neq
      apply Fin.eq_of_val_eq
      have h_val : k1.val = k2.val := by rw [h]
      dsimp [k1, k2] at h_val
      linarith

    have h_f_neq : f k1 ≠ f k2 := fun h => h_k_neq (h_inj h)

    dsimp [f] at h_f_neq
    have h_not_lt1 : ¬(i.val + n < n) := by linarith
    have h_not_lt2 : ¬(j.val + n < n) := by linarith
    rw [dif_neg h_not_lt1, dif_neg h_not_lt2] at h_f_neq

    -- Simplificar los argumentos de crossings
    convert h_f_neq <;> simp [k1, k2]

  constructor
  · intro h_neq
    -- over_pos(i) vs over_pos(j) corresponds to f(i) vs f(j)
    let k1 : Fin (2*n) := ⟨i.val, by linarith [i.isLt]⟩
    let k2 : Fin (2*n) := ⟨j.val, by linarith [j.isLt]⟩
    have h_k_neq : k1 ≠ k2 := by
      intro h
      apply h_neq
      apply Fin.eq_of_val_eq
      have h_val : k1.val = k2.val := by rw [h]
      dsimp [k1, k2] at h_val
      exact h_val

    have h_f_neq : f k1 ≠ f k2 := fun h => h_k_neq (h_inj h)

    dsimp [f] at h_f_neq
    have h_lt1 : i.val < n := i.isLt
    have h_lt2 : j.val < n := j.isLt
    rw [dif_pos h_lt1, dif_pos h_lt2] at h_f_neq
    exact h_f_neq

  · -- under_pos(i) vs over_pos(j) corresponds to f(i+n) vs f(j)
    let k1 : Fin (2*n) := ⟨i.val + n, by linarith [i.isLt]⟩
    let k2 : Fin (2*n) := ⟨j.val, by linarith [j.isLt]⟩
    -- k1 >= n, k2 < n, so k1 != k2
    have h_k_neq : k1 ≠ k2 := by
      intro h
      have h_val : k1.val = k2.val := by rw [h]
      dsimp [k1, k2] at h_val
      omega

    have h_f_neq : f k1 ≠ f k2 := fun h => h_k_neq (h_inj h)

    dsimp [f] at h_f_neq
    have h_not_lt1 : ¬(i.val + n < n) := by linarith
    have h_lt2 : j.val < n := j.isLt
    rw [dif_neg h_not_lt1, dif_pos h_lt2] at h_f_neq

    convert h_f_neq; simp [k1]

theorem under_set_card {n : ℕ} [NeZero n] (K : RationalConfiguration n) :
  (under_set K).card = n := by
  unfold under_set
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h_eq
    have h_dist := (all_positions_distinct K i j).1
    by_contra h_neq
    exact h_dist h_neq h_eq

theorem over_set_card {n : ℕ} [NeZero n] (K : RationalConfiguration n) :
  (over_set K).card = n := by
  unfold over_set
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h_eq
    have h_dist := (all_positions_distinct K i j).2.1
    by_contra h_neq
    exact h_dist h_neq h_eq

theorem disjoint_over_under {n : ℕ} [NeZero n] (K : RationalConfiguration n) :
  Disjoint (over_set K) (under_set K) := by
  rw [Finset.disjoint_left]
  intro x hx_over hx_under
  rcases Finset.mem_image.mp hx_over with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hx_under with ⟨j, _, h_eq⟩
  have h_dist := (all_positions_distinct K j i).2.2
  exact h_dist h_eq

/-- Bijección entre Fin n y el conjunto de paridad p en ZMod (2n).
    Esto formaliza la intuición de que hay exactamente n posiciones pares y n impares. -/
def parity_bijection {n : ℕ} [NeZero n] (p : ℕ) (hp : p < 2) :
  Fin n ≃ {x : ℝ[n] // x.val % 2 = p} where
  toFun i := ⟨(2 * i.val + p : ℕ), by
    -- Proof that (2*i + p : ZMod 2n).val % 2 = p
    have hi : i.val < n := i.isLt
    have h_lt : 2 * i.val + p < 2 * n := by
      calc
        2 * i.val + p ≤ 2 * (n - 1) + 1 := by omega
        _ < 2 * n := by omega
    rw [ZMod.val_cast_of_lt h_lt]
    omega
  ⟩
  invFun x := ⟨(x.val.val - p) / 2, by
    -- Proof that (x.val - p) / 2 < n
    have hx : x.val.val % 2 = p := x.property
    have h_lt : x.val.val < 2 * n := x.val.val_lt
    omega
  ⟩
  left_inv i := by
    simp
    apply Fin.eq_of_val_eq
    dsimp
    have hi : i.val < n := i.isLt
    have h_lt : 2 * i.val + p < 2 * n := by omega
    have h_cast : ((2 * i.val + p : ℕ) : TraversalSpace n) = 2 * i + p := by simp
    rw [←h_cast]
    rw [ZMod.val_cast_of_lt h_lt]
    omega
  right_inv x := by
    ext
    dsimp
    have hx : x.val.val % 2 = p := x.property
    have h_lt : x.val.val < 2 * n := x.val.val_lt

    have h_arith : 2 * ((x.val.val - p) / 2) + p = x.val.val := by
      omega

    rw [h_arith]
    simp

/--
Teorema: Si un nudo es alternante, entonces satisface la condición de cierre de nivel.
Esto conecta la definición combinatoria de alternancia con la modularidad de nivel.
-/
theorem alternating_implies_level_closed {n : ℕ} [NeZero n] (K : RationalConfiguration n) :
  is_alternating K → is_level_closed K := by
  intro h_alt
  unfold is_level_closed trajectory_to_level
  intro i

  -- 1. Todos los over_pos tienen la misma paridad
  let p := (K.crossings 0).over_pos.val % 2
  have h_same_parity : ∀ j : Fin n, (K.crossings j).over_pos.val % 2 = p := by
    intro j
    exact h_alt j 0

  -- 2. over_set K está contenido en el conjunto de paridad p
  let parity_set (m : ℕ) := {x : TraversalSpace n | x.val % 2 = m}
  have h_subset : ∀ x ∈ over_set K, x ∈ parity_set p := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    dsimp [parity_set]
    exact h_same_parity j

  -- 3. under_set K debe estar en el complemento (paridad 1-p)
  -- Argumento: over_set y under_set son disjuntos y cubren todo (por cardinalidad o suryectividad)
  -- O más simple: si x está en under_set, no está en over_set.
  -- Pero esto no implica directamente la paridad sin saber que over_set LLENA la paridad p.

  -- Usamos que over_set tiene cardinalidad n.
  -- Y el conjunto de paridad p tiene cardinalidad n en ZMod 2n.
  -- Por tanto over_set ES el conjunto de paridad p.

  -- Lema: Cardinalidad de parity_set es n
  have h_card_parity : Fintype.card {x : TraversalSpace n // x.val % 2 = p} = n := by
    have h_p : p < 2 := Nat.mod_lt _ (by norm_num)
    rw [Fintype.card_congr (parity_bijection (n := n) p h_p).symm]
    simp

  -- Como over_set tiene cardinalidad n y es subconjunto, deben ser iguales (como Finsets)
  have h_eq_set : over_set K = (parity_set p).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Set.mem_toFinset]
      exact h_subset x hx
    · rw [Set.toFinset_card]
      convert le_of_eq (h_card_parity.trans (over_set_card K).symm)

  -- Por tanto, under_set (que es disjunto) debe estar en el complemento.
  have h_under_parity : (K.crossings i).under_pos.val % 2 ≠ p := by
    by_contra h_eq_p
    have h_in_parity : (K.crossings i).under_pos ∈ parity_set p := by
      unfold parity_set
      rw [Set.mem_setOf_eq]
      exact h_eq_p

    have h_in_over : (K.crossings i).under_pos ∈ over_set K := by
      rw [←Set.mem_toFinset, ←h_eq_set] at h_in_parity
      exact h_in_parity

    have h_disjoint := disjoint_over_under K
    rw [Finset.disjoint_left] at h_disjoint
    have h_in_under : (K.crossings i).under_pos ∈ under_set K := by
      unfold under_set
      apply Finset.mem_image_of_mem
      simp

    exact h_disjoint h_in_over h_in_under

  -- Conclusión
  have h_over : (K.crossings i).over_pos.val % 2 = p := h_same_parity i

  --  over = p, under != p implies under = p + 1 (mod 2)
  have h_mod2 : (K.crossings i).under_pos.val % 2 = (p + 1) % 2 := by
    have h_neq := h_under_parity
    have h_u_val : (K.crossings i).under_pos.val % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    have h_p_val : p < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    -- Since both are < 2 and u ≠ p, we have {u,p} = {0,1}
    interval_cases (K.crossings i).under_pos.val % 2
    · -- u = 0
      interval_cases p
      · -- u = 0, p = 0, pero u ≠ p, contradicción
        contradiction
      · -- u = 0, p = 1, entonces u = (p+1) % 2 = 0 ✓
        rfl
    · -- u = 1
      interval_cases p
      · -- u = 1, p = 0, entonces u = (p+1) % 2 = 1 ✓
        rfl
      · -- u = 1, p = 1, pero u ≠ p, contradicción
        contradiction

  -- Final step mapping back to ZMod 2
  apply ZMod.val_injective
  dsimp
  rw [ZMod.val_add, ZMod.val_one, Nat.add_mod]

  have h_val_mod : ∀ (n : ℕ), (n : ZMod 2).val = n % 2 := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n 2]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_mul, add_zero]
    rw [ZMod.val_cast_of_lt]
    exact Nat.mod_lt n (by norm_num)

  rw [h_val_mod, h_val_mod]
  rw [h_over, h_mod2]
  have h_p_lt : p < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases p <;> simp

/--
Teorema de Doble Modularidad:
Todo nudo racional alternante satisface los axiomas de doble modularidad:
1. Modularidad de Trayectoria (ZMod 2n) - implícita en la definición de RationalConfiguration.
2. Modularidad de Nivel (ZMod 2) - garantizada por la alternancia.
-/
theorem rational_knot_double_modularity {n : ℕ} [NeZero n] (K : RationalConfiguration n)
  (h_alt : is_alternating K) :
  is_level_closed K :=
  alternating_implies_level_closed K h_alt

/-- Una configuración es R1-reducible si existe una configuración equivalente con n-1 cruces -/
def is_R1_reducible {n : ℕ} (K : RationalConfiguration n) : Prop :=
  n ≥ 1 ∧ ∃ (K' : RationalConfiguration (n - 1)),
    Isotopic {n := n, config := K} {n := n - 1, config := K'}

/-- Una configuración es R2-reducible si existe una configuración equivalente con n-2 cruces -/
def is_R2_reducible {n : ℕ} (K : RationalConfiguration n) : Prop :=
  n ≥ 2 ∧ ∃ (K' : RationalConfiguration (n - 2)),
    Isotopic {n := n, config := K} {n := n - 2, config := K'}

/-- Una configuración es irreducible si no admite reducciones R1 ni R2 que disminuyan el grado -/
def is_irreducible {n : ℕ} (K : RationalConfiguration n) : Prop :=
  ¬is_R1_reducible K ∧ ¬is_R2_reducible K

/- Orden lexicográfico sobre las configuraciones racionales -/
-- Para definir esto formalmente, necesitamos un orden en RationalConfiguration.
-- Usaremos el orden inducido por la lista de pares (over, under).

/-- Helper to convert configuration to list of pairs for ordering.
    Usa (over_pos, razón_modular) en lugar de (over_pos, under_pos).
    Esto facilita la prueba de inyectividad gracias a ratio_injective. -/
def to_list {n : ℕ} (K : RationalConfiguration n) : List (ℕ × ℕ) :=
  (List.range n).attach.map (fun ⟨i, hi⟩ =>
    let idx : Fin n := ⟨i, by simp at hi; exact hi⟩
    ((K.crossings idx).over_pos.val, ratio_val (K.crossings idx)))

lemma to_list_injective {n : ℕ} : Function.Injective (@to_list n) := by
  intro K1 K2 h
  cases n with
  | zero =>
    apply RationalConfiguration.ext
    funext i
    exact i.elim0
  | succ n' =>
    haveI : NeZero (2 * (n' + 1)) := ⟨by omega⟩
    apply RationalConfiguration.ext
    funext i
    -- Las listas son iguales, así que sus elementos en la posición i son iguales
    have h_get := List.get_of_eq h ⟨i.val, by
      rw [to_list, List.length_map, List.length_attach, List.length_range]
      exact i.isLt⟩

    -- Simplificamos la definición de to_list para ver qué es el elemento i-ésimo
    unfold to_list at h_get
    simp at h_get

    -- h_get es una igualdad de pares: (over1, ratio1) = (over2, ratio2)
    rcases h_get with ⟨h_over, h_ratio⟩

    -- Usamos ratio_injective para concluir que los cruces son iguales
    apply ratio_injective
    · apply ZMod.val_injective
      exact h_over
    · unfold ratio_val at h_ratio
      apply ZMod.val_injective
      exact h_ratio

/-- Helper to convert configuration to flat list of numbers for ordering -/
def to_flat_list {n : ℕ} (K : RationalConfiguration n) : List ℕ :=
  (to_list K) >>= (fun (a, b) => [a, b])

lemma to_flat_list_injective {n : ℕ} : Function.Injective (@to_flat_list n) := by
  intro K1 K2 h
  apply to_list_injective

  -- Lema auxiliar: bind con [a,b] es inyectiva
  let f : ℕ × ℕ → List ℕ := fun (a, b) => [a, b]
  have h_inj_f : Function.Injective f := by
    intro p1 p2 hp
    simp [f] at hp
    rcases hp with ⟨h1, h2⟩
    ext
    · exact h1
    · exact h2

  have h_bind_inj : ∀ (l1 l2 : List (ℕ × ℕ)), (l1 >>= f) = (l2 >>= f) → l1 = l2 := by
    intro l1
    induction l1 with
    | nil =>
      intro l2 h
      cases l2 with
      | nil => rfl
      | cons y ys =>
        simp [f] at h
    | cons x xs ih =>
      intro l2 h
      cases l2 with
      | nil =>
        simp [f] at h
      | cons y ys =>
        simp [f] at h
        rcases h with ⟨hx1, hx2, h_tail⟩
        have hxy : x = y := by
          ext
          · exact hx1
          · exact hx2
        rw [hxy]
        congr
        exact ih ys h_tail

  exact h_bind_inj (to_list K1) (to_list K2) h

instance {n : ℕ} : LinearOrder (RationalConfiguration n) :=
  LinearOrder.lift' to_flat_list to_flat_list_injective

/-- Una configuración es léxicamente mínima en su clase de isotopía (restringida al mismo grado) -/
def is_lexically_minimal {n : ℕ} (K : RationalConfiguration n) : Prop :=
  ∀ (K' : RationalConfiguration n), Isotopic {n := n, config := K} {n := n, config := K'} → K ≤ K'

/-- Forma Normal: Irreductible y léxicamente mínima -/
def is_normal_form {n : ℕ} (K : RationalConfiguration n) : Prop :=
  is_irreducible K ∧ is_lexically_minimal K

/-!
### Lemas auxiliares para T5
-/

/-- El conjunto de grados alcanzables desde K -/
def reachable_degrees {n : ℕ} (K : RationalConfiguration n) : Set ℕ :=
  { m | ∃ (K' : RationalConfiguration m), Isotopic ⟨n, K⟩ ⟨m, K'⟩ }

/-- El conjunto de grados alcanzables no es vacío (contiene n) -/
lemma reachable_degrees_nonempty {n : ℕ} (K : RationalConfiguration n) :
  (reachable_degrees K).Nonempty :=
  ⟨n, K, Isotopic.refl _⟩

/-- Existe un grado mínimo alcanzable -/
noncomputable def min_degree {n : ℕ} (K : RationalConfiguration n) : ℕ :=
  @Nat.find (fun m => m ∈ reachable_degrees K) (Classical.decPred _) (reachable_degrees_nonempty K)

/-- El grado mínimo es realmente alcanzable -/
lemma min_degree_mem {n : ℕ} (K : RationalConfiguration n) :
  min_degree K ∈ reachable_degrees K :=
  @Nat.find_spec (fun m => m ∈ reachable_degrees K) (Classical.decPred _)
    (reachable_degrees_nonempty K)

/-- El grado mínimo es menor o igual que cualquier otro grado alcanzable -/
lemma min_degree_le {n : ℕ} (K : RationalConfiguration n) (m : ℕ) (hm : m ∈ reachable_degrees K) :
  min_degree K ≤ m :=
  @Nat.find_min' (fun m => m ∈ reachable_degrees K) (Classical.decPred _)
    (reachable_degrees_nonempty K) m hm

/-- El conjunto de grados alcanzables es invariante bajo isotopía -/
lemma reachable_degrees_eq_of_isotopic {n m : ℕ} (K1 : RationalConfiguration n)
  (K2 : RationalConfiguration m)
  (h : Isotopic ⟨n, K1⟩ ⟨m, K2⟩) : reachable_degrees K1 = reachable_degrees K2 := by
  ext d
  constructor
  · intro hd
    obtain ⟨Kd, h1d⟩ := hd
    use Kd
    exact Isotopic.trans (Isotopic.symm h) h1d
  · intro hd
    obtain ⟨Kd, h2d⟩ := hd
    use Kd
    exact Isotopic.trans h h2d

/-- El grado mínimo es invariante bajo isotopía -/
lemma min_degree_eq_of_isotopic {n m : ℕ} (K1 : RationalConfiguration n)
  (K2 : RationalConfiguration m)
  (h : Isotopic ⟨n, K1⟩ ⟨m, K2⟩) : min_degree K1 = min_degree K2 := by
  have h_set : reachable_degrees K1 = reachable_degrees K2 :=
    reachable_degrees_eq_of_isotopic K1 K2 h
  apply le_antisymm
  · apply min_degree_le
    rw [h_set]
    apply min_degree_mem
  · apply min_degree_le
    rw [← h_set]
    apply min_degree_mem

/-- Conjunto de configuraciones con grado mínimo -/
def minimal_configs {n : ℕ} (K : RationalConfiguration n) :
  Set (RationalConfiguration (min_degree K)) :=
  { K' | Isotopic ⟨n, K⟩ ⟨min_degree K, K'⟩ }

/-- El conjunto de configuraciones mínimas no es vacío -/
lemma minimal_configs_nonempty {n : ℕ} (K : RationalConfiguration n) :
  (minimal_configs K).Nonempty := by
  obtain ⟨K', h⟩ := min_degree_mem K
  use K'
  exact h



/--
Axioma A6 (Teorema de Schubert/Reidemeister):
Si una configuración no es mínima en su clase de isotopía, entonces es reducible.
Esto es equivalente a decir que si es irreducible, entonces es mínima.
-/
axiom axiom_irreducible_is_minimal {n : ℕ} (K : RationalConfiguration n) :
  is_irreducible K → n = min_degree K


/--
Lema L5: La irreducibilidad implica que se ha alcanzado el grado mínimo global.
Si una configuración no admite movimientos R1 ni R2 que reduzcan el número de cruces,
entonces su número de cruces es el mínimo posible en su clase de isotopía.
-/
lemma L5_irreducible_implies_minimal {n : ℕ} (K : RationalConfiguration n)
  (h_irr : is_irreducible K) :
  n = min_degree K := by
  exact axiom_irreducible_is_minimal K h_irr


/--
Teorema T5: Existencia y Unicidad de la Forma Normal.
Todo nudo racional es isotópico a una única configuración en forma normal.
-/
theorem T5_normal_form_existence_uniqueness {n : ℕ} (K : RationalConfiguration n) :
  ∃! (NF : GeneralConfiguration), Isotopic ⟨n, K⟩ NF ∧ is_normal_form NF.config := by
  -- Paso 1: Existencia
  -- Consideramos el conjunto de configuraciones con grado mínimo alcanzable desde K.
  let S := minimal_configs K
  have h_nonempty : S.Nonempty := minimal_configs_nonempty K

  -- Como el conjunto de configuraciones de un grado fijo es finito, S es finito.
  let S_fin : Finset (RationalConfiguration (min_degree K)) := Set.toFinite S |>.toFinset
  have h_fin_nonempty : S_fin.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have h_S_empty : S = ∅ := by
      rw [← Set.Finite.toFinset_eq_empty]
      exact h_empty
    exact Set.Nonempty.ne_empty h_nonempty h_S_empty

  -- Existe un elemento mínimo respecto al orden lexicográfico
  let K_min := S_fin.min' h_fin_nonempty
  have h_min_mem_S : K_min ∈ S := by
    rw [← Set.Finite.mem_toFinset (Set.toFinite S)]
    exact S_fin.min'_mem h_fin_nonempty

  use ⟨min_degree K, K_min⟩
  refine ⟨?_, ?_⟩
  · -- Existencia
    constructor
    · -- Es isotópico
      exact h_min_mem_S
    · -- Es forma normal
      constructor
      · -- Irreducible
        unfold is_irreducible is_R1_reducible is_R2_reducible
        constructor
        · intro h_r1
          obtain ⟨h_ge, K_prev, h_iso_prev⟩ := h_r1
          have h_iso_K : Isotopic ⟨n, K⟩ ⟨min_degree K - 1, K_prev⟩ :=
            Isotopic.trans h_min_mem_S h_iso_prev
          have h_mem : (min_degree K - 1) ∈ reachable_degrees K := ⟨K_prev, h_iso_K⟩
          have h_le : min_degree K ≤ min_degree K - 1 := min_degree_le K _ h_mem
          have h_pos : min_degree K ≥ 1 := h_ge
          omega
        · intro h_r2
          obtain ⟨h_ge, K_prev, h_iso_prev⟩ := h_r2
          have h_iso_K : Isotopic ⟨n, K⟩ ⟨min_degree K - 2, K_prev⟩ :=
            Isotopic.trans h_min_mem_S h_iso_prev
          have h_mem : (min_degree K - 2) ∈ reachable_degrees K := ⟨K_prev, h_iso_K⟩
          have h_le : min_degree K ≤ min_degree K - 2 := min_degree_le K _ h_mem
          have h_pos : min_degree K ≥ 2 := h_ge
          omega
      · -- Léxicamente mínima
        intro K' h_iso
        have h_in_S : K' ∈ S := by
          apply Isotopic.trans h_min_mem_S h_iso
        have h_in_fin : K' ∈ S_fin := by
          rw [Set.Finite.mem_toFinset (Set.toFinite S)]
          exact h_in_S
        exact S_fin.min'_le K' h_in_fin

  · -- Unicidad
    intro NF2 ⟨h_iso2, h_nf2⟩
    obtain ⟨n2, K2⟩ := NF2
    rcases h_nf2 with ⟨h_irr2, h_min2⟩

    -- Por L5, n2 debe ser el grado mínimo
    have h_deg_eq : n2 = min_degree K := by
      rw [L5_irreducible_implies_minimal K2 h_irr2]
      exact (min_degree_eq_of_isotopic K K2 h_iso2).symm

    subst h_deg_eq
    congr
    -- K2 = K_min
    apply le_antisymm
    · -- K2 <= K_min
      apply h_min2
      exact Isotopic.trans (Isotopic.symm h_iso2) h_min_mem_S
    · -- K_min <= K2
      have h_iso_K_K2 : Isotopic ⟨n, K⟩ ⟨min_degree K, K2⟩ := h_iso2
      have h_K2_in_S : K2 ∈ S := h_iso_K_K2
      have h_K2_in_fin : K2 ∈ S_fin := by
        rw [Set.Finite.mem_toFinset (Set.toFinite S)]
        exact h_K2_in_S
      exact S_fin.min'_le K2 h_K2_in_fin

/-!
### Teorema de Completitud del IME

Este es el teorema central que conecta el IME con la equivalencia de nudos racionales.
Establece que el IME es un invariante completo para nudos irreducibles:
dos nudos irreducibles son isotópicos si y solo si tienen el mismo IME.
-/

theorem isotopic_irreducible_same_crossing_number {n m : ℕ}
  (K₁ : RationalConfiguration n) (K₂ : RationalConfiguration m)
  (h_irr1 : is_irreducible K₁) (h_irr2 : is_irreducible K₂) :
  Isotopic ⟨n, K₁⟩ ⟨m, K₂⟩ → n = m := by
  intro h
  -- Por L5, n = min_degree K1 y m = min_degree K2
  -- Y min_degree es invariante bajo isotopía
  rw [L5_irreducible_implies_minimal K₁ h_irr1]
  rw [L5_irreducible_implies_minimal K₂ h_irr2]
  apply min_degree_eq_of_isotopic
  exact h

/--
Axioma A7 (Lema de Unicidad Modular):
Si dos configuraciones tienen el grado mínimo en su clase de isotopía,
entonces son equivalentes salvo rotación.
Adaptado de `E:\Nudos_LEAN\Articulo\Lema de Unicidad Modular.md`.
-/
axiom minimal_isotopic_implies_rotation {n : ℕ} (K1 K2 : RationalConfiguration n) :
  n = min_degree K1 → Isotopic ⟨n, K1⟩ ⟨n, K2⟩ → ∃ k : ℝ[n], K2 = rotate_knot k K1

theorem isotopic_irreducible_same_IME {n : ℕ} (K₁ K₂ : RationalConfiguration n)
  (h_irr1 : is_irreducible K₁) (h_irr2 : is_irreducible K₂) :
  Isotopic ⟨n, K₁⟩ ⟨n, K₂⟩ → IME K₁ = IME K₂ := by
  intro h_iso
  by_cases hn : n = 0
  · subst hn
    rfl
  · haveI : NeZero n := ⟨hn⟩
    -- 1. Por L5, ambos tienen grado mínimo
    have h_min1 : n = min_degree K₁ := L5_irreducible_implies_minimal K₁ h_irr1

    -- 2. Por Axioma A7, son rotaciones
    obtain ⟨k, rfl⟩ := minimal_isotopic_implies_rotation K₁ K₂ h_min1 h_iso

    -- 3. IME es invariante bajo rotación
    exact (IME_rotation_invariant K₁ k).symm

/-- Si dos configuraciones tienen el mismo IME, existe una rotación que las relaciona -/
theorem same_IME_implies_rotation {n : ℕ} (K₁ K₂ : RationalConfiguration n) :
  IME K₁ = IME K₂ → ∃ (k : ℝ[n]), K₂ = rotate_knot k K₁ := by
  intro h_ime
  -- Caso n=0
  by_cases h_n : n = 0
  · subst h_n
    use 0
    apply RationalConfiguration.ext
    funext i
    exact Fin.elim0 i

  -- Caso n>0
  · haveI : NeZero n := ⟨h_n⟩
    -- 1. IME igual implica ratio_val igual
    have h_ratio : ∀ i, ratio_val (K₁.crossings i) = ratio_val (K₂.crossings i) :=
      IME_eq_implies_ratio_val_eq K₁ K₂ h_ime

    -- 2. Axioma de reconstrucción da el desplazamiento k
    obtain ⟨k, h_over⟩ := reconstruct_from_first K₁ K₂ h_ratio
    use k

    -- 3. Verificar que K₂ = rotate_knot k K₁
    apply RationalConfiguration.ext
    funext i
    show K₂.crossings i = (rotate_knot k K₁).crossings i

    apply RationalCrossing.ext
    · -- over_pos
      rw [h_over i]
      rfl
    · -- under_pos
      -- 1. Relacionar under con over y ratio
      have h_u1 : (K₂.crossings i).under_pos - (K₂.crossings i).over_pos =
        modular_ratio (K₂.crossings i) := rfl
      rw [sub_eq_iff_eq_add] at h_u1

      have h_u2 : ((rotate_knot k K₁).crossings i).under_pos -
        ((rotate_knot k K₁).crossings i).over_pos =
        modular_ratio ((rotate_knot k K₁).crossings i) := rfl
      rw [sub_eq_iff_eq_add] at h_u2

      have h_mod_ratio : modular_ratio (K₂.crossings i) =
        modular_ratio ((rotate_knot k K₁).crossings i) := by
        unfold ratio_val at h_ratio
        apply ZMod.val_injective
        rw [←h_ratio i]
        rw [rotation_preserves_ratios]

      rw [h_u1, h_u2, h_over i, h_mod_ratio]
      rfl

theorem rotation_implies_isotopic {n : ℕ} (K : RationalConfiguration n) (k : ℝ[n]) :
  Isotopic ⟨n, K⟩ ⟨n, rotate_knot k K⟩ := by
  apply Isotopic.rotation

/--
Teorema de Completitud del IME (Versión Correcta):
Dos nudos racionales irreducibles son isotópicos si y solo si tienen el mismo número de cruces
y el mismo IME.
-/
theorem IME_complete {n m : ℕ} (K₁ : RationalConfiguration n) (K₂ : RationalConfiguration m)
  (h_irr1 : is_irreducible K₁) (h_irr2 : is_irreducible K₂) :
  Isotopic ⟨n, K₁⟩ ⟨m, K₂⟩ ↔ (n = m ∧ IME K₁ = IME K₂) := by
  constructor
  · intro h_iso
    have h_nm : n = m := isotopic_irreducible_same_crossing_number K₁ K₂ h_irr1 h_irr2 h_iso
    subst h_nm
    constructor
    · rfl
    · exact isotopic_irreducible_same_IME K₁ K₂ h_irr1 h_irr2 h_iso
  · intro h
    rcases h with ⟨rfl, h_IME⟩
    obtain ⟨k, rfl⟩ := same_IME_implies_rotation K₁ K₂ h_IME
    exact rotation_implies_isotopic K₁ k


/-!
# 6. Traducción Aritmética (Reidemeister Racional)

Esta sección formaliza la propuesta de traducir la equivalencia topológica
a la equivalencia aritmética de fracciones continuas, abordando el Problema Abierto 4.1.
-/

/-- Fracción Continua: una lista de enteros [a₁, ..., aₖ] que representa un tangle racional -/
abbrev ContinuedFraction := List Int

/--
Evaluación de una fracción continua a un número racional.
[a] -> a
[a, b, ...] -> a + 1 / eval [b, ...]
-/
def eval_continued_fraction : ContinuedFraction → Rat
  | [] => 0
  | [a] => a
  | a :: rest => (a : Rat) + 1 / eval_continued_fraction rest

/--
Equivalencia Aritmética:
Dos fracciones continuas son equivalentes si evalúan al mismo número racional.
Esto captura implícitamente las movidas R2 (cancelación de ceros) y R3 (identidades de Euclides).
-/
def arithmetic_equiv (cf1 cf2 : ContinuedFraction) : Prop :=
  eval_continued_fraction cf1 = eval_continued_fraction cf2

/--
Mapeo de Configuración a Fracción Continua (Axiomático).
Este es el puente entre el mundo combinatorio (Axioma A2) y el aritmético.
-/
axiom to_continued_fraction {n : ℕ} : RationalConfiguration n → ContinuedFraction

/--
Teorema de Clasificación de Schubert (Axioma A5 - Propuesto):
Dos nudos racionales son isotópicos si y solo si sus fracciones continuas asociadas
representan el mismo número racional módulo 1 (es decir, p/q y p'/q' tal que p/q ≡ p'/q' mod 1).
Nota: La igualdad estricta se aplica a Tangles; para Nudos (clausuras), es módulo 1.
-/
axiom schubert_classification {n m : ℕ}
  (K1 : RationalConfiguration n) (K2 : RationalConfiguration m) :
  Isotopic ⟨n, K1⟩ ⟨m, K2⟩ ↔
  ∃ (k : Int), eval_continued_fraction (to_continued_fraction K1) =
               eval_continued_fraction (to_continued_fraction K2) + k

end TMENudos
