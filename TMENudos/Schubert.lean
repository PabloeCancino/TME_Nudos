import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Topology.Basic
import Mathlib.Algebra.Polynomial.Basic
import TMENudos.Reidemeister

/-!
# Teoremas de Schubert sobre Nudos

Este archivo formaliza los teoremas fundamentales de Horst Schubert sobre
la estructura algebraica y geométrica de los nudos.

## Referencias Principales

- Schubert, H. (1949). "Die eindeutige Zerlegbarkeit eines Knotens in Primknoten"
- Schubert, H. (1953). "Knoten und Vollringe"
- Schubert, H. (1954). "Über eine numerische Knoteninvariante"

## Contenido

1. **Teorema de Descomposición Única** (1949)
2. **Teorema del Compañero** (Companion Theorem)
3. **Teorema sobre Nudos Satélites**
4. **Teorema del Índice de Puente** (Bridge Number)
5. **Teorema de la Suma Conexa**

-/

namespace TMENudos.SchubertTheorems

open TMENudos.Reidemeister
open TMENudos.Reidemeister.ReidemeisterMoves

/-- Un nudo como clase de equivalencia de diagramas bajo movimientos de Reidemeister -/
def Knot := Quotient DiagramSetoid

/-- Equivalencia topológica (isotopía ambiente) de nudos es la igualdad en el cociente -/
def knot_isotopic (K₁ K₂ : Knot) : Prop := K₁ = K₂

infix:50 " ≅ " => knot_isotopic

/-- El nudo trivial (unknot) es la clase del diagrama vacío -/
noncomputable def unknot : Knot :=
  Quotient.mk DiagramSetoid { n := 0, config := { crossings := fun x => x.elim0 } }

/-!
## 1. TEOREMA DE DESCOMPOSICIÓN ÚNICA DE SCHUBERT (1949)

El teorema más importante de Schubert, análogo al Teorema Fundamental
de la Aritmética para números.
-/

/-! ### Definiciones Preliminares -/

/-- Suma conexa de nudos: operación de "pegar" dos nudos -/
axiom connected_sum : Knot → Knot → Knot

infixl:65 " # " => connected_sum

/-- Un nudo es primo si no es trivial y no puede escribirse como suma conexa
    no trivial de dos nudos -/
def is_prime (K : Knot) : Prop :=
  K ≠ unknot ∧
  ∀ K₁ K₂ : Knot, K ≅ connected_sum K₁ K₂ → (K₁ ≅ unknot ∨ K₂ ≅ unknot)

/-- Propiedades básicas de la suma conexa -/
axiom connected_sum_comm (K₁ K₂ : Knot) : K₁ # K₂ ≅ K₂ # K₁

axiom connected_sum_assoc (K₁ K₂ K₃ : Knot) :
    (K₁ # K₂) # K₃ ≅ K₁ # (K₂ # K₃)

axiom connected_sum_unknot (K : Knot) : K # unknot ≅ K

/-- Ejemplos de nudos primos -/
axiom trefoil : Knot  -- Trébol 3₁
axiom figure_eight : Knot  -- Figura ocho 4₁
axiom cinquefoil : Knot  -- 5₁

axiom trefoil_is_prime : is_prime trefoil
axiom figure_eight_is_prime : is_prime figure_eight

/-!
### TEOREMA 1: DESCOMPOSICIÓN ÚNICA DE SCHUBERT (1949)

**Enunciado**: Todo nudo puede expresarse de manera única (salvo orden y
equivalencia) como suma conexa de nudos primos.

**Formulación matemática**:
```
∀ K : Knot, ∃! (primes : List Knot),
  (∀ P ∈ primes, is_prime P) ∧
  K ≅ primes.foldl (·#·) unknot
```

**Analogía con números**:
- Números naturales: n = p₁^e₁ · p₂^e₂ · ... · pₖ^eₖ
- Nudos: K = K₁ # K₂ # ... # Kₙ (donde cada Kᵢ es primo)

**Importancia histórica**:
- Publicado en 1949 en "Sitzungsberichte der Heidelberger Akademie"
- Título: "Die eindeutige Zerlegbarkeit eines Knotens in Primknoten"
- Resolvió un problema abierto desde los trabajos de Tait (1880s)
- Primera estructura algebraica profunda en teoría de nudos
-/

/-- **Axioma (Schubert 1949, existencia).** Todo nudo es suma conexa de una lista finita
    de nudos primos. Es un teorema profundo ya establecido (Schubert, "Die eindeutige
    Zerlegbarkeit eines Knotens in Primknoten", 1949), que depende de la teoría de
    3-variedades y no se formaliza aquí; ver el principio rector del mapa de ruta.

    CAMBIO (etapa de saneamiento de Schubert): antes `prime_decomposition` se definía con
    `Classical.choice sorry` y sus dos propiedades eran axiomas, la primera con la
    disyunción `is_prime P ∨ P ≅ unknot`. Ahora hay un único axioma de existencia y las
    dos propiedades son teoremas (la primera, sin nudos triviales: `is_prime P`). -/
axiom schubert_existence_axiom (K : Knot) :
    ∃ primes : List Knot,
      (∀ P ∈ primes, is_prime P) ∧ K ≅ primes.foldl (· # ·) unknot

/-- Descomposición en factores primos de un nudo (una elegida con `Classical.choose`) -/
noncomputable def prime_decomposition (K : Knot) : List Knot :=
  Classical.choose (schubert_existence_axiom K)

/-- Todo elemento de la descomposición prima es un nudo primo -/
theorem prime_decomposition_prime (K : Knot) :
    ∀ P ∈ prime_decomposition K, is_prime P :=
  (Classical.choose_spec (schubert_existence_axiom K)).1

/-- La descomposición reconstruye el nudo original -/
theorem prime_decomposition_reconstructs (K : Knot) :
    K ≅ (prime_decomposition K).foldl (·#·) unknot :=
  (Classical.choose_spec (schubert_existence_axiom K)).2

/--
**TEOREMA DE SCHUBERT - EXISTENCIA**

Todo nudo admite una factorización prima.
-/
theorem schubert_existence (K : Knot) :
    ∃ (primes : List Knot),
      (∀ P ∈ primes, is_prime P) ∧
      K ≅ primes.foldl (·#·) unknot := by
  exact ⟨prime_decomposition K, prime_decomposition_prime K,
    prime_decomposition_reconstructs K⟩

/--
**TEOREMA DE SCHUBERT - UNICIDAD**

La descomposición prima es única salvo:
1. Orden de los factores (por conmutatividad)
2. Equivalencia topológica de cada factor

Esta es la parte más difícil del teorema. La prueba original de Schubert
usa teoría de 3-variedades y esferas incompresibles.

CAMBIO: antes era un teorema con `sorry`. Se declara **axioma** (Schubert 1949, unicidad),
por ser un resultado profundo ya establecido; ver el principio rector del mapa de ruta.
-/
axiom schubert_uniqueness (K : Knot)
    (primes₁ primes₂ : List Knot)
    (h₁ : ∀ P ∈ primes₁, is_prime P)
    (h₂ : ∀ P ∈ primes₂, is_prime P)
    (hK₁ : K ≅ primes₁.foldl (· # ·) unknot)
    (hK₂ : K ≅ primes₂.foldl (· # ·) unknot) :
    ∃ (σ : Fin primes₁.length ≃ Fin primes₂.length),
      ∀ i : Fin primes₁.length,
        primes₁.get i ≅ primes₂.get (σ i)

/-- La suma conexa iterada no depende del orden de los factores (por conmutatividad y
    asociatividad). -/
theorem foldl_perm {l l' : List Knot} (h : l.Perm l') :
    l.foldl (· # ·) unknot = l'.foldl (· # ·) unknot := by
  haveI : RightCommutative (fun (a b : Knot) => a # b) :=
    ⟨fun a b c => by
      have h1 : (a # b) # c = a # (b # c) := connected_sum_assoc a b c
      have h2 : b # c = c # b := connected_sum_comm b c
      have h3 : (a # c) # b = a # (c # b) := connected_sum_assoc a c b
      rw [h1, h2, h3]⟩
  exact h.foldl_eq _

/--
**TEOREMA DE DESCOMPOSICIÓN ÚNICA - VERSIÓN COMPLETA**

Existencia + Unicidad
-/
theorem schubert_unique_factorization :
    ∀ K : Knot, ∃! (primes : Multiset Knot),
      (∀ P ∈ primes, is_prime P) ∧
      K ≅ primes.toList.foldl (·#·) unknot := by
  intro K
  refine ⟨(prime_decomposition K : Multiset Knot), ⟨?_, ?_⟩, ?_⟩
  · intro P hP
    exact prime_decomposition_prime K P (Multiset.mem_coe.mp hP)
  · have hperm : (Multiset.toList (prime_decomposition K : Multiset Knot)).Perm
        (prime_decomposition K) := Multiset.coe_eq_coe.mp (by simp)
    rw [foldl_perm hperm]
    exact prime_decomposition_reconstructs K
  · rintro m ⟨hm₁, hm₂⟩
    obtain ⟨σ, hσ⟩ := schubert_uniqueness K (prime_decomposition K) m.toList
      (prime_decomposition_prime K)
      (fun P hP => hm₁ P (Multiset.mem_toList.mp hP))
      (prime_decomposition_reconstructs K) hm₂
    have hget : (prime_decomposition K).get =
        m.toList.get ∘ σ := funext fun i => hσ i
    calc m = (m.toList : Multiset Knot) := (Multiset.coe_toList m).symm
      _ = Finset.univ.val.map m.toList.get := by
          rw [Fin.univ_val_map, List.ofFn_get]
      _ = Finset.univ.val.map (m.toList.get ∘ σ) := by
          rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
      _ = Finset.univ.val.map (prime_decomposition K).get := by rw [hget]
      _ = (prime_decomposition K : Multiset Knot) := by
          rw [Fin.univ_val_map, List.ofFn_get]

/-!
### Lemas auxiliares sobre la suma conexa iterada y la longitud de la descomposición

Con la unicidad (axioma de Schubert) la longitud de `prime_decomposition K` no depende de
la factorización elegida: es la de cualquier factorización prima de `K`.
-/

/-- El nudo trivial es neutro a la izquierda de la suma conexa. -/
theorem unknot_sum (K : Knot) : unknot # K = K :=
  Eq.trans (connected_sum_comm unknot K) (connected_sum_unknot K)

/-- Desplazar el acumulador del `foldl` de la suma conexa. -/
theorem foldl_shift (l : List Knot) (a : Knot) :
    l.foldl (· # ·) a = a # l.foldl (· # ·) unknot := by
  induction l generalizing a with
  | nil => exact (connected_sum_unknot a).symm
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (a # x), ih (unknot # x), unknot_sum]
    exact connected_sum_assoc a x _

/-- La suma conexa iterada de una concatenación. -/
theorem foldl_append (l₁ l₂ : List Knot) :
    (l₁ ++ l₂).foldl (· # ·) unknot =
      l₁.foldl (· # ·) unknot # l₂.foldl (· # ·) unknot := by
  rw [List.foldl_append, foldl_shift l₂]

/-- Cualquier factorización prima de `K` tiene la misma longitud que `prime_decomposition K`
    (consecuencia de la unicidad). -/
theorem decomposition_length_eq (K : Knot) (l : List Knot)
    (hl : ∀ P ∈ l, is_prime P) (hK : K ≅ l.foldl (· # ·) unknot) :
    (prime_decomposition K).length = l.length := by
  obtain ⟨σ, _⟩ := schubert_uniqueness K (prime_decomposition K) l
    (prime_decomposition_prime K) hl (prime_decomposition_reconstructs K) hK
  exact Fin.equiv_iff_eq.mp ⟨σ⟩

/-- La longitud de la descomposición prima es aditiva bajo la suma conexa. -/
theorem decomposition_length_add (K₁ K₂ : Knot) :
    (prime_decomposition (K₁ # K₂)).length =
      (prime_decomposition K₁).length + (prime_decomposition K₂).length := by
  have e₁ : K₁ = (prime_decomposition K₁).foldl (· # ·) unknot :=
    prime_decomposition_reconstructs K₁
  have e₂ : K₂ = (prime_decomposition K₂).foldl (· # ·) unknot :=
    prime_decomposition_reconstructs K₂
  have h := decomposition_length_eq (K₁ # K₂)
    (prime_decomposition K₁ ++ prime_decomposition K₂)
    (by
      intro P hP
      rcases List.mem_append.mp hP with h | h
      · exact prime_decomposition_prime K₁ P h
      · exact prime_decomposition_prime K₂ P h)
    (by
      change K₁ # K₂ = _
      rw [foldl_append, ← e₁, ← e₂])
  rw [h, List.length_append]

/-- Un nudo cuya descomposición prima es vacía es el nudo trivial, y recíprocamente. -/
theorem decomposition_nil_iff (K : Knot) :
    prime_decomposition K = [] ↔ K = unknot := by
  constructor
  · intro h
    have e : K = (prime_decomposition K).foldl (· # ·) unknot :=
      prime_decomposition_reconstructs K
    rw [h] at e
    exact e
  · intro h
    have h0 := decomposition_length_eq K [] (by simp)
      (by rw [h]; rfl)
    exact List.length_eq_zero_iff.mp h0

/-!
## 2. TEOREMA DEL COMPAÑERO (COMPANION THEOREM)

Relaciona nudos satélites con sus "nudos compañeros".
-/

/-- Un nudo K es satélite de P si K puede obtenerse "envolviendo"
    una curva alrededor de P de manera no trivial -/
def is_satellite (K P : Knot) : Prop := sorry

/-- El patrón de un nudo satélite -/
noncomputable def satellite_pattern (K P : Knot) (h : is_satellite K P) : Knot := sorry

/--
**TEOREMA DEL COMPAÑERO (Schubert, 1953)**

Si K es un nudo satélite con compañero P, entonces:
1. El género de K es mayor o igual que el género de P
2. Existe una factorización canónica K = pattern(P)

**Formulación**: Un nudo satélite "hereda" complejidad de su compañero.
-/
axiom knot_genus : Knot → ℕ

theorem schubert_companion_theorem (K P : Knot) (h : is_satellite K P) :
    knot_genus K ≥ knot_genus P ∧
    ∃ (pattern : Knot), K ≅ sorry := by  -- Construcción del satélite
  sorry

/-!
## 3. TEOREMA SOBRE NUDOS TÓRICOS

Schubert clasificó completamente los nudos tóricos.
-/

/-- Un nudo tórico T(p,q) vive en la superficie de un toro -/
noncomputable def torus_knot (p q : ℕ) : Knot := sorry

/--
**TEOREMA DE SCHUBERT SOBRE NUDOS TÓRICOS (1949)**

1. T(p,q) es primo si y solo si gcd(p,q) = 1
2. T(p,q) ≅ T(q,p)
3. T(p,q) ≅ T(-p,-q) (nudo espejo)
4. El género de T(p,q) es (p-1)(q-1)/2
-/
theorem schubert_torus_knot_primality (p q : ℕ) :
    is_prime (torus_knot p q) ↔ Nat.gcd p q = 1 := by
  sorry

theorem schubert_torus_knot_symmetry (p q : ℕ) :
    torus_knot p q ≅ torus_knot q p := by
  sorry

theorem schubert_torus_knot_genus (p q : ℕ) (h : Nat.gcd p q = 1) :
    knot_genus (torus_knot p q) = (p - 1) * (q - 1) / 2 := by
  sorry

/-!
## 4. TEOREMA DEL ÍNDICE DE PUENTE (BRIDGE NUMBER)

El índice de puente mide cuántos "puentes" necesita un nudo.
-/

/-- El índice de puente de un nudo: número mínimo de arcos "sobre"
    en cualquier proyección -/
axiom bridge_number : Knot → ℕ

/--
**PROPIEDADES DEL ÍNDICE DE PUENTE (Schubert, 1954)**

1. bridge_number(unknot) = 1
2. bridge_number(K) = 1 ⟺ K ≅ unknot
3. bridge_number es un invariante de nudos
4. bridge_number(K₁ # K₂) = bridge_number(K₁) + bridge_number(K₂) - 1
-/
theorem bridge_number_unknot_val : bridge_number unknot = 1 := by
  sorry

-- theorem bridge_number_isotopy (K₁ K₂ : Knot) :
--     K₁ ≅ K₂ → bridge_number K₁ = bridge_number K₂ := by
--   sorry

/--
**TEOREMA DE ADITIVIDAD DEL ÍNDICE DE PUENTE**

Este es un resultado profundo de Schubert.
-/
theorem schubert_bridge_number_additivity (K₁ K₂ : Knot) :
    bridge_number (K₁ # K₂) =
    bridge_number K₁ + bridge_number K₂ - 1 := by
  sorry

/-!
## 5. TEOREMA DE LA 3-ESFERA DE SCHUBERT

Sobre la topología de complementos de nudos.
-/

/-- El complemento de un nudo K en S³ -/
axiom knot_complement : Knot → Type  -- Should be a 3-manifold

/-- El grupo fundamental del complemento -/
axiom knot_group : Knot → Type  -- Should be a Group

/--
**TEOREMA DE SCHUBERT SOBRE COMPLEMENTOS**

Si K₁ # K₂ = K, entonces el complemento de K es la suma conexa
de los complementos de K₁ y K₂.

Esto establece una correspondencia entre la suma de nudos y
la suma conexa de 3-variedades.
-/
axiom manifold_connected_sum : Type → Type → Type

theorem schubert_complement_sum (K₁ K₂ : Knot) :
    knot_complement (K₁ # K₂) =
    manifold_connected_sum (knot_complement K₁) (knot_complement K₂) := by
  sorry

/-!
## 6. APLICACIONES DE LOS TEOREMAS DE SCHUBERT
-/

/-- **Aplicación 1: Clasificación de Nudos Simples**

Usando la descomposición prima, podemos clasificar nudos
por sus factores primos.
-/
noncomputable def knot_complexity (K : Knot) : ℕ :=
  (prime_decomposition K).length

theorem complexity_additive (K₁ K₂ : Knot) :
    knot_complexity (K₁ # K₂) ≤
    knot_complexity K₁ + knot_complexity K₂ := by
  unfold knot_complexity
  exact (decomposition_length_add K₁ K₂).le

/-- **Aplicación 2: Detección de Nudos Compuestos**

Un nudo es compuesto si y solo si su descomposición prima
tiene más de un factor.
-/
def is_composite (K : Knot) : Prop :=
  (prime_decomposition K).length > 1

theorem composite_characterization (K : Knot) :
    is_composite K ↔
    ∃ K₁ K₂, (K ≅ K₁ # K₂) ∧ (K₁ ≠ unknot) ∧ (K₂ ≠ unknot) := by
  constructor
  · intro hc
    unfold is_composite at hc
    have e : K = (prime_decomposition K).foldl (· # ·) unknot :=
      prime_decomposition_reconstructs K
    have hp := prime_decomposition_prime K
    generalize prime_decomposition K = l at hc e hp
    match l, hc, e, hp with
    | a :: b :: rest, _, e, hp =>
      have hne : (b :: rest).foldl (· # ·) unknot ≠ unknot := by
        intro h0
        have hlen := decomposition_length_eq unknot (b :: rest)
          (fun P hP => hp P (List.mem_cons_of_mem _ hP)) h0.symm
        have hnil := (decomposition_nil_iff unknot).mpr rfl
        rw [hnil] at hlen
        simp at hlen
      refine ⟨a, (b :: rest).foldl (· # ·) unknot, ?_, (hp a (by simp)).1, hne⟩
      change K = a # _
      rw [e, List.foldl_cons, foldl_shift, unknot_sum]
  · rintro ⟨K₁, K₂, hK, h₁, h₂⟩
    unfold is_composite
    have hK' : K = K₁ # K₂ := hK
    rw [hK', decomposition_length_add]
    have n₁ : (prime_decomposition K₁).length ≠ 0 := fun h0 =>
      h₁ ((decomposition_nil_iff K₁).mp (List.length_eq_zero_iff.mp h0))
    have n₂ : (prime_decomposition K₂).length ≠ 0 := fun h0 =>
      h₂ ((decomposition_nil_iff K₂).mp (List.length_eq_zero_iff.mp h0))
    omega

/-- **Aplicación 3: Cálculo del Género**

El género de una suma conexa es la suma de los géneros.
-/
theorem genus_additive (K₁ K₂ : Knot) :
    knot_genus (K₁ # K₂) = knot_genus K₁ + knot_genus K₂ := by
  sorry

/-!
## 7. COMPARACIÓN CON OTROS RESULTADOS
-/

/-- **Relación con el Teorema de Reidemeister**

Los movimientos de Reidemeister preservan la descomposición prima.

Saneamiento 0.3: antes existía `axiom reidemeister_equivalent : Knot → Knot → Prop`
(chocaba con `Reidemeister.reidemeister_equivalent`, ahora inductiva sobre `KnotConfig`)
y el teorema tenía `sorry`. En el cociente `Knot` la equivalencia de Reidemeister es la
igualdad, así que la hipótesis pasa a ser `K₁ ≅ K₂` y el teorema se demuestra.
-/
theorem reidemeister_preserves_decomposition (K₁ K₂ : Knot) :
    K₁ ≅ K₂ →
    (prime_decomposition K₁).length = (prime_decomposition K₂).length := by
  intro h
  exact congrArg (fun K => (prime_decomposition K).length) h

/-- **Relación con Invariantes Polinomiales**

El polinomio de Alexander de una suma es el producto
de los polinomios de los sumandos.
-/
axiom alexander_polynomial : Knot → Polynomial ℤ

theorem alexander_multiplicative (K₁ K₂ : Knot) :
    alexander_polynomial (K₁ # K₂) =
    alexander_polynomial K₁ * alexander_polynomial K₂ := by
  sorry

/-!
## 8. GENERALIZACIONES MODERNAS
-/

/-- **JSJ Decomposition (Jaco-Shalen-Johannson)**

Generalización moderna del teorema de Schubert a 3-variedades generales.
-/
axiom ThreeManifold : Type

axiom JSJ_decomposition : ThreeManifold → List ThreeManifold

/-- El teorema de Schubert es un caso especial de JSJ para
    complementos de nudos -/
theorem schubert_is_JSJ_special_case (K : Knot) :
    ∃ (decomp : List Knot),
      prime_decomposition K = decomp ∧
      sorry  -- Relación con JSJ
  := by
  sorry

/-!
## 9. COMPLEJIDAD COMPUTACIONAL
-/

/-- **Problema de Factorización de Nudos**

Dado un nudo K, encontrar su descomposición prima.
-/
noncomputable def factorization_problem (K : Knot) :
    {primes : List Knot // ∀ P ∈ primes, is_prime P} :=
  ⟨prime_decomposition K, prime_decomposition_prime K⟩

/-- **Resultado de Complejidad (Agol-Hass-Thurston, 2002)**

El problema de determinar si un nudo es primo está en NP.
-/
axiom knot_primality_in_NP :
    ∃ (verifier : Knot → Bool),
      ∀ K : Knot, verifier K = true ↔ is_prime K

/-!
## 10. EJEMPLOS CONCRETOS
-/

/-- Ejemplo 1: El nudo de la abuela (granny knot): la suma conexa de dos tréboles de la
    misma quiralidad, `trefoil # trefoil`.

    CAMBIO DE NOMBRE: antes esta definición se llamaba `square_knot` y la de `trefoil # mirror
    trefoil` se llamaba `granny_knot`; estaban intercambiadas. El nudo cuadrado es el trébol
    sumado con su imagen especular, y el nudo de la abuela es el trébol sumado consigo mismo.
    Los teoremas de abajo (`granny_knot_composite`, `granny_knot_decomposition`, antes
    `square_knot_composite` y `square_knot_decomposition`) no cambian de contenido. -/
noncomputable def granny_knot : Knot := trefoil # trefoil

theorem granny_knot_composite :
    is_composite granny_knot := by
  unfold is_composite granny_knot
  have h := decomposition_length_eq (trefoil # trefoil) [trefoil, trefoil]
    (by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl <;> exact trefoil_is_prime)
    (by simp [List.foldl, unknot_sum]; rfl)
  rw [h]
  decide

theorem granny_knot_decomposition :
    prime_decomposition granny_knot = [trefoil, trefoil] := by
  have hprimes : ∀ P ∈ [trefoil, trefoil], is_prime P := by
    intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl <;> exact trefoil_is_prime
  have hfold : granny_knot ≅ [trefoil, trefoil].foldl (· # ·) unknot := by
    change granny_knot = _
    simp [granny_knot, List.foldl, unknot_sum]
  obtain ⟨σ, hσ⟩ := schubert_uniqueness granny_knot (prime_decomposition granny_knot)
    [trefoil, trefoil] (prime_decomposition_prime granny_knot) hprimes
    (prime_decomposition_reconstructs granny_knot) hfold
  have hlen : (prime_decomposition granny_knot).length = 2 :=
    Fin.equiv_iff_eq.mp ⟨σ⟩
  have hget : ∀ j : Fin [trefoil, trefoil].length, [trefoil, trefoil].get j = trefoil := by
    intro j
    fin_cases j <;> rfl
  have hall : ∀ x ∈ prime_decomposition granny_knot, x = trefoil := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
    exact (hσ i).trans (hget (σ i))
  exact (List.eq_replicate_iff.mpr ⟨hlen, hall⟩).trans rfl

/-- Ejemplo 2: El nudo cuadrado (square knot): la suma conexa de un trébol con su imagen
    especular, `trefoil # mirror trefoil`. (Antes se llamaba `granny_knot`; ver el ejemplo 1.) -/
axiom mirror : Knot → Knot

noncomputable def square_knot : Knot := trefoil # mirror trefoil

/-- El nudo de la abuela y el nudo cuadrado son distintos. (El enunciado no cambia con el
    intercambio de nombres: es simétrico en esta forma.) -/
theorem granny_distinct_from_square :
    ¬(granny_knot ≅ square_knot) := by
  sorry

/-- Ejemplo 3: Suma de nudos primos diferentes -/
noncomputable def example_composite : Knot := trefoil # figure_eight

theorem example_has_two_prime_factors :
    (prime_decomposition example_composite).length = 2 := by
  have h := decomposition_length_eq example_composite [trefoil, figure_eight]
    (by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact trefoil_is_prime
      · exact figure_eight_is_prime)
    (by simp [example_composite, List.foldl, unknot_sum]; rfl)
  rw [h]
  rfl

end TMENudos.SchubertTheorems
