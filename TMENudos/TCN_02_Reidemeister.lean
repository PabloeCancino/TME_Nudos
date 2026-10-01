-- TCN_02_Reidemeister.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 2 - Movimientos Reidemeister

import TMENudos.TCN_01_Fundamentos

/-!
# Bloque 2: Movimientos Reidemeister

Este módulo define los movimientos de Reidemeister R1 y R2 en el contexto
combinatorio de configuraciones K₃ sobre Z/6Z.

## Contenido Principal

1. **Movimiento R1**: Tuplas consecutivas [i, i±1]
2. **Movimiento R2**: Pares de tuplas adyacentes
3. **Predicados decidibles**: hasR1, hasR2
4. **Conteos**: Configuraciones con R1 y R2

## Propiedades

- ✅ **Completo**: Todos los predicados son decidibles
- ✅ **Depende solo de**: Bloque 1
- ✅ **Conteos demostrados (firmados)**: 704 con R1, 264 con R2
- ✅ **Documentado**: Ejemplos y explicaciones

## Resultados Principales

- `isConsecutive`: Caracterización de tuplas consecutivas
- `formsR2Pattern`: Caracterización de pares R2
- Conteos: 704/960 configuraciones tienen R1, 264/960 tienen R2, 172/960 ninguno

## Referencias

- Reidemeister moves: Movimientos que preservan el tipo de nudo
- R1: Eliminar/agregar una "lazada" simple
- R2: Eliminar/agregar dos cruces adyacentes

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open OrderedPair K3Config

/-! ## Movimiento Reidemeister R1 -/

/-- Una tupla [a,b] es consecutiva si b = a+1 o b = a-1 en Z/6Z.

    Interpretación geométrica: Representa una "lazada simple" que puede
    eliminarse sin cambiar el tipo de nudo. -/
def isConsecutive (p : OrderedPair) : Prop :=
  p.snd = p.fst + 1 ∨ p.snd = p.fst - 1

/-- Decidibilidad de consecutividad -/
instance (p : OrderedPair) : Decidable (isConsecutive p) := by
  unfold isConsecutive
  infer_instance

/-- Una configuración tiene movimiento R1 si contiene al menos una tupla consecutiva -/
def hasR1 (K : K3Config) : Prop :=
  ∃ p ∈ K.pairs, isConsecutive p

/-- Decidibilidad de hasR1 -/
instance (K : K3Config) : Decidable (hasR1 K) := by
  unfold hasR1
  infer_instance

/-- Ejemplos de tuplas consecutivas -/
example : isConsecutive (OrderedPair.make 0 1 (by decide) true) := by
  unfold isConsecutive
  left
  decide

example : isConsecutive (OrderedPair.make 3 2 (by decide) false) := by
  unfold isConsecutive
  right
  decide

example : ¬isConsecutive (OrderedPair.make 0 2 (by decide) true) := by
  unfold isConsecutive
  push Not
  constructor <;> decide

/-- Número de configuraciones firmadas con movimiento R1.

    MIGRACIÓN (cifra): antes → después
    - antes: 88 de 120. Después: 704 de 960 (= 88 · 8: R1 no mira el signo, así que cada
      configuración sin signo con R1 da sus 8 asignaciones de signos). La fracción 11/15 no cambia.
    - Demostrado por `decide +kernel` en `counts_signed` (abajo). -/
def numConfigsWithR1 : ℕ := 704

/-- Fórmula: 704/960 = 11/15 de las configuraciones tienen R1 -/
theorem configs_with_r1_probability :
  (numConfigsWithR1 : ℚ) / totalConfigs = 11 / 15 := by
  unfold numConfigsWithR1 totalConfigs
  norm_num

/-! ## Movimiento Reidemeister R2 -/

/-- Dos tuplas [a,b] y [c,d] forman un patrón R2 si:
    - Signos OPUESTOS (`p.pos ≠ q.pos`)
    - Numeradores consecutivos: |c - a| = 1
    - Denominadores consecutivos: |d - b| = 1

    MIGRACIÓN (regla 4, signo como dato): antes → después
    - antes: solo las condiciones de posición (sin signo).
    - después: se añade `p.pos ≠ q.pos` (un R2 cancela dos cruces de signos opuestos; es lo que
      se demostró en `Etapa1_R2`). R1 (`isConsecutive`) admite cualquier signo.

    Esto produce 4 combinaciones:
    - Paralelo:     (c,d) = (a±1, b±1) con mismo signo
    - Antiparalelo: (c,d) = (a±1, b∓1) con signos opuestos

    Interpretación geométrica: Dos cruces adyacentes que se cancelan. -/
def formsR2Pattern (p q : OrderedPair) : Prop :=
  p.pos ≠ q.pos ∧
  ((q.fst = p.fst + 1 ∧ q.snd = p.snd + 1) ∨  -- Paralelo +
   (q.fst = p.fst - 1 ∧ q.snd = p.snd - 1) ∨  -- Paralelo -
   (q.fst = p.fst + 1 ∧ q.snd = p.snd - 1) ∨  -- Antiparalelo +
   (q.fst = p.fst - 1 ∧ q.snd = p.snd + 1))   -- Antiparalelo -

/-- Decidibilidad de formsR2Pattern -/
instance (p q : OrderedPair) : Decidable (formsR2Pattern p q) := by
  unfold formsR2Pattern
  infer_instance

/-- Una configuración tiene movimiento R2 si contiene un par con patrón R2 -/
def hasR2 (K : K3Config) : Prop :=
  ∃ p ∈ K.pairs, ∃ q ∈ K.pairs, p ≠ q ∧ formsR2Pattern p q

/-- Decidibilidad de hasR2 -/
instance (K : K3Config) : Decidable (hasR2 K) := by
  unfold hasR2
  infer_instance

/-- Ejemplo de par R2: [0,2]+ y [1,3]- forman patrón paralelo con signos opuestos -/
example : formsR2Pattern
  (OrderedPair.make 0 2 (by decide) true)
  (OrderedPair.make 1 3 (by decide) false) := by
  unfold formsR2Pattern
  refine ⟨by decide, Or.inl ?_⟩
  constructor <;> decide

/-- Con signos iguales NO hay patrón R2 (nuevo con el signo como dato). -/
example : ¬ formsR2Pattern
  (OrderedPair.make 0 2 (by decide) true)
  (OrderedPair.make 1 3 (by decide) true) := by
  decide

/-- Número de pares ORDENADOS (p, q) de tuplas firmadas distintas con patrón R2.

    MIGRACIÓN (cifra): antes → después
    - antes: la constante `numR2Pairs = 48`, SIN demostración y que no coincide con el cómputo:
      contando con la definición sin signo hay 108 pares ordenados (54 no ordenados).
    - después: 216 pares ordenados (= 2 · 108: para cada pareja de posiciones con patrón R2 hay
      exactamente 2 asignaciones de signos opuestos). Ahora SÍ demostrado (`r2_pairs_count`). -/
def numR2Pairs : ℕ := 216

theorem r2_pairs_count :
    (Finset.univ.filter (fun x : OrderedPair × OrderedPair =>
      x.1 ≠ x.2 ∧ formsR2Pattern x.1 x.2)).card = numR2Pairs := by
  decide +kernel

/-- Número de configuraciones firmadas con movimiento R2 (con signos opuestos).

    MIGRACIÓN (cifra): antes → después
    - antes: la constante `104` (de 120), sin demostración; el cómputo con la definición sin signo
      da 60 de 120, así que la cifra antigua era incorrecta.
    - después: 264 de 960, demostrado por `decide +kernel` en `counts_signed`. -/
def numConfigsWithR2 : ℕ := 264

/-- Fórmula: 264/960 = 11/40 de las configuraciones firmadas tienen R2 -/
theorem configs_with_r2_probability :
  (numConfigsWithR2 : ℚ) / totalConfigs = 11 / 40 := by
  unfold numConfigsWithR2 totalConfigs
  norm_num

/-! ## Configuraciones sin R1 ni R2 -/

/-- Número de configuraciones firmadas sin R1 ni R2.

    MIGRACIÓN (cifra): antes → después: 14 de 120 → 172 de 960 (demostrado en `counts_signed`).
    Con el signo dato, R2 exige signos opuestos y por eso hay MÁS irreducibles. Según la regla 8
    del plan, "irreducible" sobrecuenta (incluye diagramas no planos): la clasificación con
    sentido pide además índice cero (Etapa 3). -/
def numConfigsNoR1NoR2 : ℕ := 172

/-- Probabilidad de que una configuración firmada no tenga R1 ni R2 (antes 7/60) -/
theorem probability_no_r1_no_r2 :
  (numConfigsNoR1NoR2 : ℚ) / totalConfigs = 43 / 240 := by
  norm_num [numConfigsNoR1NoR2, totalConfigs]

/-- **Conteos firmados** (los tres a la vez, una sola enumeración de las 960 configuraciones):
    704 con R1, 264 con R2 y 172 sin R1 ni R2. -/
theorem counts_signed :
    (Finset.univ.filter (fun K : K3Config => hasR1 K)).card = numConfigsWithR1 ∧
    (Finset.univ.filter (fun K : K3Config => hasR2 K)).card = numConfigsWithR2 ∧
    (Finset.univ.filter (fun K : K3Config => ¬hasR1 K ∧ ¬hasR2 K)).card =
      numConfigsNoR1NoR2 := by
  decide +kernel

/-! ## Propiedades de los Movimientos -/

/-- R1 es una propiedad local de tuplas individuales -/
theorem r1_local (K : K3Config) (p : OrderedPair) (hp : p ∈ K.pairs) :
  isConsecutive p → hasR1 K := by
  intro h
  unfold hasR1
  exact ⟨p, hp, h⟩

/-- R2 es una propiedad de pares de tuplas -/
theorem r2_pairwise (K : K3Config) (p q : OrderedPair)
    (hp : p ∈ K.pairs) (hq : q ∈ K.pairs) (hne : p ≠ q) :
  formsR2Pattern p q → hasR2 K := by
  intro h
  unfold hasR2
  exact ⟨p, hp, q, hq, hne, h⟩

/-- Si una configuración no tiene R1, ninguna de sus tuplas es consecutiva -/
theorem not_hasR1_iff (K : K3Config) :
  ¬hasR1 K ↔ ∀ p ∈ K.pairs, ¬isConsecutive p := by
  unfold hasR1
  push Not
  rfl

/-- Si una configuración no tiene R2, ningún par forma patrón R2 -/
theorem not_hasR2_iff (K : K3Config) :
  ¬hasR2 K ↔ ∀ p ∈ K.pairs, ∀ q ∈ K.pairs, p ≠ q → ¬formsR2Pattern p q := by
  unfold hasR2
  push Not
  rfl

/-! ## Simetría de Movimientos -/

/-- La inversión de una tupla consecutiva es también consecutiva -/
theorem consecutive_reverse (p : OrderedPair) :
  isConsecutive p → isConsecutive p.reverse := by
  intro h
  unfold isConsecutive at h ⊢
  unfold OrderedPair.reverse
  simp only
  rcases h with h1 | h2
  · right; rw [h1]; ring
  · left; rw [h2]; ring

/-- El patrón R2 es simétrico bajo intercambio de tuplas -/
theorem r2_symmetric (p q : OrderedPair) :
  formsR2Pattern p q → formsR2Pattern q p := by
  intro h
  unfold formsR2Pattern at h ⊢
  obtain ⟨hs, h⟩ := h
  refine ⟨hs.symm, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- q.fst = p.fst + 1, q.snd = p.snd + 1 → p.fst = q.fst - 1, p.snd = q.snd - 1
    right; left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- q.fst = p.fst - 1, q.snd = p.snd - 1 → p.fst = q.fst + 1, p.snd = q.snd + 1
    left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- q.fst = p.fst + 1, q.snd = p.snd - 1 → p.fst = q.fst - 1, p.snd = q.snd + 1
    right; right; right
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- q.fst = p.fst - 1, q.snd = p.snd + 1 → p.fst = q.fst + 1, p.snd = q.snd - 1
    right; right; left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring


/-! ## Movimiento Reidemeister R3 -/

/-- Tres tuplas [p, q, r] forman un patrón R3 si son distintas dos a dos.
    En el contexto de K3, esto corresponde a la configuración global de 3 tuplas.

    Interpretación geométrica: "Movimiento de Triángulo".
    Permite deslizar una hebra sobre el cruce de las otras dos. -/
def formsR3Pattern (p q r : OrderedPair) : Prop :=
  p ≠ q ∧ q ≠ r ∧ r ≠ p

/-- Decidibilidad del patrón R3 -/
instance (p q r : OrderedPair) : Decidable (formsR3Pattern p q r) := by
  unfold formsR3Pattern
  infer_instance

/-- Una configuración tiene movimiento R3 si contiene 3 tuplas distintas que forman el patrón.
    NOTA: En K3, esto es siempre verdadero por definición (card = 3). -/
def hasR3 (K : K3Config) : Prop :=
  ∃ p ∈ K.pairs, ∃ q ∈ K.pairs, ∃ r ∈ K.pairs, formsR3Pattern p q r

/-- Decidibilidad de hasR3 -/
instance (K : K3Config) : Decidable (hasR3 K) := by
  unfold hasR3
  infer_instance

/-- Teorema: Toda configuración K3 tiene movimiento R3 (siempre existen 3 pares distintos) -/
theorem k3_always_has_r3 (K : K3Config) : hasR3 K := by
  unfold hasR3 formsR3Pattern
  have h_card : K.pairs.card = 3 := K.card_eq
  rw [Finset.card_eq_three] at h_card
  obtain ⟨p, q, r, hpq, hpr, hqr, h_eq⟩ := h_card
  use p; constructor
  · rw [h_eq]; simp
  use q; constructor
  · rw [h_eq]; simp
  use r; constructor
  · rw [h_eq]; simp
  exact ⟨hpq, hqr, hpr.symm⟩

/-! ## Resumen del Bloque 2 -/

/-
## Estado del Bloque

✅ **Predicados decidibles**: hasR1, hasR2
✅ **Conteos demostrados**: 704 con R1, 264 con R2, 172 sin ninguno (de 960)
✅ **Propiedades probadas**: Simetría, localidad
✅ **Depende de**: Solo Bloque 1

## Definiciones Exportadas

- `isConsecutive`: Tupla consecutiva
- `formsR2Pattern`: Par con patrón R2
- `hasR1`, `hasR2`: Predicados sobre configuraciones
- `numConfigsWithR1`, `numConfigsWithR2`: Constantes de conteo

## Teoremas Principales

- `consecutive_reverse`: R1 es simétrico bajo inversión
- `r2_symmetric`: R2 es simétrico bajo intercambio
- `not_hasR1_iff`, `not_hasR2_iff`: Caracterizaciones
- `r1_local`, `r2_pairwise`: Propiedades de localidad

## Próximo Bloque

**Bloque 3: Matchings Perfectos**
- PerfectMatching (estructura)
- Los 4 matchings triviales
- Orientaciones
- Conexión con configuraciones

-/

end KnotTheory
