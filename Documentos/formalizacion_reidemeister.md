# Formalización de Movimientos de Reidemeister Racionales

**Fecha**: 2025-12-01

Este documento formaliza los **Movimientos de Reidemeister** adaptados a la teoría de Nudos Modulares Racionales. Estos movimientos generan la relación de equivalencia isotópica.

## 1. Definiciones Fundamentales

### 3.1. Adyacencia Modular
Dos posiciones en el espacio modular son adyacentes si están a distancia 1. Esto representa continuidad física en el diagrama.

```lean
/-- Dos posiciones p, q son adyacentes si p ⊕ 1 = q o q ⊕ 1 = p. -/
def is_adjacent {n : ℕ} (p q : ℝ[n]) : Prop :=
  p + 1 = q ∨ q + 1 = p
```

## 2. Definición de Movimientos

### 3.2. Movida R1 (Twist/Untwist)
Un cruce es eliminable (R1) si sus posiciones son adyacentes y está aislado (no entrelazado).

```lean
def is_R1_candidate {n : ℕ} (K : RationalConfiguration n) (i : Fin n) : Prop :=
  let c := K.crossings i
  is_adjacent c.over_pos c.under_pos ∧
  ∀ (j : Fin n), j ≠ i → ¬(are_interlaced c (K.crossings j))
```

### 3.3. Movida R2 (Poke/Unpoke)
Dos cruces forman un par R2 si sus hebras son adyacentes paralelamente y se entrelazan entre sí.

```lean
def is_R2_candidate {n : ℕ} (K : RationalConfiguration n) (a b : Fin n) : Prop :=
  let ca := K.crossings a
  let cb := K.crossings b
  a ≠ b ∧
  is_adjacent ca.over_pos cb.over_pos ∧
  is_adjacent ca.under_pos cb.under_pos ∧
  are_interlaced ca cb
```

### 3.4. Movida R3 (Slide/Triangle)
La movida más compleja. Requiere tres cruces formando una estructura triangular específica.

```lean
/-- Verifica si una lista de posiciones sigue un orden cíclico -/
def is_cyclic_order {n : ℕ} (_l : List (ℝ[n])) : Prop :=
  ∃ k, List.Sorted (fun a b => a.val < b.val) (_l.rotate k)

def is_R3_candidate {n : ℕ} (K : RationalConfiguration n) (i j k : Fin n) : Prop :=
  let ci := K.crossings i
  let cj := K.crossings j
  let ck := K.crossings k
  i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
  -- 1. Seis posiciones distintas (no comparten vértices)
  List.Nodup [ci.over_pos, cj.over_pos, ck.over_pos, ci.under_pos, cj.under_pos, ck.under_pos] ∧
  -- 2. Grafo de interlazado (dos pares se cruzan, uno no)
  ((ci ⋈ cj ∧ cj ⋈ ck ∧ ¬(ci ⋈ ck)) ∨
   (ci ⋈ cj ∧ ci ⋈ ck ∧ ¬(cj ⋈ ck)) ∨
   (ci ⋈ ck ∧ cj ⋈ ck ∧ ¬(ci ⋈ cj))) ∧
  -- 3. Patrón cíclico preservado
  is_cyclic_order [ci.over_pos, cj.over_pos, ck.over_pos, ci.under_pos, cj.under_pos, ck.under_pos]
```

## 3. Equivalencia Isotópica

Definimos la isotopía como la clausura reflexiva, simétrica y transitiva generada por estos movimientos y las rotaciones.

```lean
/-- Wrapper para configuraciones de cualquier tamaño -/
structure GeneralConfiguration where
  n : ℕ
  config : RationalConfiguration n

/-- Predicados de Transición (Placeholders) -/
-- Definen la relación funcional entre la configuración antes y después de la movida
def is_R1_transition {n : ℕ} (_K : RationalConfiguration n) (_K' : RationalConfiguration (n-1)) (_i : Fin n) : Prop := True
def is_R2_transition {n : ℕ} (_K : RationalConfiguration n) (_K' : RationalConfiguration (n-2)) (_a _b : Fin n) : Prop := True
def is_R3_transition {n : ℕ} (_K _K' : RationalConfiguration n) (_i _j _k : Fin n) : Prop := True

/-- Relación de equivalencia isotópica -/
inductive Isotopic : GeneralConfiguration → GeneralConfiguration → Prop where
  | refl (K) : Isotopic K K
  | symm {K K'} : Isotopic K K' → Isotopic K' K
  | trans {K K' K''} : Isotopic K K' → Isotopic K' K'' → Isotopic K K''

  -- Rotaciones (Preservan n)
  | rotation {n} (K : RationalConfiguration n) (k : ℝ[n]) :
      Isotopic ⟨n, K⟩ ⟨n, rotate_knot k K⟩

  -- R1: Reduce n en 1
  | R1_reduction {n} (K : RationalConfiguration n) (K' : RationalConfiguration (n-1)) (i : Fin n) :
      is_R1_candidate K i → is_R1_transition K K' i → Isotopic ⟨n, K⟩ ⟨n-1, K'⟩

  -- R2: Reduce n en 2
  | R2_reduction {n} (K : RationalConfiguration n) (K' : RationalConfiguration (n-2)) (a b : Fin n) :
      is_R2_candidate K a b → is_R2_transition K K' a b → Isotopic ⟨n, K⟩ ⟨n-2, K'⟩

  -- R3: Preserva n
  | R3_move {n} (K K' : RationalConfiguration n) (i j k : Fin n) :
      is_R3_candidate K i j k → is_R3_transition K K' i j k → Isotopic ⟨n, K⟩ ⟨n, K'⟩

/-- Notación -/
infix:50 " ∼ " => Isotopic
```

## 4. Análisis y Siguientes Pasos

1.  **Implementación de Transiciones**: Los predicados `is_RX_transition` son actualmente `True`. El siguiente paso crítico es definir constructivamente cómo cambia la configuración (renumeración de índices, ajuste de módulo).
2.  **Validación de R3**: La condición `is_cyclic_order` es elegante, pero verificar que captura exactamente la geometría del movimiento R3 requerirá pruebas con ejemplos concretos.
3.  **Conexión con IME**: Una vez definidos estos movimientos, se puede proceder a intentar demostrar `IME_reidemeister_invariant`.
