# Extensión de Movimientos de Reidemeister a K_n

**Autor:** Dr. Pablo Eduardo Cancino Marentes  
**Fecha:** Diciembre 21, 2025  
**Objetivo:** Formalizar movimientos de Reidemeister para configuraciones K_n genéricas en Lean 4

---

## 1. ANÁLISIS DE FACTIBILIDAD

### 1.1. Estado Actual del Código

**Implementaciones existentes:**

1. **Reidemeister.lean (General pero incompleto)**
   - ✅ Define `KnotConfig (n : ℕ)` genérico
   - ✅ Estructura abstracta de movimientos R1, R2, R3
   - ❌ Implementaciones concretas con `sorry`
   - ❌ Usa axiomas en lugar de teoremas probados
   - 🎯 Enfoque: Teórico/abstracto

2. **TCN_02_Reidemeister.lean (K₃ completo)**
   - ✅ Implementación concreta para Z/6Z
   - ✅ Predicados decidibles `hasR1`, `hasR2`
   - ✅ Todos los teoremas probados (0 sorry)
   - ✅ Conteos verificados: 88 con R1, 104 con R2
   - 🎯 Enfoque: Concreto/constructivo

### 1.2. Desafíos de la Generalización

**Desafío 1: Parametrización del anillo modular**
```lean
K₃: Z/6Z   (ring fijo)
K₄: Z/8Z   (ring fijo)
K_n: Z/(2n)Z  (ring parametrizado por n)
```

**Desafío 2: Grupos diédricos variables**
```lean
K₃: D₆   (orden 12)
K₄: D₈   (orden 16)  
K_n: D₂ₙ  (orden 4n)
```

**Desafío 3: Definiciones dependientes de n**
```lean
-- K₃ específico
def isConsecutive (p : OrderedPair) : Prop :=
  p.snd = p.fst + 1 ∨ p.snd = p.fst - 1

-- K_n general (requiere parametrización)
def isConsecutive (n : ℕ) (p : OrderedPair n) : Prop :=
  p.snd = p.fst + 1 ∨ p.snd = p.fst - 1
```

---

## 2. ESTRATEGIA DE GENERALIZACIÓN

### 2.1. Fase 1: Fundamentos Parametrizados (CRÍTICO)

**Objetivo:** Crear estructuras base parametrizadas por n

```lean
-- Estructura de par ordenado parametrizada
structure OrderedPair (n : ℕ) where
  fst : ZMod (2*n)
  snd : ZMod (2*n)
  distinct : fst ≠ snd

-- Configuración K_n genérica
structure KnConfig (n : ℕ) where
  pairs : Finset (OrderedPair n)
  card_eq : pairs.card = n
  coverage : ∀ i : ZMod (2*n), ∃ p ∈ pairs, p.fst = i ∨ p.snd = i
```

**Implementación:**
- Archivo: `KN_00_Fundamentos_General.lean`
- Depende de: `Mathlib.Data.ZMod.Basic`
- Estado: Por crear

---

### 2.2. Fase 2: Movimientos Reidemeister Generales

#### 2.2.1. Movimiento R1 (Consecutivos)

**Definición parametrizada:**

```lean
namespace Reidemeister

/-- Un par es consecutivo en Z/(2n)Z si sus componentes difieren en ±1 -/
def isConsecutive (n : ℕ) (p : OrderedPair n) : Prop :=
  p.snd = p.fst + 1 ∨ p.snd = p.fst - 1

/-- Una configuración K_n tiene movimiento R1 -/
def hasR1 {n : ℕ} (K : KnConfig n) : Prop :=
  ∃ p ∈ K.pairs, isConsecutive n p

/-- Decidibilidad de R1 (crítico para computación) -/
instance decidableR1 (n : ℕ) [NeZero n] (K : KnConfig n) : 
    Decidable (hasR1 K) := by
  unfold hasR1
  infer_instance

end Reidemeister
```

**Propiedades clave a probar:**

```lean
/-- R1 se preserva bajo rotaciones -/
theorem r1_rotation_invariant {n : ℕ} (K : KnConfig n) (p : OrderedPair n) :
    isConsecutive n p → 
    isConsecutive n (rotate_pair n p) := by
  sorry

/-- Conteo de pares consecutivos en Z/(2n)Z -/
theorem count_consecutive_pairs (n : ℕ) [NeZero n] :
    (Finset.filter (isConsecutive n) (all_pairs n)).card = 2*n := by
  sorry
```

#### 2.2.2. Movimiento R2 (Pares Paralelos)

**Definición parametrizada:**

```lean
/-- Dos pares forman patrón R2 si son adyacentes en ambas componentes -/
def formsR2Pattern (n : ℕ) (p q : OrderedPair n) : Prop :=
  (q.fst = p.fst + 1 ∧ q.snd = p.snd + 1) ∨  -- Paralelo +
  (q.fst = p.fst - 1 ∧ q.snd = p.snd - 1) ∨  -- Paralelo -
  (q.fst = p.fst + 1 ∧ q.snd = p.snd - 1) ∨  -- Antiparalelo +
  (q.fst = p.fst - 1 ∧ q.snd = p.snd + 1)    -- Antiparalelo -

/-- Una configuración tiene movimiento R2 -/
def hasR2 {n : ℕ} (K : KnConfig n) : Prop :=
  ∃ p ∈ K.pairs, ∃ q ∈ K.pairs, p ≠ q ∧ formsR2Pattern n p q

instance decidableR2 (n : ℕ) [NeZero n] (K : KnConfig n) : 
    Decidable (hasR2 K) := by
  unfold hasR2
  infer_instance
```

**Propiedades clave:**

```lean
/-- R2 es simétrico -/
theorem r2_symmetric {n : ℕ} (p q : OrderedPair n) :
    formsR2Pattern n p q → formsR2Pattern n q p := by
  sorry

/-- Conteo de pares R2 en Z/(2n)Z -/
theorem count_r2_pairs (n : ℕ) [NeZero n] :
    (Finset.filter (uncurry (formsR2Pattern n)) (all_pair_pairs n)).card = 8*n := by
  sorry
```

---

## 3. COMPARACIÓN: K₃ vs K_n

### 3.1. Tabla Comparativa

| Aspecto | K₃ (Concreto) | K_n (General) |
|---------|---------------|---------------|
| **Anillo** | `ZMod 6` | `ZMod (2*n)` |
| **Grupo** | `D₆` | `D₂ₙ` |
| **Par ordenado** | `OrderedPair` (fijo) | `OrderedPair n` (parametrizado) |
| **Consecutivo** | `p.snd = p.fst ± 1` en Z/6Z | `p.snd = p.fst ± 1` en Z/(2n)Z |
| **R2 pattern** | 4 casos en Z/6Z | 4 casos en Z/(2n)Z |
| **Decidibilidad** | `instance` directo | `instance` con `[NeZero n]` |
| **Complejidad pruebas** | Simple (`decide`) | Requiere inducción/casos |

### 3.2. Similitudes (Lo que se preserva)

✅ **Estructura lógica idéntica:**
- R1: `∃ p, isConsecutive p`
- R2: `∃ p q, p ≠ q ∧ formsR2Pattern p q`

✅ **Propiedades algebraicas:**
- Simetría de R2
- Inversión de consecutivos
- Localidad de movimientos

✅ **Decidibilidad:**
- Todos los predicados siguen siendo decidibles
- Finitud de configuraciones garantiza computabilidad

### 3.3. Diferencias (Lo que cambia)

❌ **Tipo de datos:**
```lean
-- K₃
OrderedPair = { fst snd : ZMod 6 // fst ≠ snd }

-- K_n
OrderedPair (n : ℕ) = { fst snd : ZMod (2*n) // fst ≠ snd }
```

❌ **Cardinalidades:**
```lean
-- K₃
|Z/6Z| = 6
|Pares| = 6 × 5 = 30
|Configs| = 6!/(3!) = 120

-- K_n
|Z/(2n)Z| = 2n
|Pares| = 2n × (2n-1)
|Configs| = (2n)! / n!
```

❌ **Complejidad de pruebas:**
```lean
-- K₃: decide funciona directamente
example : isConsecutive (OrderedPair.make 0 1 _) := by decide

-- K_n: requiere razonamiento sobre n
theorem consecutive_plus_one {n : ℕ} (i : ZMod (2*n)) :
    isConsecutive n ⟨i, i+1, by omega⟩ := by
  left; rfl
```

---

## 4. PLAN DE IMPLEMENTACIÓN

### 4.1. Arquitectura de Archivos

```
KN_General/
├── KN_00_Fundamentos_General.lean
│   ├── OrderedPair (n : ℕ)
│   ├── KnConfig (n : ℕ)
│   ├── Axiomas básicos
│   └── Propiedades de ZMod (2*n)
│
├── KN_01_Reidemeister_General.lean
│   ├── isConsecutive (n : ℕ)
│   ├── formsR2Pattern (n : ℕ)
│   ├── hasR1, hasR2
│   └── Propiedades de simetría
│
├── KN_02_Grupo_Dihedral_General.lean
│   ├── Acción de D₂ₙ en KnConfig n
│   ├── rotate_config (n : ℕ)
│   ├── reflect_config (n : ℕ)
│   └── Teorema órbita-estabilizador
│
├── KN_03_Invariantes_General.lean
│   ├── IME parametrizado
│   ├── Gaps parametrizado
│   └── Signs parametrizado
│
└── KN_04_Instancias/
    ├── K3_Instance.lean  (n=3, recupera TCN_02)
    ├── K4_Instance.lean  (n=4, nuevo)
    └── K5_Instance.lean  (n=5, ejemplo)
```

### 4.2. Fases de Desarrollo

#### **FASE 1: Fundamentos (Semanas 1-2)**

**Archivo:** `KN_00_Fundamentos_General.lean`

**Tareas:**
1. ✅ Definir `OrderedPair (n : ℕ)` con `ZMod (2*n)`
2. ✅ Definir `KnConfig (n : ℕ)` con axiomas parametrizados
3. ✅ Probar propiedades básicas de `ZMod (2*n)`
4. ✅ Establecer decidibilidad de igualdad

**Entregables:**
- Estructura `OrderedPair n` funcional
- Estructura `KnConfig n` con axiomas verificados
- Lemmas básicos de aritmética modular

#### **FASE 2: Reidemeister General (Semanas 3-4)**

**Archivo:** `KN_01_Reidemeister_General.lean`

**Tareas:**
1. ✅ Implementar `isConsecutive n`
2. ✅ Implementar `formsR2Pattern n`
3. ✅ Probar decidibilidad de `hasR1`, `hasR2`
4. ✅ Probar propiedades de simetría
5. ✅ Contar configuraciones con R1/R2 (fórmulas generales)

**Teoremas críticos:**
```lean
theorem consecutive_characterization {n : ℕ} [NeZero n] (p : OrderedPair n) :
    isConsecutive n p ↔ 
    (p.snd : ℤ) - (p.fst : ℤ) ≡ ±1 [ZMOD (2*n)] := by
  sorry

theorem r2_count_formula {n : ℕ} [NeZero n] :
    countR2Pairs n = 8*n := by
  sorry
```

#### **FASE 3: Acción de Grupo (Semanas 5-6)**

**Archivo:** `KN_02_Grupo_Dihedral_General.lean`

**Tareas:**
1. ✅ Definir acción de D₂ₙ en `ZMod (2*n)`
2. ✅ Implementar rotación y reflexión parametrizadas
3. ✅ Probar que es acción de grupo
4. ✅ Teorema órbita-estabilizador para K_n

**Estructura clave:**
```lean
/-- Acción del grupo diédrico D₂ₙ -/
def dihedral_action (n : ℕ) : D₂ₙ →* (ZMod (2*n) ≃ ZMod (2*n)) := sorry

/-- Rotación de configuración -/
def rotate_config {n : ℕ} (K : KnConfig n) (k : ZMod (2*n)) : KnConfig n := sorry

/-- Teorema órbita-estabilizador general -/
theorem orbit_stabilizer_formula {n : ℕ} [NeZero n] (K : KnConfig n) :
    (orbit K).card * (stabilizer K).card = 4*n := by
  sorry
```

#### **FASE 4: Instancias Concretas (Semanas 7-8)**

**Archivos:** `K3_Instance.lean`, `K4_Instance.lean`

**Tareas:**
1. ✅ Mostrar que K₃ específico es caso particular (n=3)
2. ✅ Implementar K₄ como instancia (n=4)
3. ✅ Verificar que teoremas generales se especializan correctamente
4. ✅ Probar equivalencia con versiones anteriores

**Ejemplo de instancia:**
```lean
-- K₃ como caso especial
def K3_as_instance : KnConfig 3 := {
  pairs := -- mismas tuplas que TCN_01
  card_eq := by norm_num
  coverage := by -- mismo teorema
}

-- Verificar equivalencia
theorem k3_r1_agrees :
    hasR1 K3_as_instance ↔ TCN_02.hasR1 K3_old := by
  sorry
```

---

## 5. DESAFÍOS TÉCNICOS Y SOLUCIONES

### 5.1. Desafío: Dependencia de Tipos

**Problema:**
```lean
-- No compila: n no es el mismo en ambos lados
def bad_example (n m : ℕ) (p : OrderedPair n) : OrderedPair m := p
```

**Solución:**
Usar conversión explícita cuando `n = m`:
```lean
def convert_pair {n m : ℕ} (h : n = m) (p : OrderedPair n) : OrderedPair m :=
  h ▸ p
```

### 5.2. Desafío: Decidibilidad con Parámetros

**Problema:**
```lean
-- ¿Cómo hacer decidible algo que depende de n?
instance hasR1_decidable (n : ℕ) (K : KnConfig n) : Decidable (hasR1 K) := ?
```

**Solución:**
Usar `Classical.decEq` o requerir `[DecidableEq (ZMod (2*n))]`:
```lean
instance hasR1_decidable (n : ℕ) [NeZero n] [DecidableEq (ZMod (2*n))] 
    (K : KnConfig n) : Decidable (hasR1 K) := by
  unfold hasR1 isConsecutive
  infer_instance
```

### 5.3. Desafío: Cardinalidades Variables

**Problema:**
```lean
-- K₃ tiene 120 configs, K₄ tiene (8!)/(4!), K_n tiene (2n)!/n!
-- ¿Cómo probar fórmulas generales?
```

**Solución:**
Probar por inducción sobre n, o usar combinatoria de Mathlib:
```lean
theorem config_count (n : ℕ) [NeZero n] :
    (all_configs n).card = Nat.factorial (2*n) / Nat.factorial n := by
  -- Usar teoremas de permutaciones de Mathlib
  sorry
```

### 5.4. Desafío: Preservación de Propiedades

**Problema:**
¿Cómo garantizar que las propiedades de K₃ se preservan en K_n?

**Solución:**
Crear "test instances" que verifiquen automáticamente:
```lean
-- Verificación automática para n=3
example : (config_count 3 : ℚ) = 120 := by norm_num
example : (count_r1_configs 3 : ℚ) = 88 := by norm_num
```

---

## 6. VENTAJAS DE LA GENERALIZACIÓN

### 6.1. Científicas

✅ **Unificación teórica:**
- Un solo framework para todos los K_n
- Teoremas que cubren infinitos casos

✅ **Extensibilidad:**
- Fácil agregar K₅, K₆, ..., K_n
- Patrones generales visibles

✅ **Verificación formal:**
- Pruebas garantizan corrección para todo n
- Eliminan errores de casos especiales

### 6.2. Computacionales

✅ **Reutilización de código:**
- Algoritmos escritos una vez
- Aplicables a cualquier n

✅ **Optimización:**
- Complejidad explícita: O(n²) para R1, O(n⁴) para R2
- Posibilidad de paralelización

### 6.3. Pedagógicas

✅ **Claridad conceptual:**
- Separa lo esencial de lo accidental
- Muestra estructura común

✅ **Documentación:**
- Ejemplos concretos (K₃, K₄) + general (K_n)
- Escalera de abstracción

---

## 7. RIESGOS Y MITIGACIÓN

### 7.1. Riesgo: Complejidad Excesiva

**Señal de alarma:**
- Pruebas se vuelven muy largas
- Muchos casos especiales

**Mitigación:**
- Dividir teoremas en lemmas pequeños
- Usar automation (`omega`, `ring`, `decide`)
- Crear biblioteca de tácticas personalizadas

### 7.2. Riesgo: Pérdida de Decidibilidad

**Señal de alarma:**
- `decidable` requiere axiomas
- Computación no termina

**Mitigación:**
- Mantener todas las instancias `decidable`
- Usar `Classical` solo cuando sea inevitable
- Test computacionales para n pequeños

### 7.3. Riesgo: Incompatibilidad con K₃

**Señal de alarma:**
- Teoremas de K₃ no se recuperan
- Resultados numéricos difieren

**Mitigación:**
- Tests de equivalencia explícitos
- Verificar que `KnConfig 3 ≃ K3Config`
- Mantener ambas versiones temporalmente

---

## 8. CRONOGRAMA PROPUESTO

### Semanas 1-2: Fundamentos
- [ ] `OrderedPair (n : ℕ)`
- [ ] `KnConfig (n : ℕ)`
- [ ] Axiomas generales
- [ ] Propiedades de `ZMod (2*n)`

### Semanas 3-4: Reidemeister
- [ ] `isConsecutive n`, `formsR2Pattern n`
- [ ] `hasR1`, `hasR2` decidibles
- [ ] Conteos y fórmulas
- [ ] Propiedades de simetría

### Semanas 5-6: Grupo
- [ ] Acción de D₂ₙ
- [ ] Órbitas y estabilizadores
- [ ] Teorema órbita-estabilizador
- [ ] Representantes canónicos

### Semanas 7-8: Instancias
- [ ] K₃ como caso especial
- [ ] K₄ implementado
- [ ] Verificación cruzada
- [ ] Documentación

---

## 9. CONCLUSIONES

### 9.1. Factibilidad: **ALTA** ✅

**Razones:**
1. La estructura matemática es uniforme
2. Las definiciones se parametrizan naturalmente
3. Mathlib tiene todas las herramientas necesarias
4. K₃ funciona como prototipo validado

### 9.2. Dificultad: **MODERADA** ⚠️

**Aspectos fáciles:**
- Definiciones (mecánicas)
- Decidibilidad (automática)
- Propiedades locales (pattern matching)

**Aspectos difíciles:**
- Conteos generales (requiere combinatoria)
- Teorema órbita-estabilizador (teoría de grupos)
- Preservación de equivalencias (pruebas largas)

### 9.3. Valor: **MUY ALTO** 🎯

**Beneficios inmediatos:**
- Framework unificado K₃, K₄, K₅, ...
- Verificación formal de propiedades generales
- Base para clasificación completa

**Impacto a largo plazo:**
- Primera formalización completa de TME en Lean
- Contribución a MathComp/Mathlib
- Referencia para teoría de nudos constructiva

---

## 10. RECOMENDACIÓN FINAL

**PROCEDER CON LA GENERALIZACIÓN**, siguiendo el plan en fases.

**Estrategia recomendada:**
1. **Comenzar con `KN_00_Fundamentos_General.lean`**
2. **Iterar rápidamente en K₄** (caso concreto siguiente)
3. **Generalizar solo cuando el patrón sea claro**
4. **Mantener tests de regresión con K₃**

**Criterio de éxito:**
```lean
-- Si podemos escribir esto y compilar, hemos tenido éxito:
theorem reidemeister_works_for_all_n (n : ℕ) [NeZero n] (K : KnConfig n) :
    hasR1 K ∨ hasR2 K ∨ IsIrreducible K := by
  -- Clasificación completa
  sorry
```

---

**Próximo paso sugerido:** Crear `KN_00_Fundamentos_General.lean` con la estructura base parametrizada.

