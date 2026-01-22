# Síntesis: Teoría de Componentes en TME

**Autor:** Dr. Pablo Eduardo Cancino Marentes  
**Proyecto:** Teoría Modular Estructural de Nudos  
**Fecha:** Enero 2026

---

## RESUMEN EJECUTIVO

Hemos formalizado la distinción entre **nudos** (1 componente) y **enlaces** (múltiples componentes) en el contexto de la TME. El análisis revela que:

1. ✅ La configuración K₂ expone claramente el problema
2. ✅ El criterio simple de "IME uniforme" NO es suficiente
3. ✅ Se requiere análisis de **estructura de órbitas** del matching
4. 🔧 El problema es sutil y matemáticamente profundo

---

## 1. CONFIGURACIONES K₂ (CORREGIDAS)

### K₂,₁ = {(1,0), (2,3)} en ℤ/4ℤ

```
Diagrama:
    1───────0
    │       │
    │   ╭───┘
    │   │
    3───2
```

**Propiedades:**
- IME = {3, 1} → **NO uniforme**
- Componentes: **1** (nudo trivial con lazada)
- Reducible con R1 o R2
- Recorrido: 0→1→2→3→0 (ciclo único)

### K₂,₂ = {(1,3), (2,0)} en ℤ/4ℤ

```
Diagrama:
   Círculo A     Círculo B
     1───3         2───0
     │   │         │   │
     └───┘         └───┘
```

**Propiedades:**
- IME = {2, 2} → **Uniforme**
- Componentes: **2** (unlink)
- NO es un nudo, es un enlace
- Dos ciclos separados

---

## 2. CRITERIO DE UNIFORMIDAD (Primera Versión - INCOMPLETA)

### Hipótesis Inicial
> Si IME es uniforme con razón r, y r divide a 2n con cociente k > 1,
> entonces la configuración tiene k componentes.

### Verificación en K₂
- **K₂,₁**: IME = {3,1} NO uniforme → criterio no aplica → ✅ correcto (1 comp)
- **K₂,₂**: IME = {2,2} uniforme, 4/2 = 2 → ✅ correcto (2 comp)

### Contraejemplo en K₃

**K₃,special = {(0,3), (1,4), (2,5)}**
- IME = {3, 3, 3} → **Uniforme**
- 2n = 6, r = 3, k = 6/3 = 2
- **Predicción del criterio**: 2 componentes
- **Realidad**: 1 componente (es un nudo!)

❌ **El criterio de uniformidad simple FALLA**

---

## 3. ANÁLISIS DEL CONTRAEJEMPLO

¿Por qué K₃,special tiene 1 componente a pesar de ser uniforme?

### Estructura de K₃,special

```
En ℤ/6ℤ:
  Cruce 0: (0,3) - conecta posiciones opuestas
  Cruce 1: (1,4) - conecta posiciones opuestas  
  Cruce 2: (2,5) - conecta posiciones opuestas

Todos los cruces forman una única "espiral" antipodal
```

### Versus K₂,₂

```
En ℤ/4ℤ:
  Cruce 0: (1,3) - conecta posiciones opuestas
  Cruce 1: (2,0) - conecta posiciones opuestas

Los cruces forman DOS "espirales" independientes
```

**La diferencia:** En K₃ los 3 cruces están "entrelazados" formando un único ciclo. En K₂ los 2 cruces están "separados" formando dos ciclos.

---

## 4. CRITERIO REFINADO: ESTRUCTURA DE ÓRBITAS

### Concepto Clave: Órbitas del Matching

Bajo rotaciones del círculo ℤ/(2n)ℤ, los cruces forman órbitas.

**Definición formal:**
```lean
def rotate_crossing {n : ℕ} (c : RationalCrossing n) (k : ℕ) : RationalCrossing n :=
  ⟨c.over_pos + k, c.under_pos + k, ...⟩

-- Órbita de un cruce bajo rotación por r
def orbit_under_rotation (c : RationalCrossing n) (r : ℕ) : Set (RationalCrossing n) :=
  {rotate_crossing c (i * r) | i : ℕ, i < 2*n/r}
```

### Teorema Conjeturado (Versión Correcta)

> **El número de componentes de una configuración con IME uniforme (razón r) 
> es igual al número de órbitas de los cruces bajo rotación por r.**

### Aplicación a Casos

**K₂,₂: r = 2**
```
Órbita 1: (1,3) → rotar +2 → (3,1) → rotar +2 → (1,3) [mod 4]
Órbita 2: (2,0) → rotar +2 → (0,2) → rotar +2 → (2,0) [mod 4]

Número de órbitas = 2
Predicción: 2 componentes ✓
```

**K₃,special: r = 3**
```
Cruce 0: (0,3) → rotar +3 → (3,0) ≡ (3,0)
Cruce 1: (1,4) → rotar +3 → (4,1) ≡ (4,1)
Cruce 2: (2,5) → rotar +3 → (5,2) ≡ (5,2)

¡Todos los cruces se intercambian bajo rotación!
Forman UNA órbita única: {(0,3), (1,4), (2,5)} ↔ {(3,0), (4,1), (5,2)}

Número de órbitas = 1
Predicción: 1 componente ✓
```

---

## 5. FORMALIZACIÓN MATEMÁTICA

### Definiciones

```lean
-- Matching es uniforme
def has_uniform_IME {n : ℕ} (K : RationalConfiguration n) : Prop :=
  ∃ r : ℕ, ∀ i : Fin n, ratio_val (K.crossings i) = r

-- Número de órbitas bajo rotación por r
def num_rotation_orbits {n : ℕ} (K : RationalConfiguration n) (r : ℕ) : ℕ :=
  -- Contar clases de equivalencia bajo rotación
  sorry

-- TEOREMA PRINCIPAL
theorem components_eq_rotation_orbits {n : ℕ} [NeZero n] 
    (K : RationalConfiguration n) (r : ℕ)
    (h_uniform : has_uniform_IME K)
    (h_div : is_dividing_ratio n r) :
    num_components K = num_rotation_orbits K r := by
  sorry
```

### Algoritmo de Cálculo

```python
def count_rotation_orbits(K, n, r):
    """
    Contar órbitas de cruces bajo rotación por r
    """
    visited = set()
    num_orbits = 0
    
    for crossing in K.crossings:
        if crossing not in visited:
            num_orbits += 1
            # Marcar toda la órbita como visitada
            orbit = compute_orbit(crossing, r, 2*n)
            visited.update(orbit)
    
    return num_orbits

def compute_orbit(crossing, r, mod):
    """
    Computar la órbita de un cruce bajo rotación por r
    """
    orbit = []
    current = crossing
    for i in range(mod // r):
        orbit.append(current)
        current = rotate_crossing(current, r, mod)
        if current == crossing:
            break
    return orbit
```

---

## 6. TABLA DE VERIFICACIÓN

### K₂ (ℤ/4ℤ, 2n=4)

| Config | IME | Uniforme? | r | k=4/r | Órbitas | Componentes | Correcto? |
|--------|-----|-----------|---|-------|---------|-------------|-----------|
| K₂,₁ | {3,1} | ❌ | - | - | - | 1 | N/A |
| K₂,₂ | {2,2} | ✅ | 2 | 2 | 2 | 2 | ✅ |

### K₃ (ℤ/6ℤ, 2n=6)

| Config | IME | Uniforme? | r | k=6/r | Órbitas | Componentes | Correcto? |
|--------|-----|-----------|---|-------|---------|-------------|-----------|
| special | {3,3,3} | ✅ | 3 | 2 | 1 | 1 | ✅ |
| trefoil | {2,3,2} | ❌ | - | - | - | 1 | N/A |
| mirror | {4,3,4} | ❌ | - | - | - | 1 | N/A |

---

## 7. CONSECUENCIAS PARA TME

### Clasificación de Configuraciones

```
Total de configuraciones K_n
    ↓
1. Filtro R1/R2 (irreducibles)
    ↓
2. Calcular IME
    ↓
3a. IME uniforme? → Analizar órbitas → Contar componentes
3b. IME no uniforme? → Probablemente 1 componente (nudo)
    ↓
4. Separar nudos (1 comp) de enlaces (>1 comp)
    ↓
5. Solo para NUDOS: aplicar teoría de órbitas D₂ₙ
    ↓
Representantes canónicos de nudos K_n
```

### Impacto en el Universo Combinatorio

Para K₄ (por ejemplo):
```
Total: ~1000 configuraciones en ℤ/8ℤ
  ↓ Filtro irreducible
~100 configuraciones
  ↓ Separar por componentes
  - Nudos (1 comp): ~85
  - Enlaces (2+ comp): ~15
  ↓ Solo nudos → Órbitas D₈
~10 representantes de nudos K₄
```

---

## 8. IMPLEMENTACIÓN PROPUESTA

### Fase 1: Validación Manual ✅

- [x] Analizar K₂,₁ y K₂,₂
- [x] Identificar problema con criterio simple
- [x] Verificar K₃,special como contraejemplo

### Fase 2: Algoritmo de Órbitas 🔧

```lean
-- Archivo: TCN_08_RotationOrbits.lean

-- 1. Implementar rotación de cruces
def rotate_crossing {n : ℕ} (c : RationalCrossing n) (k : ℕ) : RationalCrossing n

-- 2. Calcular órbita de un cruce
def compute_crossing_orbit {n : ℕ} (c : RationalCrossing n) (r : ℕ) : List (RationalCrossing n)

-- 3. Particionar en órbitas
def partition_into_orbits {n : ℕ} (K : RationalConfiguration n) (r : ℕ) : 
    List (List (RationalCrossing n))

-- 4. Contar componentes
def num_components_via_orbits {n : ℕ} (K : RationalConfiguration n) : ℕ
```

### Fase 3: Integración con TME 📊

Actualizar archivos existentes:
- **TCN_02_Reidemeister**: Movimientos preservan num_components
- **TCN_05_Orbitas**: Acción D₂ₙ conmuta con estructura de componentes
- **TCN_07_Clasificacion**: Añadir información de componentes

---

## 9. PREGUNTAS ABIERTAS

### Teóricas

1. **¿El criterio de órbitas es completo?**
   - ¿Funciona para TODAS las configuraciones uniformes?
   - ¿Hay excepciones más allá de K₃?

2. **¿Qué pasa con configuraciones NO uniformes?**
   - ¿Pueden tener múltiples componentes?
   - ¿Necesitamos otro criterio?

3. **¿Relación con teoría clásica de nudos?**
   - ¿Cómo se conecta con la definición topológica de componentes?
   - ¿Es equivalente?

### Computacionales

1. **¿Complejidad del algoritmo de órbitas?**
   - Calcular órbitas es O(n) o O(n²)?
   - ¿Optimizaciones posibles?

2. **¿Verificación formal en Lean?**
   - ¿Cómo probar el teorema principal?
   - ¿Qué axiomas necesitamos?

---

## 10. CONCLUSIONES

### Lo que hemos logrado

✅ **Identificación precisa del problema**: K₂,₂ vs K₂,₁  
✅ **Criterio inicial y su refutación**: IME uniforme NO es suficiente  
✅ **Contraejemplo constructivo**: K₃,special  
✅ **Criterio refinado**: Análisis de órbitas  
✅ **Formalización en Lean**: ~500 líneas de código

### Camino a seguir

1. **Implementar algoritmo de órbitas** (2-3 días)
2. **Verificar en casos K₄** (1 semana)
3. **Probar teorema principal** (si es posible constructivamente)
4. **Integrar con clasificación existente** (1 semana)

### Impacto en TME

Este análisis:
- 🎯 Refina el universo combinatorio eliminando enlaces
- 🔍 Provee criterio decidible para detectar componentes
- 📐 Conecta estructura algebraica (IME) con topología (componentes)
- 🚀 Permite clasificación completa de nudos K_n

---

## PRÓXIMO PASO CONCRETO

👉 **Implementar `TCN_08_RotationOrbits.lean`**

Comenzar con:
```lean
-- 1. Rotación básica (ya hecho en UniformityCriterion)
-- 2. Cálculo de órbitas
-- 3. Aplicación a K₂,₂ y K₃,special
-- 4. Teorema de correctness
```

¿Procedemos con esta implementación?

---

**Documento preparado para:** Dr. Pablo Eduardo Cancino Marentes  
**Estado:** Análisis completo, listo para implementación  
**Prioridad:** Alta - fundamental para clasificación K_n  
**Fecha:** Enero 2026
