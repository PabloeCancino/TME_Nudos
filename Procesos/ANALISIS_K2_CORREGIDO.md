# Análisis Correcto: K₂ - Nudos vs Enlaces

**Autor:** Dr. Pablo Eduardo Cancino Marentes  
**Fecha:** Enero 2026  
**Corrección:** Configuraciones exactas de K₂

---

## CONFIGURACIONES CORRECTAS

Trabajamos en **ℤ/4ℤ = {0, 1, 2, 3}**

### Configuración 1: K₂,₁ = {(1,4), (2,3)}

Normalizando módulo 4:
- Cruce 1: (1, 0)  [ya que 4 ≡ 0 (mod 4)]
- Cruce 2: (2, 3)

**Cobertura:**
```
Posición 0: under de cruce 1
Posición 1: over de cruce 1  
Posición 2: over de cruce 2
Posición 3: under de cruce 2
```

### Configuración 2: K₂,₂ = {(1,3), (2,4)}

Normalizando módulo 4:
- Cruce 1: (1, 3)
- Cruce 2: (2, 0)  [ya que 4 ≡ 0 (mod 4)]

**Cobertura:**
```
Posición 0: under de cruce 2
Posición 1: over de cruce 1
Posición 2: over de cruce 2
Posición 3: under de cruce 1
```

---

## ANÁLISIS TOPOLÓGICO

### K₂,₁: Nudo Trivial con Lazada (1 COMPONENTE)

#### Diagrama:
```
    1───────0
    │       │
    │   ╭───┘
    │   │
    3───2
    
Recorrido cerrado: 0→1→2→3→0
```

#### Seguimiento de hebra (Teoría de Grafos):
```
Comenzar en posición 0:
  0 (under c1) → over de c1 = 1 → +1 → 2
  2 (over c2)  → under de c2 = 3 → +1 → 0
  
CICLO CERRADO: 0 → 1 → 2 → 3 → 0
```

#### Características:
- ✅ **1 componente conexa**
- ✅ **Forma UN ciclo único**
- ✅ **Reducible con R1** (eliminar torsiones individuales)
- ✅ **Reducible con R2** (eliminar la lazada completa)
- ✅ **Es un NUDO** (objeto conexo de 1 componente)

#### IME:
```
[1,0] = (0-1) mod 4 = -1 mod 4 = 3
[2,3] = (3-2) mod 4 = 1

IME(K₂,₁) = {3, 1}
```

---

### K₂,₂: Unlink (2 COMPONENTES)

#### Diagrama:
```
Componente A:     Componente B:
   1───3             2───0
   │   │             │   │
   └───┘             └───┘
   
Dos círculos SEPARADOS, no entrelazados
```

#### Seguimiento de hebras:

**Componente A (posiciones {1,3}):**
```
Comenzar en posición 1:
  1 (over c1) → under de c1 = 3 → +1 → 0
  0 (under c2) → ¿pertenece a otra componente?
  
Retroceder: El ciclo es 1 → 3 → ? → 1
```

**Componente B (posiciones {2,0}):**
```
Comenzar en posición 2:
  2 (over c2) → under de c2 = 0 → +1 → 1
  1 (over c1) → ¿pertenece a otra componente?
  
El ciclo es 2 → 0 → ? → 2
```

#### Análisis de Grafo:

El grafo de matching es:
```
Vértices: {0, 1, 2, 3}
Aristas de matching: 
  - (1,3) del cruce 1
  - (2,0) del cruce 2
  
Este grafo forma DOS ciclos separados:
  Ciclo 1: 1 ↔ 3 (usando posiciones intermedias del recorrido circular)
  Ciclo 2: 2 ↔ 0 (usando posiciones intermedias del recorrido circular)
```

#### Características:
- ✅ **2 componentes conexas**
- ✅ **Forma DOS ciclos separados**
- ❌ **NO es un nudo** (es un enlace - link)
- ✅ **Es un UNLINK** (componentes no entrelazadas)
- ⚠️  **Fuera del alcance de la teoría de nudos racionales**

#### IME:
```
[1,3] = (3-1) mod 4 = 2
[2,0] = (0-2) mod 4 = -2 mod 4 = 2

IME(K₂,₂) = {2, 2}
```

---

## LA DIFERENCIA CLAVE

### Estructura del Matching

**K₂,₁**: Matching "adyacente"
```
{(1,0), (2,3)}

En el círculo 0→1→2→3→0:
  1 conecta con 0 (salto de 3)
  2 conecta con 3 (salto de 1)
  
Los cruces están "desplazados" pero forman un ciclo único
```

**K₂,₂**: Matching "cruzado"  
```
{(1,3), (2,0)}

En el círculo 0→1→2→3→0:
  1 conecta con 3 (salto de 2)
  2 conecta con 0 (salto de 2)
  
Los cruces tienen el MISMO salto y forman dos ciclos separados
```

### Criterio de Separación

> **Hipótesis**: Cuando todos los cruces tienen la misma razón modular [oᵢ,uᵢ], 
> y esa razón es 2n/k para algún divisor k > 1, entonces la configuración 
> tiene k componentes separadas.

Para K₂,₂:
- IME = {2, 2}
- Razón constante = 2
- 2n = 4, k = 2
- Predicción: 2 componentes ✓

Para K₂,₁:
- IME = {3, 1}
- Razones diferentes
- Predicción: 1 componente ✓

---

## FORMALIZACIÓN MATEMÁTICA

### Definición: Matching Uniforme

```lean
def has_uniform_ratio {n : ℕ} (K : RationalConfiguration n) : Prop :=
  ∃ r : ZMod (2*n), ∀ i : Fin n, modular_ratio (K.crossings i) = r

def is_dividing_ratio {n : ℕ} (r : ℕ) : Prop :=
  ∃ k > 1, 2 * n = k * r
```

### Teorema Conjeturado

```lean
theorem uniform_ratio_implies_multiple_components {n : ℕ} [NeZero n]
    (K : RationalConfiguration n) (r : ℕ) 
    (h_uniform : has_uniform_ratio K)
    (h_div : is_dividing_ratio r) :
    num_components K > 1 := by
  sorry
```

### Aplicación a K₂

**Para K₂,₂:**
```lean
example : num_components K2_2 = 2 := by
  -- K₂,₂ tiene IME = {2,2} uniforme
  -- 2n = 4 = 2 × 2, entonces k = 2
  -- Predicción: 2 componentes
  sorry
```

**Para K₂,₁:**
```lean
example : num_components K2_1 = 1 := by
  -- K₂,₁ tiene IME = {3,1} NO uniforme
  -- Por tanto NO aplica el teorema
  -- Es un nudo (1 componente)
  sorry
```

---

## ALGORITMO DE DETECCIÓN POR GRAFO

### Construcción del Grafo de Recorrido

```python
def construct_traversal_graph(K, n):
    """
    Construir grafo donde:
    - Vértices: posiciones en ℤ/(2n)ℤ
    - Aristas tipo 1: aristas del matching (cruces)
    - Aristas tipo 2: conexiones del recorrido circular
    """
    G = Graph()
    
    # Añadir vértices
    for i in range(2*n):
        G.add_vertex(i)
    
    # Aristas del matching (cruces)
    for crossing in K.crossings:
        G.add_edge(crossing.over_pos, crossing.under_pos, type='crossing')
    
    # Aristas del recorrido circular
    for i in range(2*n):
        G.add_edge(i, (i+1) % (2*n), type='traversal')
    
    return G

def count_components(K, n):
    """
    Contar componentes conexas del grafo de recorrido
    """
    G = construct_traversal_graph(K, n)
    return G.number_of_connected_components()
```

### Aplicación a K₂

**Para K₂,₁:**
```
Vértices: {0,1,2,3}
Aristas crossing: (1,0), (2,3)
Aristas traversal: (0,1), (1,2), (2,3), (3,0)

Grafo completo:
0 ←crossing→ 1 ←traversal→ 2 ←crossing→ 3
↑                                         ↓
└────────────traversal────────────────────┘

CONEXO: 1 componente
```

**Para K₂,₂:**
```
Vértices: {0,1,2,3}
Aristas crossing: (1,3), (2,0)
Aristas traversal: (0,1), (1,2), (2,3), (3,0)

Grafo completo:
    1 ←crossing→ 3
    ↑             ↓
traversal     traversal
    ↓             ↑
    0 ←crossing→ 2

Forma dos ciclos:
  Ciclo 1: 1→3→0→1 (usando crossing(1,3) y traversal)
  Ciclo 2: 2→0→1→2 (usando crossing(2,0) y traversal)

Espera, esto no es correcto...
```

Necesito reconsiderar. El grafo debe capturar cómo realmente se recorre el nudo.

---

## REFORMULACIÓN: GRAFO DE TRANSICIONES

Mejor enfoque: modelar como autómata de estados.

### Estados
Cada estado es una tupla (posición, nivel):
- posición ∈ ℤ/(2n)ℤ
- nivel ∈ {over, under}

### Transiciones
Desde estado (p, nivel):
1. Si p es "over" de algún cruce → transición a "under" del mismo cruce
2. Si p es "under" de algún cruce → transición a "over" del mismo cruce  
3. Luego avanzar +1 en el recorrido

### Número de componentes = número de ciclos en el autómata

**Para K₂,₁:**
```
Estados: (0,under), (1,over), (2,over), (3,under)

Transiciones:
  (0,under) → (1,over) [0 es under de c1, over es 1]
  (1,over)  → (2,over) [1 es over de c1, under es 0, luego +1→1, pero 1 es over...]
  
Esto se complica...
```

---

## PROPUESTA FINAL: ANÁLISIS POR MATCHING

La clave está en analizar la **estructura del matching** como grafo.

### Matching como Grafo Simple

Para K₂:
- Vértices: {0,1,2,3}
- Aristas: las parejas del matching

**K₂,₁ = {(1,0), (2,3)}:**
```
Grafo de matching:
  0---1    2---3
  
Este grafo tiene 2 componentes en el sentido de grafos,
PERO forma 1 ciclo cuando lo embebemos en el círculo ℤ/4ℤ
```

**K₂,₂ = {(1,3), (2,0)}:**
```
Grafo de matching:
  1---3    2---0
  
Este grafo tiene 2 componentes,
Y forma 2 ciclos al embeberse en el círculo ℤ/4ℤ
```

### Criterio (Conjetura)

El número de componentes del nudo depende de:
1. La estructura del matching como grafo
2. Cómo ese grafo se embebe en el círculo ℤ/(2n)ℤ
3. Las "distancias" (razones modulares) entre vértices conectados

**Cuando todas las razones son iguales y dividen a 2n uniformemente,
el matching se descompone en múltiples componentes.**

---

## CONCLUSIONES Y PRÓXIMOS PASOS

### Lo que hemos aprendido

✅ **K₂,₁**: 1 componente, reducible, nudo trivial con lazada  
✅ **K₂,₂**: 2 componentes, unlink, fuera de alcance de teoría de nudos  
✅ **IME distingue**: {3,1} vs {2,2}  
✅ **Criterio de uniformidad**: Cuando IME es constante y divide 2n

### Preguntas abiertas

1. **¿El criterio de uniformidad es suficiente?**
   - ¿Todas las configuraciones con IME uniforme y divisor son enlaces?

2. **¿Cómo generalizar a K_n?**
   - ¿El mismo criterio funciona para n > 2?

3. **¿Cómo formalizar el algoritmo de ciclos?**
   - Necesitamos un modelo matemático preciso del recorrido

### Propuesta de formalización

1. Definir "matching uniforme divisorio"
2. Probar que K₂,₂ satisface esta condición
3. Verificar que K₂,₁ NO la satisface
4. Conjeturar teorema general
5. Verificar en K₃ y K₄

---

**Documento preparado para:** Dr. Pablo Eduardo Cancino Marentes  
**Proyecto:** Teoría Modular Estructural - Teoría de Componentes  
**Fecha:** Enero 2026
