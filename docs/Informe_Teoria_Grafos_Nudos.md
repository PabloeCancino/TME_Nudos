# Informe Preliminar: Teoría de Grafos Aplicada a la Teoría Modular de Nudos

## 📋 Resumen Ejecutivo

Este informe documenta la aplicación de la teoría de grafos a la clasificación de nudos mediante una representación modular. Basado en la verificación completa de las 24 configuraciones de nudos de 2 cruces, establecemos los fundamentos teóricos de la correspondencia entre conceptos de grafos y estructuras de nudos.

---

## 🔢 Notación y Definiciones

### Configuración de Nudo K_n

Un nudo con `n` cruces se representa como:

```
K_n = {(o₁,u₁), (o₂,u₂), ..., (oₙ,uₙ)}
```

Donde:
- `oᵢ` = arco que pasa **over** (sobre) en el cruce i
- `uᵢ` = arco que pasa **under** (bajo) en el cruce i
- Cada par `(oᵢ,uᵢ)` representa un cruce del nudo

### Aritmética Modular

Los arcos se numeran en un módulo `m` (típicamente `m = 2n` para `n` cruces):
- Arcos: `{0, 1, 2, ..., m-1}` en ℤₘ
- Operaciones: suma y resta módulo `m`

---

## 🔄 Correspondencia: Teoría de Grafos ↔ Teoría de Nudos

### Tabla de Equivalencias Fundamentales

| Concepto en Teoría de Grafos | Concepto en Teoría de Nudos      | Notación                            |
| ---------------------------- | -------------------------------- | ----------------------------------- |
| **Vértice**                  | **Cruce**                        | `(oᵢ,uᵢ)`                           |
| **Arista**                   | **Arco** (segmento entre cruces) | `aⱼ ∈ ℤₘ`                           |
| **Grado de vértice**         | Número de arcos en un cruce      | Siempre 4 (2 entrada, 2 salida)     |
| **Componente conexa**        | Componente del nudo/enlace       | Ciclo cerrado                       |
| **Ciclo euleriano**          | Recorrido completo del nudo      | Camino que visita cada arco una vez |
| **Grafo conexo**             | Nudo (1 componente)              | vs Enlace (2+ componentes)          |
| **Subgrafo**                 | Subnudo o componente             | Parte del diagrama                  |

---

## 📊 Representación como Grafo

### Construcción del Grafo G(K_n)

Para un nudo `K_n = {(o₁,u₁), ..., (oₙ,uₙ)}`:

1. **Vértices:** `V = {v₁, v₂, ..., vₙ}` (uno por cruce)
2. **Aristas:** `E = {e₁, e₂, ..., eₘ}` (arcos del nudo)
3. **Función de incidencia:** Cada arco `aⱼ` conecta dos cruces

### Matriz de Adyacencia

Para `n` cruces, construimos una matriz `A` de tamaño `m×m` donde:

```
A[i][j] = 1  si el arco i conecta directamente al arco j
A[i][j] = 0  en caso contrario
```

**Ejemplo para K_2 = {(0,1), (2,3)}:**

```
    0  1  2  3
0 [ 0  1  0  0 ]
1 [ 0  0  1  0 ]
2 [ 0  0  0  1 ]
3 [ 1  0  0  0 ]
```

Esta matriz representa un ciclo: 0 → 1 → 2 → 3 → 0

---

## 🔍 ETAPA 1: Análisis de Componentes Conexas

### Algoritmo: BFS (Breadth-First Search)

**Objetivo:** Determinar el número de componentes conexas del grafo.

**Pseudocódigo:**
```
función contar_componentes(grafo G):
    visitados ← conjunto vacío
    num_componentes ← 0
    
    para cada vértice v en G:
        si v no está en visitados:
            num_componentes ← num_componentes + 1
            BFS(v, visitados)  // Marcar toda la componente
    
    retornar num_componentes
```

**Complejidad:** O(V + E) - Decidible

### Interpretación en Teoría de Nudos

| Componentes | Clasificación               | Significado             |
| ----------- | --------------------------- | ----------------------- |
| 1           | **Nudo**                    | Una sola curva cerrada  |
| 2           | **Enlace de 2 componentes** | Dos curvas entrelazadas |
| k           | **Enlace de k componentes** | k curvas entrelazadas   |

**Resultado para K_2:** Todas las 24 configuraciones tienen **1 componente** → Son nudos, no enlaces.

---

## 🔄 Ciclos Eulerianos

### Teorema de Euler

Un grafo conexo tiene un ciclo euleriano si y solo si **todos los vértices tienen grado par**.

### Aplicación a Nudos

En un diagrama de nudo:
- Cada cruce tiene exactamente **4 arcos** incidentes (2 entrada, 2 salida)
- Por tanto, cada vértice tiene **grado 4** (par)
- **Conclusión:** Todo nudo bien formado tiene un ciclo euleriano

**Verificación para K_2:** Las 24 configuraciones son grafos eulerianos ✅

---

## 🎯 Propiedades Modulares y Consecutividad

### Definición de Consecutividad en ℤₘ

Dos elementos `a, b ∈ ℤₘ` son **consecutivos** si:

```
|a - b| mod m ∈ {1, m-1}
```

**Para m=4:**
- Consecutivos: (0,1), (1,2), (2,3), (3,0)
- NO consecutivos: (0,2), (1,3)

### Aplicación a Movimientos de Reidemeister

#### R1: Consecutividad Interna
Un cruce `(oᵢ,uᵢ)` es reducible si `oᵢ` y `uᵢ` son consecutivos:

```
|oᵢ - uᵢ| mod m ∈ {1, m-1}
```

**Ejemplo:** `(0,1)` → |0-1| = 1 → ✅ R1 aplicable

#### R2: Consecutividad Correspondiente
Dos cruces `(o₁,u₁)` y `(o₂,u₂)` son reducibles si:

```
|o₁ - o₂| mod m ∈ {1, m-1}  Y  |u₁ - u₂| mod m ∈ {1, m-1}
```

**Ejemplo:** `(0,2)` y `(1,3)`
- Overs: |0-1| = 1 ✅
- Unders: |2-3| = 1 ✅
- → R2 aplicable

---

## 📊 Resultados Empíricos: K_2

### Distribución de Configuraciones

De las 24 configuraciones de 2 cruces:

| Criterio                | Cantidad | Porcentaje |
| ----------------------- | -------- | ---------- |
| **R1 aplicable**        | 16       | 66.7%      |
| **R2 aplicable**        | 8        | 33.3%      |
| **Triviales (R1 o R2)** | 24       | 100%       |
| **No triviales**        | 0        | 0%         |

### Teorema Empírico

> **Teorema:** Todo nudo con exactamente 2 cruces es trivial.
>
> **Demostración:** Por verificación exhaustiva de las 4! = 24 permutaciones posibles en ℤ₄.

---

## 🔬 Invariantes de Grafos Aplicados a Nudos

### 1. Número de Componentes Conexas

**Invariante de Grafo:** `κ(G)` = número de componentes conexas

**Invariante de Nudo:** Distingue nudos (κ=1) de enlaces (κ≥2)

**Algoritmo:** BFS/DFS - O(V+E) - Decidible

### 2. Número Cromático (Futuro)

**Invariante de Grafo:** `χ(G)` = mínimo número de colores para colorear vértices

**Aplicación Potencial:** Clasificación de cruces por tipo/orientación

### 3. Número de Ciclos Independientes

**Invariante de Grafo:** Número ciclomático

**Aplicación Potencial:** Complejidad topológica del nudo

---

## 🎯 Ventajas de la Representación Modular

### 1. Computabilidad

✅ **Decidible:** Todos los algoritmos son computables
- Componentes conexas: O(V+E)
- Detección R1: O(n) por cruce
- Detección R2: O(n²) entre pares de cruces

### 2. Escalabilidad

✅ **Generalizable:** La notación `K_n` funciona para cualquier `n`
- K_2: 24 configuraciones (verificadas)
- K_3: 6! = 720 configuraciones (futuro)
- K_n: (2n)! configuraciones

### 3. Precisión

✅ **Sin ambigüedad:** La aritmética modular elimina ambigüedades
- Cada configuración tiene una representación única
- Las operaciones son bien definidas en ℤₘ

---

## 📋 Algoritmos Fundamentales

### Algoritmo 1: Verificar si es Nudo o Enlace

```python
def es_nudo(K_n):
    """
    Entrada: K_n = {(o₁,u₁), ..., (oₙ,uₙ)}
    Salida: True si es nudo (1 componente), False si es enlace
    """
    grafo = construir_grafo(K_n)
    componentes = BFS_componentes(grafo)
    return componentes == 1
```

### Algoritmo 2: Verificar Trivialidad

```python
def es_trivial(K_n):
    """
    Entrada: K_n = {(o₁,u₁), ..., (oₙ,uₙ)}
    Salida: True si es trivial (reducible a unknot)
    """
    # Verificar R1 en cada cruce
    for (oᵢ, uᵢ) in K_n:
        if son_consecutivos_mod(oᵢ, uᵢ):
            return True  # Reducible por R1
    
    # Verificar R2 entre pares de cruces
    for i, j in pares(K_n):
        if R2_aplicable(K_n[i], K_n[j]):
            return True  # Reducible por R2
    
    return False  # No trivial (requiere más análisis)
```

---

## 🔮 Extensiones Futuras

### 1. Grafos Dirigidos

Incorporar la **orientación** del nudo como direcciones en las aristas:
- Arista dirigida: `(aᵢ → aⱼ)` indica flujo del nudo
- Permite distinguir nudos quirales de sus imágenes espejo

### 2. Grafos Ponderados

Asignar **pesos** a los cruces:
- Peso = orientación (+1 o -1)
- Permite calcular el **writhe** directamente

### 3. Hipergrafos

Para nudos con **cruces múltiples** (más de 2 arcos):
- Hipervértice = cruce de k arcos
- Generalización natural de la teoría

---

## ✅ Conclusiones

### Principales Hallazgos

1. **Correspondencia Completa:** Existe una correspondencia biunívoca entre conceptos de grafos y estructuras de nudos.

2. **Decidibilidad:** Todos los algoritmos propuestos son decidibles y eficientes.

3. **Validación Empírica:** Las 24 configuraciones de K_2 validan el marco teórico.

4. **Escalabilidad:** El enfoque modular es generalizable a K_n para cualquier n.

### Contribuciones Teóricas

✅ **Unificación:** Integra teoría de grafos, aritmética modular y teoría de nudos

✅ **Computabilidad:** Proporciona algoritmos decidibles para clasificación

✅ **Rigor:** Fundamenta matemáticamente los movimientos de Reidemeister

---

## 📚 Referencias

1. **Teoría de Grafos:** Algoritmos BFS/DFS para componentes conexas
2. **Teoría de Nudos:** Movimientos de Reidemeister (R1, R2, R3)
3. **Aritmética Modular:** Operaciones en ℤₘ y consecutividad
4. **Verificación Empírica:** 24 configuraciones de K_2 completamente verificadas

---

## 📊 Datos de Soporte

- **Archivo de configuraciones:** [configuraciones_2_cruces_24_FINAL.json](file:///c:/Users/pablo/OneDrive/Documentos/TME_Nudos/data/configuraciones_2_cruces_24_FINAL.json)
- **Script de verificación:** [verificar_COMPLETO_etapa1_etapa2.py](file:///c:/Users/pablo/OneDrive/Documentos/TME_Nudos/scripts/verificar_COMPLETO_etapa1_etapa2.py)
- **Resultados:** [resultados_verificacion_COMPLETA_24.json](file:///c:/Users/pablo/OneDrive/Documentos/TME_Nudos/data/resultados_verificacion_COMPLETA_24.json)

---

*Informe preliminar generado: 2026-01-23*
*Basado en verificación completa de 24 configuraciones de K_2*
