# Matriz de Incidencia Extendida: De ℝ² a ℝ³

## 🎯 La Idea Fundamental

### Matriz Actual (ℝ²)

La matriz de incidencia tradicional solo indica **si** un arco incide en un vértice:

```
Valor = {0, 1, 2, ...}  (multiplicidad)
```

**Información codificada:**
- ✅ Conectividad (qué arcos conectan qué vértices)
- ❌ Profundidad (over/under)

### Matriz Extendida (ℝ³)

Usando **signos** para codificar la tercera dimensión:

```
Valor ∈ ℤ  (enteros con signo)
  +n: El arco pasa OVER (sobre) n veces
  -n: El arco pasa UNDER (bajo) n veces
   0: El arco no incide
```

**Información codificada:**
- ✅ Conectividad
- ✅ **Profundidad (over/under)**

---

## 📊 Ejemplo: K_3_5 en ℝ³

### Matriz Original (ℝ²)

|     | a₁  | a₂  | a₃  | a₄  | a₅  | a₆  |
| --- | --- | --- | --- | --- | --- | --- |
| v₁  | 2   | 1   | 1   | 0   | 0   | 0   |
| v₂  | 0   | 1   | 0   | 1   | 1   | 1   |
| v₃  | 0   | 0   | 1   | 1   | 1   | 1   |

### Matriz Extendida (ℝ³) con Información Over/Under

Dado que K_3_5 = {V₁(0,3), V₂(1,4), V₃(2,5)}:
- V₁: arco 0 pasa **over** arco 3
- V₂: arco 1 pasa **over** arco 4
- V₃: arco 2 pasa **over** arco 5

**Interpretación:**
- En v₁: a₁ (arco 0) → +2 (bucle over), a₂ (arco 3) → -1 (under)
- En v₂: a₂ (arco 1) → +1 (over), a₄ (arco 4) → -1 (under)
- En v₃: a₃ (arco 2) → +1 (over), a₄,a₅,a₆ (arco 5) → -1 (under)

|     | a₁     | a₂     | a₃     | a₄     | a₅     | a₆     |
| --- | ------ | ------ | ------ | ------ | ------ | ------ |
| v₁  | **+2** | **+1** | **-1** | 0      | 0      | 0      |
| v₂  | 0      | **+1** | 0      | **-1** | **-1** | **-1** |
| v₃  | 0      | 0      | **+1** | **-1** | **-1** | **-1** |

---

## 🔧 Reglas de Construcción

### Para cada cruce Vᵢ(oᵢ, uᵢ):

1. **Arco over (oᵢ):**
   - Matriz[i][oᵢ] = **+n** (donde n es la multiplicidad)

2. **Arco under (uᵢ):**
   - Matriz[i][uᵢ] = **-n** (donde n es la multiplicidad)

3. **Otros arcos:**
   - Matriz[i][j] = 0

### Ejemplo: V₁(0,3)

```
Cruce V₁: arco 0 pasa OVER arco 3

Matriz[1][0] = +1  (arco 0 es over)
Matriz[1][3] = -1  (arco 3 es under)
```

---

## 📐 Propiedades de la Matriz ℝ³

### 1. Conservación de Información

La matriz extendida preserva **toda** la información:

```
|Matriz[i][j]| → Multiplicidad (conectividad)
sign(Matriz[i][j]) → Profundidad (over/under)
```

### 2. Suma de Filas = 0

Para cada cruce (fila), la suma debe ser 0:

```
∑ⱼ Matriz[i][j] = 0
```

**Razón:** Cada cruce tiene igual número de arcos over y under.

### 3. Cálculo del Writhe

El writhe se puede calcular directamente:

```
writhe = ∑ᵢ sign(det(orientación_cruce_i))
```

O simplemente contar signos en la diagonal de cruces.

---

## 🎯 Ventajas de la Representación ℝ³

### 1. Información Completa en Una Sola Estructura

✅ **Antes (ℝ²):** Necesitábamos:
- Matriz de incidencia (conectividad)
- Pares ordenados (over/under)

✅ **Ahora (ℝ³):** Solo necesitamos:
- Matriz de incidencia extendida (todo incluido)

### 2. Cálculos Más Directos

```python
# Calcular writhe
writhe = sum(sign(matriz[i][over_i]) for i in cruces)

# Detectar orientación
orientacion_i = sign(matriz[i][over_i])
```

### 3. Compatibilidad con Álgebra Lineal

Podemos usar operaciones matriciales estándar:

```
Transpuesta: Matriz^T
Producto: Matriz₁ × Matriz₂
Determinante: det(Matriz)
```

---

## 🔬 Ejemplo Completo: K_3_1

### Configuración
K_3_1 = {V₁(0,3), V₂(4,1), V₃(2,5)}

### Matriz ℝ³

|     | a₀     | a₁     | a₂     | a₃     | a₄     | a₅     |
| --- | ------ | ------ | ------ | ------ | ------ | ------ |
| v₁  | **+1** | 0      | 0      | **-1** | 0      | 0      |
| v₂  | 0      | **-1** | 0      | 0      | **+1** | 0      |
| v₃  | 0      | 0      | **+1** | 0      | 0      | **-1** |

### Verificación

**Suma de filas:**
- v₁: +1 + (-1) = 0 ✅
- v₂: -1 + (+1) = 0 ✅
- v₃: +1 + (-1) = 0 ✅

**Writhe:**
```
writhe = sign(+1) + sign(+1) + sign(+1) = +1 + 1 + 1 = +3 ✅
```

---

## 📊 Comparación: ℝ² vs ℝ³

| Aspecto          | Matriz ℝ²                  | Matriz ℝ³             |
| ---------------- | -------------------------- | --------------------- |
| **Valores**      | {0, 1, 2, ...}             | ℤ (enteros con signo) |
| **Conectividad** | ✅                          | ✅                     |
| **Profundidad**  | ❌                          | ✅                     |
| **Writhe**       | ❌ Requiere cálculo externo | ✅ Directo             |
| **Orientación**  | ❌ Requiere pares ordenados | ✅ En la matriz        |
| **Espacio**      | ℝ²                         | ℝ³                    |

---

## 🔧 Implementación en Python

```python
import numpy as np

def construir_matriz_R3(cruces, m):
    """
    Construye matriz de incidencia en ℝ³.
    
    Args:
        cruces: Lista de (over, under) para cada cruce
        m: Número de arcos (módulo)
    
    Returns:
        Matriz de incidencia con signos
    """
    n = len(cruces)
    matriz = np.zeros((n, m), dtype=int)
    
    for i, (over, under) in enumerate(cruces):
        matriz[i][over] = +1   # Over → positivo
        matriz[i][under] = -1  # Under → negativo
    
    return matriz

# Ejemplo: K_3_1
cruces_K31 = [(0, 3), (4, 1), (2, 5)]
matriz_K31 = construir_matriz_R3(cruces_K31, m=6)

print("Matriz ℝ³ de K_3_1:")
print(matriz_K31)

# Calcular writhe
writhe = np.sum(matriz_K31 > 0, axis=1).sum()
print(f"Writhe: {writhe}")
```

---

## 🎯 Aplicaciones

### 1. Detección Automática de R1

```python
def detectar_R1_matriz(matriz, i):
    """Detecta R1 en cruce i usando la matriz."""
    arcos_positivos = np.where(matriz[i] > 0)[0]
    arcos_negativos = np.where(matriz[i] < 0)[0]
    
    for over in arcos_positivos:
        for under in arcos_negativos:
            if son_consecutivos_mod(over, under):
                return True
    return False
```

### 2. Cálculo de Invariantes

```python
def calcular_invariantes(matriz):
    """Calcula invariantes del nudo desde la matriz."""
    n_cruces = matriz.shape[0]
    
    # Writhe
    writhe = sum(np.sign(matriz[i][matriz[i] > 0]).sum() 
                 for i in range(n_cruces))
    
    # Número de cruces positivos/negativos
    positivos = sum(1 for i in range(n_cruces) 
                    if (matriz[i] > 0).any())
    
    return {
        'writhe': writhe,
        'cruces_positivos': positivos,
        'cruces_negativos': n_cruces - positivos
    }
```

---

## ✅ Conclusiones

### Ventajas de ℝ³

1. ✅ **Información completa** en una sola estructura
2. ✅ **Cálculos directos** de invariantes
3. ✅ **Compatible** con álgebra lineal
4. ✅ **Más eficiente** computacionalmente

### Fórmula de Conversión

```
Matriz ℝ² + Pares Ordenados → Matriz ℝ³

Matriz_ℝ³[i][j] = {
  +|Matriz_ℝ²[i][j]|  si j es over en cruce i
  -|Matriz_ℝ²[i][j]|  si j es under en cruce i
   0                  si j no incide en cruce i
}
```

### Próximos Pasos

1. Implementar construcción automática de matrices ℝ³
2. Actualizar algoritmos para usar matrices ℝ³
3. Calcular invariantes directamente desde la matriz
4. Extender a grafos dirigidos ponderados

---

*Documento técnico sobre matrices de incidencia en ℝ³*
*Generado: 2026-01-23*
