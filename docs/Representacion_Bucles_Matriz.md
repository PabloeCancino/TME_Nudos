# Representación de Bucles (R1) en Matrices de Incidencia

## 🎯 El Problema: (v₁, a₁) = +2

### ¿Qué Significa?

En la matriz de incidencia:

```
|     | a₁  | a₂  | a₃  | ... |
| --- | --- | --- | --- | --- |
| v₁  | +2  | +1  | -1  | ... |
```

**Matriz[v₁][a₁] = +2** significa:
- El arco a₁ incide **dos veces** en el vértice v₁
- Ambas incidencias son **over** (positivo)
- Es un **BUCLE** (loop): el arco sale y regresa al mismo vértice

---

## 📐 Visualización del Bucle

### Diagrama Conceptual

```
        ╭──── a₁ ────╮
        │            │
        │   (bucle)  │
        ↓            ↑
       v₁ ──────────┘
      (cruce)
```

### Interpretación Topológica

1. El arco a₁ **sale** de v₁ (primera incidencia: +1)
2. El arco a₁ **regresa** a v₁ (segunda incidencia: +1)
3. Total: +1 + 1 = **+2**

### En Términos de Nudos

Esto es un **rizo** (kink) o **twist** - exactamente el patrón que elimina **Reidemeister I**.

---

## 🔍 Tipos de Bucles

### Bucle Over (+2)

```
Matriz[i][j] = +2
```

**Significado:** El arco j forma un bucle que pasa **sobre sí mismo** en el cruce i.

```
    ╭─────╮
    │  ↑  │  (arco pasa sobre)
    │  │  │
    v₁────┘
```

### Bucle Under (-2)

```
Matriz[i][j] = -2
```

**Significado:** El arco j forma un bucle que pasa **bajo sí mismo** en el cruce i.

```
    ╭─────╮
    │  ↓  │  (arco pasa bajo)
    │  │  │
    v₁────┘
```

### Bucle Mixto (+1, -1)

```
Matriz[i][j] = 0  (pero con estructura especial)
```

Si un arco pasa una vez over y una vez under en el mismo vértice, se cancelan.

---

## 🎯 Detección de R1 en la Matriz

### Regla de Detección

Un cruce i tiene **R1 aplicable** si:

```
∃ j tal que |Matriz[i][j]| ≥ 2
```

**Interpretación:** Hay un arco que incide múltiples veces en el mismo cruce.

### Algoritmo

```python
def detectar_R1_bucle(matriz):
    """
    Detecta bucles (R1) en la matriz de incidencia.
    
    Returns:
        Lista de (cruce, arco, multiplicidad)
    """
    bucles = []
    n_cruces, n_arcos = matriz.shape
    
    for i in range(n_cruces):
        for j in range(n_arcos):
            if abs(matriz[i][j]) >= 2:
                bucles.append({
                    'cruce': i + 1,
                    'arco': j + 1,
                    'multiplicidad': abs(matriz[i][j]),
                    'tipo': 'over' if matriz[i][j] > 0 else 'under',
                    'R1_aplicable': True
                })
    
    return bucles
```

---

## 📊 Ejemplo: K_3_5

### Matriz

```
|     | a₁  | a₂  | a₃  | a₄  | a₅  | a₆  |
| --- | --- | --- | --- | --- | --- | --- |
| v₁  | +2  | +1  | -1  | 0   | 0   | 0   |
| v₂  | 0   | +1  | 0   | -1  | -1  | -1  |
| v₃  | 0   | 0   | +1  | -1  | -1  | -1  |
```

### Detección de Bucles

```python
bucles_K35 = detectar_R1_bucle(matriz_K35)

# Resultado:
# [{
#   'cruce': 1,
#   'arco': 1,
#   'multiplicidad': 2,
#   'tipo': 'over',
#   'R1_aplicable': True
# }]
```

**Interpretación:**
- Cruce v₁ tiene un bucle en arco a₁
- Multiplicidad 2 (bucle completo)
- Tipo: over (pasa sobre sí mismo)
- **R1 aplicable** ✅

---

## 🎨 Representación Visual Mejorada

### Notación Gráfica

Para hacer más comprensible el bucle en la matriz:

```
|     | a₁     | a₂  | a₃  | a₄  | a₅  | a₆  |
| --- | ------ | --- | --- | --- | --- | --- |
| v₁  | +2 (⟲) | +1  | -1  | 0   | 0   | 0   |
| v₂  | 0      | +1  | 0   | -1  | -1  | -1  |
| v₃  | 0      | 0   | +1  | -1  | -1  | -1  |
```

**Símbolos:**
- **(⟲)** = Bucle over (sentido horario)
- **(⟳)** = Bucle under (sentido antihorario)

### Anotación Textual

```
Matriz de Incidencia con Anotaciones:

v₁: [+2(bucle), +1, -1, 0, 0, 0]
    └─ a₁ forma un bucle over en v₁ → R1 aplicable
    
v₂: [0, +1, 0, -1, -1, -1]
    └─ Sin bucles
    
v₃: [0, 0, +1, -1, -1, -1]
    └─ Sin bucles
```

---

## 🔧 Representación en Código

### Clase para Bucles

```python
class Bucle:
    def __init__(self, cruce, arco, multiplicidad, tipo):
        self.cruce = cruce
        self.arco = arco
        self.multiplicidad = multiplicidad
        self.tipo = tipo  # 'over' o 'under'
    
    def __str__(self):
        simbolo = '⟲' if self.tipo == 'over' else '⟳'
        return f"Bucle {simbolo} en v_{self.cruce} (arco a_{self.arco})"
    
    def es_R1_aplicable(self):
        return self.multiplicidad >= 2

# Ejemplo
bucle_K35 = Bucle(cruce=1, arco=1, multiplicidad=2, tipo='over')
print(bucle_K35)  # "Bucle ⟲ en v_1 (arco a_1)"
print(f"R1 aplicable: {bucle_K35.es_R1_aplicable()}")  # True
```

---

## 📋 Tabla de Interpretación

| Valor  | Significado       | Visualización | R1  |
| ------ | ----------------- | ------------- | --- |
| **+2** | Bucle over        | ⟲             | ✅   |
| **-2** | Bucle under       | ⟳             | ✅   |
| **+1** | Arco over normal  | →             | ❌   |
| **-1** | Arco under normal | ←             | ❌   |
| **0**  | Sin incidencia    | ·             | ❌   |

---

## 🎯 Aplicación a Movimientos de Reidemeister

### R1: Eliminar Bucles

Si detectamos `Matriz[i][j] = ±2`:

1. **Identificar** el bucle
2. **Aplicar R1** para eliminarlo
3. **Actualizar** la matriz:
   - Eliminar fila i (cruce)
   - Eliminar columna j (arco del bucle)
   - Reducir dimensión de la matriz

### Ejemplo: Eliminar Bucle en K_3_5

**Antes:**
```
|     | a₁  | a₂  | a₃  | a₄  | a₅  | a₆  |
| --- | --- | --- | --- | --- | --- | --- |
| v₁  | +2  | +1  | -1  | 0   | 0   | 0   | ← Eliminar |
| v₂  | 0   | +1  | 0   | -1  | -1  | -1  |
| v₃  | 0   | 0   | +1  | -1  | -1  | -1  |
       ↑
    Eliminar
```

**Después de R1:**
```
|     | a₂  | a₃  | a₄  | a₅  | a₆  |
| --- | --- | --- | --- | --- | --- |
| v₂  | +1  | 0   | -1  | -1  | -1  |
| v₃  | 0   | +1  | -1  | -1  | -1  |
```

Nudo simplificado con 2 cruces.

---

## ✅ Resumen

### Interpretación de (v₁, a₁) = +2

1. **Topológicamente:** Bucle (loop) en el vértice v₁
2. **Visualmente:** ⟲ (rizo que pasa sobre sí mismo)
3. **En teoría de nudos:** Patrón de Reidemeister I
4. **Acción:** Eliminable mediante R1

### Representación Comprensible

**Opción 1 - Símbolo:**
```
v₁: [+2⟲, +1, -1, ...]
```

**Opción 2 - Anotación:**
```
v₁: [+2(bucle), +1, -1, ...]
```

**Opción 3 - Color/Formato:**
```
v₁: [**+2**, +1, -1, ...]  ← Bucle detectado (R1)
```

---

*Documento sobre representación de bucles en matrices de incidencia*
*Generado: 2026-01-23*
