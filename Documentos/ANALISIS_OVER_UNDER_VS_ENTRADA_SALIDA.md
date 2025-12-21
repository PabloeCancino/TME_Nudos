# Relación entre Over/Under y Entrada/Salida (E/S)

## Resumen

**Estás en lo correcto**: `over/under` (Basic.lean) y `entrada/salida` (E/S en TCN_01_Fundamentos.lean) son **esencialmente los mismos conceptos**, pero aplicados en diferentes niveles de abstracción y con ligeras diferencias de interpretación.

---

## 📊 Comparación Directa

| Aspecto | Basic.lean | TCN_01_Fundamentos.lean |
|---------|------------|-------------------------|
| **Estructura** | `RationalCrossing` | `OrderedPair` |
| **Primer elemento** | `over_pos` | `fst` (entrada E) |
| **Segundo elemento** | `under_pos` | `snd` (salida S) |
| **Espacio** | `ℝ[n]` (general) | `ZMod 6` (específico K₃) |
| **Diferencia** | `modular_ratio` | `pairDelta` |
| **Interpretación** | Topológica (nudo) | Algebraica (modular) |

---

## 🔍 Análisis Detallado

### Basic.lean: Interpretación Topológica

```lean
structure RationalCrossing (n : ℕ) where
  over_pos : ℝ[n]      -- Posición "arriba" del cruce
  under_pos : ℝ[n]     -- Posición "abajo" del cruce
  distinct : over_pos ≠ under_pos
```

**Interpretación**: 
- `over_pos`: Donde el hilo pasa **por arriba** del cruce
- `under_pos`: Donde el hilo pasa **por abajo** del cruce
- **Razón modular**: `[o,u] = under_pos - over_pos`

**Semántica**: Enfocada en la **geometría del nudo** (qué hilo está arriba/abajo).

---

### TCN_01_Fundamentos.lean: Interpretación Algebraica

```lean
structure OrderedPair where
  fst : ZMod 6         -- "Entrada" E del par
  snd : ZMod 6         -- "Salida" S del par
  distinct : fst ≠ snd
```

**Interpretación**:
- `fst` (entrada E): **Punto de entrada** en el par modular
- `snd` (salida S): **Punto de salida** del par modular
- **Desplazamiento modular**: `δ = snd - fst = S - E`

**Semántica**: Enfocada en el **recorrido algebraico** (de dónde a dónde se mueve).

---

## 🔗 Correspondencia Exacta

La relación es:

```
over_pos   ←→   fst (entrada E)
under_pos  ←→   snd (salida S)
modular_ratio  ←→   pairDelta
```

### Fórmulas Equivalentes

**Basic.lean**:
```lean
modular_ratio c = c.under_pos - c.over_pos
```

**TCN_01_Fundamentos**:
```lean
pairDelta p = (p.snd.val : ℤ) - (p.fst.val : ℤ)
```

Ambas calculan **el mismo desplazamiento modular**, pero:
- Basic.lean mantiene el resultado en `ZMod (2*n)`
- TCN_01 convierte a `ℤ` y luego ajusta a rango `[-3, 3]` con `adjustDelta`

---

## 🎯 ¿Por qué dos nombres diferentes?

### Razones Históricas y Conceptuales

1. **Basic.lean** (teoría general):
   - Usa terminología **topológica** clásica de teoría de nudos
   - `over/under` es estándar en literatura de nudos
   - Enfoque: estructura geométrica del cruce

2. **TCN_01_Fundamentos** (aplicación K₃):
   - Usa terminología **algebraica/combinatoria**
   - `entrada/salida` enfatiza el aspecto de recorrido
   - Enfoque: transformaciones modulares

### Ventajas de Cada Terminología

**Over/Under**:
- ✅ Intuitiva para visualización geométrica
- ✅ Estándar en teoría de nudos clásica
- ✅ Clara distinción de niveles (arriba/abajo)

**Entrada/Salida (E/S)**:
- ✅ Intuitiva para procesos de recorrido
- ✅ Natural en contexto algebraico
- ✅ Enfatiza la dirección del desplazamiento

---

## 🧩 Ejemplo Concreto

### En Basic.lean (K₃, n=3)

```lean
-- Cruce con over=0, under=3
c : RationalCrossing 3 := {
  over_pos := 0,      -- Posición "arriba"
  under_pos := 3,     -- Posición "abajo"
  distinct := ...
}

modular_ratio c = 3 - 0 = 3
```

### En TCN_01_Fundamentos (K₃)

```lean
-- Par ordenado equivalente
p : OrderedPair := {
  fst := 0,    -- Entrada E
  snd := 3,    -- Salida S
  distinct := ...
}

pairDelta p = 3 - 0 = 3
adjustDelta 3 = 3  -- Ya está en [-3, 3]
```

**Son el mismo objeto matemático** representado con diferente terminología.

---

## 📐 Diferencias Sutiles

### 1. Espacio de Definición

**Basic.lean**: Genérico para cualquier n
```lean
ℝ[n] = ZMod (2*n)
```

**TCN_01**: Específico para K₃
```lean
ZMod 6  (porque 2*3 = 6)
```

### 2. Procesamiento del Desplazamiento

**Basic.lean**: 
```lean
modular_ratio c : ZMod (2*n)
-- Resultado directo en el anillo modular
```

**TCN_01**:
```lean
pairDelta p : ℤ                    -- Primero a enteros
adjustDelta (pairDelta p) : ℤ     -- Luego ajusta a [-3, 3]
```

TCN_01 hace un paso extra de **ajuste al rango canónico** `[-3, 3]`.

### 3. Interpretación Física

**Basic.lean (over/under)**:
- Refleja la **estructura 3D** del nudo
- `over`: hilo que pasa por encima
- `under`: hilo que pasa por debajo
- Preserva información topológica

**TCN_01 (entrada/salida)**:
- Refleja el **recorrido lineal** en el espacio modular
- `entrada`: donde comienza el segmento
- `salida`: donde termina el segmento
- Enfoque en transformaciones algebraicas

---

## 🔄 Conversión entre Representaciones

### De Basic.lean a TCN_01

```lean
-- RationalCrossing → OrderedPair
def toOrderedPair (c : RationalCrossing 3) : OrderedPair :=
  { fst := c.over_pos,    -- over → entrada
    snd := c.under_pos,   -- under → salida
    distinct := c.distinct }
```

### De TCN_01 a Basic.lean

```lean
-- OrderedPair → RationalCrossing
def toRationalCrossing (p : OrderedPair) : RationalCrossing 3 :=
  { over_pos := p.fst,     -- entrada → over
    under_pos := p.snd,    -- salida → under
    distinct := p.distinct }
```

**Son isomorfos**: la conversión es perfecta en ambas direcciones.

---

## 💡 Recomendaciones

### Para Entender el Código

1. **Basic.lean**: Piensa en términos **geométricos**
   - Visualiza el nudo en 3D
   - `over` = hilo superior, `under` = hilo inferior

2. **TCN_01**: Piensa en términos **algebraicos**
   - Visualiza el recorrido modular
   - `entrada` = punto inicial, `salida` = punto final

### Para Trabajar con Ambos

- Son **intercambiables** conceptualmente
- La diferencia es mayormente **semántica**
- Ambos representan el **mismo objeto matemático**

---

## 📚 Conclusión

**Respuesta directa a tu pregunta**:

> **SÍ, estás en lo correcto**. 
>
> `over_pos/under_pos` (Basic.lean) y `fst/snd` como entrada/salida (TCN_01)
> son **esencialmente los mismos elementos**, representando:
> - El **mismo par ordenado** de posiciones
> - El **mismo desplazamiento modular**
> - La **misma estructura matemática**
>
> La diferencia principal es de **interpretación**:
> - Basic.lean: énfasis **topológico** (arriba/abajo del cruce)
> - TCN_01: énfasis **algebraico** (entrada/salida del recorrido)
>
> Pero matemáticamente, **son equivalentes**.

---

## 🎓 Contexto Teórico

Esta dualidad terminológica refleja dos perspectivas complementarias en teoría de nudos:

1. **Perspectiva Geométrica** (over/under)
   - Heredada de la teoría clásica de nudos
   - Enfatiza la estructura 3D y los cruces
   - Natural para visualización

2. **Perspectiva Algebraica** (entrada/salida)
   - Moderna, basada en invariantes algebraicos
   - Enfatiza transformaciones y recorridos
   - Natural para computación

Ambas son válidas y **complementarias**, no contradictorias.

---

**Autor**: Análisis comparativo TME  
**Fecha**: Diciembre 2025  
**Archivos**: Basic.lean, TCN_01_Fundamentos.lean
