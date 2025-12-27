# Análisis del Problema con h_edge.symm

## Contexto

En el teorema `toMatching_card`, estamos probando que la función `toEdge` es inyectiva sobre los pares de la configuración.

## El Problema Original

### Línea 142
```lean
h_edge : p1.toEdge = p2.toEdge
```

Esto significa: `{p1.fst, p1.snd} = {p2.fst, p2.snd}`

### Líneas 150, 156, 174

En estas líneas intentábamos probar membresías como:
- `p2.fst ∈ {p1.fst, p1.snd}`
- `p2.snd ∈ {p1.fst, p1.snd}`

Usando:
```lean
simp [h_edge.symm]
```

## ¿Por qué falla `simp [h_edge.symm]`?

### Análisis de la dirección

1. **h_edge** nos da: `{p1.fst, p1.snd} = {p2.fst, p2.snd}`
2. **h_edge.symm** nos da: `{p2.fst, p2.snd} = {p1.fst, p1.snd}`

### El objetivo

Queremos probar: `p2.fst ∈ {p1.fst, p1.snd}`

### El razonamiento lógico

1. Es trivial que: `p2.fst ∈ {p2.fst, p2.snd}` (por definición de inserción)
2. Tenemos: `{p1.fst, p1.snd} = {p2.fst, p2.snd}` (por h_edge)
3. Por tanto: `p2.fst ∈ {p1.fst, p1.snd}` (reescribiendo con ← h_edge)

### El problema con `simp [h_edge.symm]`

La táctica `simp` puede tener comportamiento impredecible con la dirección de la reescritura:

- **h_edge.symm** da `{p2.fst, p2.snd} = {p1.fst, p1.snd}`
- Pero el objetivo es `p2.fst ∈ {p1.fst, p1.snd}`
- `simp` podría intentar reescribir el conjunto objetivo usando la igualdad
- Sin embargo, la dirección y el comportamiento de `simp` no siempre son predecibles

## La Solución

Usar **`rw [← h_edge]`** en lugar de `simp [h_edge.symm]`:

```lean
have hp2_fst_mem : p2.fst ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  rw [← h_edge]          -- Reescribe {p1.fst, p1.snd} → {p2.fst, p2.snd}
  simp [OrderedPairN.toEdge]  -- Ahora p2.fst ∈ {p2.fst, p2.snd} es trivial
```

### ¿Por qué funciona `rw [← h_edge]`?

1. **`← h_edge`** significa "reescribir de derecha a izquierda"
2. h_edge es `{p1.fst, p1.snd} = {p2.fst, p2.snd}`
3. **`← h_edge`** reescribe `{p1.fst, p1.snd}` → `{p2.fst, p2.snd}`
4. El objetivo se convierte en: `p2.fst ∈ {p2.fst, p2.snd}`
5. Esto es trivialmente verdadero por `simp [OrderedPairN.toEdge]`

## Diferencias entre `rw` y `simp`

| Táctica | Comportamiento | Predictibilidad |
|---------|---------------|-----------------|
| `rw [← h_edge]` | Reescritura **exacta** en la dirección especificada | Alta |
| `simp [h_edge.symm]` | Simplificación **heurística** que puede usar la igualdad | Media-Baja |

**Conclusión**: Para reescrituras específicas de igualdades, `rw` es más confiable que `simp`.

## Cambios Aplicados

### Línea 150 (original 149-151)
```lean
-- ANTES:
have hp2_fst_mem : p2.fst ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  simp only [h_edge.symm, Finset.mem_insert, Finset.mem_singleton]
  left; rfl

-- DESPUÉS:
have hp2_fst_mem : p2.fst ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  rw [← h_edge]
  simp [OrderedPairN.toEdge]
```

### Línea 156 (original 156-157)
```lean
-- ANTES:
have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  simp [h_edge.symm]

-- DESPUÉS:
have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  rw [← h_edge]
  simp [OrderedPairN.toEdge]
```

### Línea 174 (original 173-174)
```lean
-- ANTES:
have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  simp [h_edge.symm]

-- DESPUÉS:
have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  rw [← h_edge]
  simp [OrderedPairN.toEdge]
```

## Lección General

**Principio**: Cuando necesitas reescribir usando una igualdad en una dirección específica:

✅ **Usa `rw`** - control exacto de la dirección
❌ **Evita `simp` solo** - comportamiento menos predecible

**Patrón común**:
```lean
rw [← equality]   -- Reescribe de derecha a izquierda
rw [equality]     -- Reescribe de izquierda a derecha
simp             -- Luego simplifica lo que quede
```
