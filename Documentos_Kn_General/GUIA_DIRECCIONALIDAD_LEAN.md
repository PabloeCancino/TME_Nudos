# Guía Rápida: Errores de Direccionalidad en Lean

## Problema Principal: Direccionalidad de Igualdades

En Lean, las igualdades tienen **dirección**. Cuando tienes `h : a = b`, esto NO es lo mismo que tener `b = a` para propósitos de reescritura y simplificación.

### Síntomas Comunes

**Error 1: Type mismatch con igualdades**
```
Type mismatch
  h_edge
has type
  {p1.fst, p1.snd} = {p2.fst, p2.snd}
but is expected to have type
  {p2.fst, p2.snd} = {p1.fst, p1.snd}
```

**Error 2: Application type mismatch**
```
Application type mismatch: The argument
  hp2_snd_eq
has type
  p2.snd = p1.fst
but is expected to have type
  p1.fst = p2.snd
```

---

## Solución: Usar `.symm`

### Concepto Básico

Si tienes `h : a = b` y necesitas `b = a`, usa `h.symm`:

```lean
-- Tienes esto:
h : a = b

-- Necesitas esto:
goal : b = a

-- Solución:
exact h.symm
```

### Aplicación en Contexto de Finsets

```lean
-- Tenemos:
h_edge : {p1.fst, p1.snd} = {p2.fst, p2.snd}

-- Queremos mostrar:
p2.fst ∈ {p1.fst, p1.snd}

-- ❌ INCORRECTO:
simp [h_edge]  -- Dirección equivocada

-- ✅ CORRECTO:
simp [h_edge.symm]  -- Invierte la igualdad primero
```

---

## Casos Específicos del Archivo

### Caso 1: Membresía en Finsets (Líneas 149, 157)

**Situación**: Tenemos `h_edge : {p1.fst, p1.snd} = {p2.fst, p2.snd}` y queremos mostrar que elementos de `p2` están en el conjunto de `p1`.

```lean
-- ❌ INCORRECTO:
have hp2_fst_mem : p2.fst ∈ {p1.fst, p1.snd} := by
  simp [h_edge]  -- Esta dirección no ayuda

-- ✅ CORRECTO:
have hp2_fst_mem : p2.fst ∈ {p1.fst, p1.snd} := by
  simp [h_edge.symm]  -- Ahora {p2.fst, p2.snd} = {p1.fst, p1.snd}
```

**Explicación**: 
- `simp [h_edge]` intenta reemplazar `{p1.fst, p1.snd}` con `{p2.fst, p2.snd}`, lo cual nos aleja del objetivo
- `simp [h_edge.symm]` reconoce que `p2.fst ∈ {p2.fst, p2.snd}` y luego usa la igualdad invertida

### Caso 2: Construcción de Pruebas (Línea 168)

**Situación**: Una función espera `a = b` pero tenemos `b = a`.

```lean
-- Tenemos:
hp2_snd_eq : p2.snd = p1.fst

-- Una función necesita:
hq_unique : ... → (p1.fst = p.fst ∨ p1.fst = p.snd) → ...

-- ❌ INCORRECTO:
hq_unique p2 ⟨hp2, Or.inr hp2_snd_eq⟩  
-- Error: Or.inr espera p1.fst = p2.snd, no p2.snd = p1.fst

-- ✅ CORRECTO:
hq_unique p2 ⟨hp2, Or.inr hp2_snd_eq.symm⟩
-- Ahora Or.inr tiene p1.fst = p2.snd como necesita
```

---

## Reglas Generales

### 1. Diagnóstico Rápido

Si ves este error:
```
has type: a = b
but is expected to have type: b = a
```

**Solución inmediata**: Agregar `.symm` al término.

### 2. Con `simp` y `rw`

```lean
-- Para simp:
simp [h]       -- Usa h : a = b para reemplazar a con b
simp [h.symm]  -- Usa b = a para reemplazar b con a

-- Para rw:
rw [h]         -- Reemplaza a con b (izquierda → derecha)
rw [← h]       -- Reemplaza b con a (derecha → izquierda)
```

### 3. En Aplicaciones de Funciones

Cuando aplicas una función que espera un argumento de cierto tipo:

```lean
-- Función espera:
f : (x = y) → Result

-- Tienes:
h : y = x

-- Solución:
f h.symm
```

---

## Patrones Comunes en Pruebas de Igualdad

### Patrón 1: Cadena Transitiva
```lean
-- Queremos: a = c
h1 : a = b
h2 : b = c

-- Solución:
exact h1.trans h2
```

### Patrón 2: Simetría más Transitividad
```lean
-- Queremos: a = c
h1 : b = a  -- Dirección "equivocada"
h2 : b = c

-- Solución:
exact h1.symm.trans h2  -- Primero invierte, luego encadena
```

### Patrón 3: En Casos Disyuntivos
```lean
-- Una prueba única requiere una de dos formas:
hp_unique : ... → (a = p.fst ∨ a = p.snd) → ...

-- Tienes: h : p.fst = a (dirección equivocada)
-- Solución: Or.inl h.symm

-- Tienes: h : p.snd = a (dirección equivocada)  
-- Solución: Or.inr h.symm
```

---

## Checklist para Debugging

Cuando encuentres un error de tipo con igualdades:

- [ ] ¿El error menciona `has type: X = Y` pero `expected: Y = X`?
- [ ] Si sí, ¿puedes agregar `.symm` al término problemático?
- [ ] ¿Estás usando `simp` o `rw` con una igualdad en la dirección equivocada?
- [ ] Si sí, prueba agregar `.symm` a la hipótesis o usar `← ` con `rw`
- [ ] ¿Estás construyendo un `Or.inl` o `Or.inr`?
- [ ] Si sí, verifica que la dirección de la igualdad coincida con lo esperado

---

## Resumen: Cuándo Usar `.symm`

**Siempre que**:
1. Tengas `a = b` pero necesites `b = a`
2. El error diga "has type X = Y but expected Y = X"
3. La dirección de una igualdad no coincida con lo que espera una función
4. Quieras simplificar en la "otra dirección"

**Recuerda**: `.symm` es tu amigo más frecuente en pruebas de igualdad. No dudes en usarlo liberalmente.