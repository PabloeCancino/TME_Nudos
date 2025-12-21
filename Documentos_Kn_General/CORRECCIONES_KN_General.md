# Correcciones a KN_General.lean

## Resumen de Problemas Identificados

Se identificaron problemas en las líneas **149**, **157**, **168** y **249** del archivo `KN_General.lean`. A continuación se explica cada problema y su solución.

---

## Línea 149: Problema con `rw [← h_edge]`

### Problema Original
```lean
have hp2_fst_mem : p2.fst ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  rw [← h_edge]  -- ❌ Error: no puede reescribir directamente
  simp only [Finset.mem_insert, Finset.mem_singleton]
  left
  rfl
```

### Diagnóstico
El problema es que `h_edge : p1.toEdge = p2.toEdge` donde `toEdge` devuelve un `Finset`. Al intentar usar `rw [← h_edge]` para reemplazar `{p1.fst, p1.snd}` con `{p2.fst, p2.snd}`, Lean no puede hacer la reescritura directamente porque `toEdge` necesita ser expandido primero.

### Solución
```lean
have hp2_fst_mem : p2.fst ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  simp only [h_edge.symm, Finset.mem_insert, Finset.mem_singleton]  -- ✅ Usar h_edge.symm
  left
```

**Explicación**: En lugar de `rw`, usamos `simp` con `h_edge.symm` porque:
- `h_edge` tiene tipo `{p1.fst, p1.snd} = {p2.fst, p2.snd}`
- Necesitamos la igualdad en dirección contraria para mostrar membresía de elementos de `p2` en el conjunto de `p1`
- `h_edge.symm` da `{p2.fst, p2.snd} = {p1.fst, p1.snd}`, que es lo que necesitamos

---

## Línea 157: Mismo problema que línea 149

### Problema Original
```lean
have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  rw [← h_edge]; simp  -- ❌ Error: mismo problema de reescritura
```

### Solución
```lean
have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
  simp [h_edge.symm]  -- ✅ Usar h_edge.symm
```

**Explicación**: Misma solución que la línea 149, usando `simp` con `h_edge.symm` para la dirección correcta de la igualdad.

---

## Línea 168: Error en construcción de prueba con `hq_unique`

### Problema Original
```lean
-- Tenemos hf2 : p2.fst = p1.snd
have h2 : p2 = q := hq_unique p2 ⟨hp2, Or.inl hf2⟩  -- ❌ Error de tipo
exact h1.trans h2.symm
```

### Diagnóstico
El problema es que `hq_unique` tiene tipo:
```lean
∀ p ∈ pairs, (p1.fst = p.fst ∨ p1.fst = p.snd) → p = q
```

Estamos intentando aplicarlo con `Or.inl hf2` donde `hf2 : p2.fst = p1.snd`, pero necesitamos probar:
```
p1.fst = p2.fst ∨ p1.fst = p2.snd
```

Tenemos `p2.fst = p1.snd`, pero eso no es lo que necesita `hq_unique`.

### Solución
```lean
· -- p2.fst = p1.snd
  -- Necesitamos demostrar que p2.snd = p1.fst
  have hp2_snd_eq : p2.snd = p1.fst := by
    -- Sabemos p2.fst = p1.snd (por hf2)
    -- p2.snd debe estar en {p1.fst, p1.snd}
    have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
      simp [h_edge.symm]  -- ✅ Usar h_edge.symm para dirección correcta
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp2_snd_mem
    rcases hp2_snd_mem with hs1 | hs2
    · exact hs1
    · -- p2.snd = p1.snd, pero p2.fst = p1.snd → contradicción
      exfalso; exact p2.distinct (hf2.trans hs2.symm)
  have h2 : p2 = q := hq_unique p2 ⟨hp2, Or.inr hp2_snd_eq.symm⟩  -- ✅ Usar .symm para invertir
  exact h1.trans h2.symm
```

**Explicación**: 
1. De `h_edge` sabemos que `{p1.fst, p1.snd} = {p2.fst, p2.snd}`
2. Como `p2.fst = p1.snd` (por `hf2`), entonces `p2.snd` debe ser `p1.fst` (son conjuntos de 2 elementos)
3. Probamos `p2.snd = p1.fst` por casos, descartando la contradicción
4. **Clave**: `hq_unique` necesita `p1.fst = p2.fst ∨ p1.fst = p2.snd`
5. Tenemos `hp2_snd_eq : p2.snd = p1.fst`, pero necesitamos `p1.fst = p2.snd`
6. **Solución**: Usamos `hp2_snd_eq.symm` para invertir la igualdad
7. Ahora podemos usar `hq_unique` con `Or.inr hp2_snd_eq.symm` que prueba `p1.fst = p2.snd`

---

## Línea 249: Uso incorrecto de `card_image_of_injective`

### Problema Original
```lean
private lemma card_image_reverse {n : ℕ} (K : KnConfig n) :
  (K.pairs.image OrderedPairN.reverse).card = n := by
  have h_inv : ∀ x : OrderedPairN n, x.reverse.reverse = x :=
    OrderedPairN.reverse_involutive
  apply Finset.card_image_of_injective  -- ❌ Error: requiere inyectividad global
  intro x y hxy
  calc x = x.reverse.reverse := (h_inv x).symm
       _ = y.reverse.reverse := by rw [hxy]
       _ = y := h_inv y
```

### Diagnóstico
`Finset.card_image_of_injective` tiene tipo:
```lean
∀ {f : α → β}, Injective f → s.card = (s.image f).card
```

Requiere que `f` sea inyectiva **globalmente** sobre todo el tipo, no solo sobre `K.pairs`. Pero nuestra prueba solo muestra inyectividad local (sobre el conjunto `K.pairs`).

### Solución
```lean
private lemma card_image_reverse {n : ℕ} (K : KnConfig n) :
  (K.pairs.image OrderedPairN.reverse).card = n := by
  have h_inv : ∀ x : OrderedPairN n, x.reverse.reverse = x :=
    OrderedPairN.reverse_involutive
  rw [Finset.card_image_of_injOn]  -- ✅ Usar injOn para inyectividad local
  · exact K.card_eq
  · -- Probar que reverse es inyectiva sobre K.pairs
    intro x _ y _ hxy
    calc x = x.reverse.reverse := (h_inv x).symm
         _ = y.reverse.reverse := by rw [hxy]
         _ = y := h_inv y
```

**Explicación**:
- Usamos `Finset.card_image_of_injOn` que tiene tipo:
  ```lean
  ∀ {f : α → β}, Set.InjOn f s → (s.image f).card = s.card
  ```
- Este lema solo requiere que `f` sea inyectiva **sobre el conjunto `s`**, no globalmente
- La prueba es la misma, pero ahora los argumentos de la función incluyen las hipótesis de membresía (`x ∈ K.pairs`, `y ∈ K.pairs`)

---

## Resumen de Técnicas Utilizadas

1. **`simp` vs `rw` con ecuaciones de Finsets**: Cuando trabajamos con igualdades de `Finset`, `simp` es más robusto que `rw` porque puede manejar las definiciones implícitas automáticamente.

2. **Dirección de igualdades con `.symm`**: 
   - `h_edge` tiene tipo `{p1.fst, p1.snd} = {p2.fst, p2.snd}`
   - Para mostrar membresía de elementos de `p2` en el conjunto de `p1`, necesitamos la dirección contraria
   - Usar `h_edge.symm` para obtener `{p2.fst, p2.snd} = {p1.fst, p1.snd}`
   - Similarmente, cuando tenemos `a = b` pero necesitamos `b = a`, usar `.symm`

3. **Construcción cuidadosa de pruebas existenciales**: Para `hq_unique`, necesitamos construir exactamente el tipo esperado (`p1.fst = p.fst ∨ p1.fst = p.snd`), no un tipo similar. Si tenemos la igualdad en dirección contraria, usar `.symm` para invertirla.

4. **Inyectividad local vs global**: 
   - `Finset.card_image_of_injective`: requiere `Injective f` (global)
   - `Finset.card_image_of_injOn`: requiere `Set.InjOn f s` (local sobre `s`)
   - Usar el lema apropiado según lo que podemos probar

---

## Verificación

El archivo corregido `KN_General_Fixed.lean` debería compilar sin errores. Puedes verificarlo con:

```bash
lake build KN_General_Fixed
```

O en el editor de Lean, las líneas problemáticas ahora deberían mostrar marcas verdes (✓) en lugar de errores rojos (✗).