# Progreso de Arreglos TCN_01_Fundamentos.lean

**Fecha:** 2025-12-23 08:25

## Resumen de Progreso

**Errores iniciales:** 25  
**Errores actuales:** ~18  
**Errores arreglados:** 7

## Arreglos Aplicados

### 1. ✅ Configuración de Linter (Línea 8)
- Agregado: `set_option linter.unusedSimpArgs false`
- Elimina warnings de simp arguments no usados

### 2. ✅ Variable No Utilizada (Línea 426)
- Cambio: `salidas` → `_salidas`
- Elimina warning de variable no utilizada

### 3. ✅ Type Mismatch en image_image_involutive (Líneas 483-491)
- Reestructurada la prueba para manejar correctamente el patrón de Finset.mem_image
- Usó `obtain` para descomponer la hipótesis anidada

### 4. ✅ List.mem_cons_self (Líneas 645, 675)
- Cambio: `List.mem_cons_self h t` → `List.mem_cons_self`
- API de Mathlib cambió, ya no requiere argumentos explícitos

### 5. ✅ Comentario de Sintaxis (Línea 462)
- Cambio: `/--` → `/-!`
- Comentario de sección en lugar de documentación

### 6. ✅ Clear Statement Problemático (Líneas 749, 795)
- Eliminado: `clear hx hd_mem hd_eq`
- La variable `hx` se necesita más adelante en la prueba

### 7. ✅ sum_list_ge y sum_list_le (Líneas 664-668, 694-698)
- Reemplazado rewrite fallido con `calc` para cadena de desigualdades
- Usa `hlen` correctamente para conectar `l.length` con `n`

## Errores Restantes (~18)

### Errores Críticos

#### 1. **Omega Failures con ZMod** (Líneas 610, 613, 754, 756, 766)
- **Problema:** `omega` no puede probar bounds en valores de `ZMod 6`
- **Causa:** Necesita información adicional sobre el rango de `p.fst.val` y `p.snd.val` (0-5)
- **Solución:** Agregar `have` statements con bounds explícitos antes de `omega`

#### 2. **List API Changes** (Línea 828)
- **Problema:** `Unknown constant 'List.get?_map'`
- **Causa:** API de Mathlib cambió el nombre
- **Solución:** Buscar el nuevo nombre en Mathlib (probablemente `List.getElem?_map` o similar)

#### 3. **Type Mismatch en Negación** (Línea 636)
- **Problema:** `fun x ↦ -x` vs `fun x ↦ x * -1`
- **Causa:** Diferentes representaciones de negación
- **Solución:** Agregar lema auxiliar que pruebe `∀ x, -x = x * -1`

#### 4. **Rewrite Failure en foldl_add_neg_aux** (Línea 628)
- **Problema:** Pattern mismatch en expresión de foldl
- **Causa:** Simplificación algebraica no reconocida
- **Solución:** Usar `ring_nf` o `simp [neg_add]` antes del rewrite

#### 5. **Unsolved Goals en ZMod Equality** (Líneas 764, 766)
- **Problema:** No puede probar `p.snd = p.fst` desde `↑p.snd.val = ↑p.fst.val`
- **Causa:** Necesita usar `ZMod.val_injective`
- **Solución:** Aplicar `ZMod.val_injective` o `Fin.ext`

### Errores de Pruebas Incompletas (sorry)
- Líneas 396, 706, 895, 902, 909, 919
- **Nota:** Estos son `sorry` statements intencionales, no errores de compilación

### Warnings de Linter
- Doc-strings sin espacio final (Líneas 268, 297, 316, 341, 371, 558, 705)
- **Solución:** Agregar espacio o newline al final de cada doc-string

## Próximos Pasos

1. **Prioridad Alta:** Arreglar omega failures agregando bounds explícitos para ZMod
2. **Prioridad Alta:** Buscar y reemplazar `List.get?_map` con API correcta
3. **Prioridad Media:** Arreglar type mismatch de negación
4. **Prioridad Media:** Arreglar rewrite failure en foldl_add_neg_aux
5. **Prioridad Baja:** Arreglar warnings de doc-strings

## Notas

- Los errores restantes son más complejos y requieren conocimiento profundo de Mathlib
- Muchos errores están relacionados con cambios de API entre versiones de Lean/Mathlib
- Las pruebas con `sorry` son intencionales y no bloquean la compilación de otros módulos
