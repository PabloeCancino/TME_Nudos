# Estrategia para Resolver los Sorry de TCN_01_Fundamentos.lean

**Fecha**: Diciembre 2025  
**Autor**: Dr. Pablo Eduardo Cancino Marentes  
**Estado**: 6 sorry pendientes de 10 originales

---

## 📊 Resumen Ejecutivo

### Estado Actual
- **✅ Teoremas probados**: 4/10 (40%)
- **⚙️ Requieren análisis**: 3/10 (30%)
- **🔧 Bloqueados**: 6/10 (60%)

### Problema Principal
**`mirror` está implementado como función identidad**, lo que bloquea 6 teoremas sobre reflexión especular.

---

## 🎯 Roadmap de Resolución

### FASE 1: Probar Teoremas Inmediatos ✅ COMPLETA

#### 1.1 `normalize_preserves_matching` ✓
```lean
theorem normalize_preserves_matching (K : K3Config) :
  K.normalize.toMatching = K.toMatching := by
  rfl
```
**Status**: ✅ PROBADO  
**Razón**: Con `normalize = K`, es trivial por reflexividad.

#### 1.2 `ime_from_dme` ✓
```lean
theorem ime_from_dme (K : K3Config) :
  K.ime = K.dme.map Int.natAbs := by
  rfl
```
**Status**: ✅ PROBADO  
**Razón**: Definición directa de `ime`.

#### 1.3 `gap_from_ime` ✓
```lean
theorem gap_from_ime (K : K3Config) :
  K.gap = K.ime.foldl (· + ·) 0 := by
  rfl
```
**Status**: ✅ PROBADO  
**Razón**: Definición directa de `gap`.

---

### FASE 2: Análisis Estructural (Requiere Lemas Auxiliares) ⚙️

#### 2.1 `dme_decomposition`

**Teorema**:
```lean
theorem dme_decomposition (K : K3Config) :
  ∀ i, i < 3 →
    ∃ (mag : ℕ) (sgn : ℤ),
      K.ime[i]? = some mag ∧
      K.chiralSigns[i]? = some sgn ∧
      K.dme[i]? = some (mag * sgn)
```

**Estrategia**:
1. Probar que `K.pairsList.length = 3` (por `K.card_eq`)
2. Probar que `K.dme.length = 3` (por construcción map sobre lista de longitud 3)
3. Para cada `i < 3`:
   - `K.dme[i]? = some δ` para algún `δ : ℤ`
   - `K.ime[i]? = some |δ|`
   - `K.chiralSigns[i]? = some (sgn δ)`
   - Usar propiedad aritmética: `δ = |δ| * sgn(δ)` para `δ ≠ 0`

**Lemas necesarios**:
```lean
-- Longitud de listas mapeadas
lemma map_length {α β : Type*} (f : α → β) (l : List α) :
  (l.map f).length = l.length

-- Acceso consistente en listas mapeadas  
lemma getElem_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]? = some (f l[i])

-- Propiedad aritmética fundamental
lemma int_abs_sign_decomp (n : ℤ) (hn : n ≠ 0) :
  n = Int.natAbs n * Int.sign n
```

**Dificultad**: Media  
**Tiempo estimado**: 2-3 horas

---

#### 2.2 `gap_ge_three`

**Teorema**:
```lean
theorem gap_ge_three (K : K3Config) : K.gap ≥ 3
```

**Estrategia**:
1. Desplegar definiciones: `K.gap = K.ime.foldl (· + ·) 0`
2. Probar que `K.ime` tiene exactamente 3 elementos
3. Probar que cada elemento `|δᵢ| ≥ 1` porque:
   - Por `adjustDelta`, tenemos `δᵢ ∈ [-3, 3]`
   - Por `distinct` en `OrderedPair`, `δᵢ ≠ 0`
   - Por tanto `|δᵢ| ≥ 1`
4. Concluir: `Σ|δᵢ| ≥ 3 × 1 = 3`

**Lemas necesarios**:
```lean
-- Propiedad de adjustDelta
lemma adjustDelta_nonzero (p : OrderedPair) :
  adjustDelta (pairDelta p) ≠ 0

-- Cota inferior de valor absoluto
lemma natAbs_pos_of_nonzero (n : ℤ) (hn : n ≠ 0) :
  Int.natAbs n ≥ 1

-- Suma de lista acotada
lemma sum_list_ge (l : List ℕ) (h : l.length = n) (hbound : ∀ x ∈ l, x ≥ m) :
  l.foldl (· + ·) 0 ≥ n * m
```

**Dificultad**: Media  
**Tiempo estimado**: 2-3 horas

---

#### 2.3 `gap_le_nine`

**Teorema**:
```lean
theorem gap_le_nine (K : K3Config) : K.gap ≤ 9
```

**Estrategia**:
1. Similar a `gap_ge_three` pero con cota superior
2. Probar que cada `|δᵢ| ≤ 3` porque:
   - `adjustDelta` garantiza `δᵢ ∈ [-3, 3]`
   - Por tanto `|δᵢ| ≤ 3`
3. Concluir: `Σ|δᵢ| ≤ 3 × 3 = 9`

**Lemas necesarios**:
```lean
-- Propiedad de adjustDelta
lemma adjustDelta_bounded (δ : ℤ) :
  -3 ≤ adjustDelta δ ∧ adjustDelta δ ≤ 3

-- Cota superior de valor absoluto
lemma natAbs_le_of_bounded (n : ℤ) (h : -m ≤ n ∧ n ≤ m) :
  Int.natAbs n ≤ m

-- Suma de lista acotada superiormente
lemma sum_list_le (l : List ℕ) (h : l.length = n) (hbound : ∀ x ∈ l, x ≤ m) :
  l.foldl (· + ·) 0 ≤ n * m
```

**Dificultad**: Media  
**Tiempo estimado**: 2-3 horas

---

### FASE 3: Implementar Mirror Correctamente 🔧 CRÍTICO

**Problema actual**:
```lean
def mirror (K : K3Config) : K3Config := K  -- ❌ INCORRECTO
```

**Implementación correcta requerida**:
```lean
def mirror (K : K3Config) : K3Config :=
  -- Invertir cada par (e, s) ↦ (s, e)
  let reversed_pairs := K.pairs.image OrderedPair.reverse
  -- Construir nueva K3Config con pares invertidos
  ⟨reversed_pairs, sorry, sorry⟩
```

**Desafíos**:
1. Probar que `reversed_pairs.card = 3`
   - Necesitamos que `reverse` sea biyectiva sobre `K.pairs`
   - Ya tenemos `reverse_involutive`

2. Probar que sigue siendo partición
   - Más complejo: si `(e, s)` está en la partición, entonces `(s, e)` también particiona Z/6Z
   - Requiere análisis de la propiedad `is_partition`

**Lemas necesarios**:
```lean
-- Cardinalidad bajo imagen de función involutiva
lemma card_image_involutive {α : Type*} [DecidableEq α] 
  (s : Finset α) (f : α → α) (hf : ∀ x, f (f x) = x) :
  (s.image f).card = s.card

-- Partición se preserva bajo inversión de pares
lemma partition_reverse (K : K3Config) :
  ∀ i : ZMod 6, ∃! p ∈ (K.pairs.image OrderedPair.reverse), i = p.fst ∨ i = p.snd
```

**Dificultad**: Alta  
**Tiempo estimado**: 4-6 horas  
**Prioridad**: 🔴 CRÍTICA (desbloquea 6 teoremas)

---

### FASE 4: Probar Teoremas de Reflexión 🎯

Una vez implementado `mirror`, estos teoremas siguen naturalmente:

#### 4.1 `dme_mirror`

**Teorema**:
```lean
theorem dme_mirror (K : K3Config) :
  K.mirror.dme = K.dme.map (· * (-1))
```

**Estrategia** (con `mirror` correcto):
1. Desplegar `dme`: es `pairsList.map (adjustDelta ∘ pairDelta)`
2. Para `mirror`, tenemos `pairsList` de pares invertidos
3. Probar: `pairDelta p.reverse = -pairDelta p`
   ```lean
   pairDelta p.reverse = p.fst - p.snd  (porque reverse intercambia)
                       = -(p.snd - p.fst)
                       = -pairDelta p
   ```
4. Probar: `adjustDelta (-δ) = -adjustDelta δ`
5. Concluir por composición

**Lemas necesarios**:
```lean
lemma pairDelta_reverse (p : OrderedPair) :
  pairDelta p.reverse = -pairDelta p

lemma adjustDelta_neg (δ : ℤ) :
  adjustDelta (-δ) = -adjustDelta δ
```

**Dificultad**: Media (con `mirror` implementado)  
**Tiempo estimado**: 1-2 horas

---

#### 4.2 `ime_mirror`

**Teorema**:
```lean
theorem ime_mirror (K : K3Config) :
  K.mirror.ime = K.ime
```

**Estrategia**:
1. Usar `dme_mirror`: `K.mirror.dme = K.dme.map (· * (-1))`
2. Aplicar `Int.natAbs`:
   ```lean
   K.mirror.ime = K.mirror.dme.map Int.natAbs
                = (K.dme.map (· * (-1))).map Int.natAbs
                = K.dme.map (Int.natAbs ∘ (· * (-1)))
                = K.dme.map Int.natAbs  (porque |-x| = |x|)
                = K.ime
   ```

**Lemas necesarios**:
```lean
lemma natAbs_neg (n : ℤ) : Int.natAbs (-n) = Int.natAbs n
```

**Dificultad**: Baja (depende de `dme_mirror`)  
**Tiempo estimado**: 30 min - 1 hora

---

#### 4.3 `gap_mirror`

**Teorema**:
```lean
theorem gap_mirror (K : K3Config) :
  K.mirror.gap = K.gap
```

**Estrategia**:
1. Trivial usando `ime_mirror`:
   ```lean
   K.mirror.gap = K.mirror.ime.foldl (· + ·) 0
                = K.ime.foldl (· + ·) 0  (por ime_mirror)
                = K.gap
   ```

**Dificultad**: Trivial (depende de `ime_mirror`)  
**Tiempo estimado**: 15 minutos

---

#### 4.4 `writhe_mirror`

**Teorema**:
```lean
theorem writhe_mirror (K : K3Config) :
  K.mirror.writhe = -K.writhe
```

**Estrategia**:
1. Usar `dme_mirror`
2. Probar que suma conmuta con negación:
   ```lean
   K.mirror.writhe = K.mirror.dme.foldl (· + ·) 0
                   = (K.dme.map (· * (-1))).foldl (· + ·) 0
                   = -(K.dme.foldl (· + ·) 0)
                   = -K.writhe
   ```

**Lemas necesarios**:
```lean
lemma foldl_sum_neg (l : List ℤ) :
  (l.map (· * (-1))).foldl (· + ·) 0 = -(l.foldl (· + ·) 0)
```

**Dificultad**: Media  
**Tiempo estimado**: 1-2 horas

---

#### 4.5 `mirror_involutive`

**Teorema**:
```lean
theorem mirror_involutive (K : K3Config) :
  K.mirror.mirror = K
```

**Estrategia**:
1. Con `mirror` implementado como `pairs.image reverse`
2. Usar `reverse_involutive`: `p.reverse.reverse = p`
3. Probar que `image reverse` aplicado dos veces da la identidad:
   ```lean
   (K.pairs.image reverse).image reverse = K.pairs
   ```

**Lemas necesarios**:
```lean
lemma image_image_involutive {α : Type*} [DecidableEq α] 
  (s : Finset α) (f : α → α) (hf : ∀ x, f (f x) = x) :
  (s.image f).image f = s
```

**Dificultad**: Media  
**Tiempo estimado**: 1-2 horas

---

#### 4.6 `nonzero_writhe_implies_chiral`

**Teorema**:
```lean
theorem nonzero_writhe_implies_chiral (K : K3Config) (h : K.writhe ≠ 0) :
  K ≠ K.mirror
```

**Estrategia**:
1. Prueba por contradicción
2. Suponer `K = K.mirror`
3. Entonces `K.writhe = K.mirror.writhe`
4. Por `writhe_mirror`: `K.mirror.writhe = -K.writhe`
5. Por tanto `K.writhe = -K.writhe`
6. Esto implica `2 * K.writhe = 0`, luego `K.writhe = 0`
7. Contradicción con hipótesis `h : K.writhe ≠ 0`

**Dificultad**: Baja (depende de `writhe_mirror`)  
**Tiempo estimado**: 30 minutos

---

## 📋 Plan de Acción Recomendado

### Semana 1: Lemas Fundamentales
**Objetivo**: Construir infraestructura de lemas auxiliares

```lean
-- archivo: TCN_01_Lemmas.lean

-- Lemas sobre listas
lemma map_length ...
lemma getElem_map ...
lemma sum_list_ge ...
lemma sum_list_le ...
lemma foldl_sum_neg ...

-- Lemas aritméticos
lemma int_abs_sign_decomp ...
lemma natAbs_pos_of_nonzero ...
lemma natAbs_le_of_bounded ...
lemma natAbs_neg ...

-- Lemas sobre adjustDelta
lemma adjustDelta_nonzero ...
lemma adjustDelta_bounded ...
lemma adjustDelta_neg ...

-- Lemas sobre OrderedPair
lemma pairDelta_reverse ...
```

**Tiempo estimado**: 8-12 horas

---

### Semana 2: Implementar Mirror
**Objetivo**: Implementación correcta de reflexión especular

```lean
-- Implementar mirror con todas las pruebas
def mirror (K : K3Config) : K3Config := ...

-- Lemas auxiliares
lemma card_image_involutive ...
lemma partition_reverse ...
lemma image_image_involutive ...
```

**Tiempo estimado**: 8-12 horas  
**Prioridad**: 🔴 CRÍTICA

---

### Semana 3: Completar Teoremas
**Objetivo**: Resolver todos los sorry

**Día 1-2**: Fase 2 (Análisis Estructural)
- `dme_decomposition` ✓
- `gap_ge_three` ✓
- `gap_le_nine` ✓

**Día 3-5**: Fase 4 (Teoremas de Reflexión)
- `dme_mirror` ✓
- `ime_mirror` ✓
- `gap_mirror` ✓
- `writhe_mirror` ✓
- `mirror_involutive` ✓
- `nonzero_writhe_implies_chiral` ✓

**Tiempo estimado**: 12-16 horas

---

## 🎓 Lecciones Aprendidas

### ✅ Buenas Prácticas
1. **Definiciones por reflexividad**: `ime_from_dme` y `gap_from_ime` se prueban con `rfl`
2. **Modularidad**: Separar lemas auxiliares facilita pruebas complejas
3. **Documentación**: Los comentarios "ESTRATEGIA" ayudan enormemente

### ⚠️ Errores a Evitar
1. **No implementar funciones completamente**: `mirror = K` bloquea 6 teoremas
2. **Saltar lemas auxiliares**: Intentar probar teoremas complejos sin lemas base
3. **No validar propiedades implícitas**: Como `validDME` que no está formalizado

### 🔮 Mejoras Futuras
1. **Formalizar `validDME`**: Convertir de `Bool` a `Prop` para usarlo en pruebas
2. **Instancia `Fintype K3Config`**: Permitiría contar configuraciones formalmente
3. **Implementar `fromNotation`**: Reconstrucción desde notación canónica
4. **Automatización**: Desarrollar tácticas personalizadas para teoremas similares

---

## 📊 Métricas de Progreso

```
Estado Inicial:  [##########] 10 sorry (100%)
Estado Actual:   [####------]  6 sorry (60%)
Estado Final:    [----------]  0 sorry (0%)

Progreso: 40% completado
Estimado: 28-40 horas para completar
```

---

## 🚀 Próximos Pasos Inmediatos

1. **HOY**: Revisar y validar las 3 pruebas completadas
2. **Esta semana**: Comenzar con lemas auxiliares (Semana 1 del plan)
3. **Próxima semana**: Implementar `mirror` correctamente
4. **En 2-3 semanas**: Bloque 1 completamente probado

---

## 📞 Notas para Consulta

### Si necesitas ayuda específica con:
- **Lemas sobre listas**: Buscar en `Mathlib.Data.List.Basic`
- **Aritmética de enteros**: Buscar en `Mathlib.Data.Int.Basic`
- **Finset.image**: Buscar en `Mathlib.Data.Finset.Image`
- **Funciones involutivas**: Buscar "involution" en Mathlib

### Recursos útiles:
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Zulip - Lean Community](https://leanprover.zulipchat.com/)

---

**Conclusión**: Con un plan sistemático y 28-40 horas de trabajo enfocado, 
el Bloque 1 puede estar completamente probado. La clave es implementar `mirror` 
correctamente, lo cual desbloqueará automáticamente 6 teoremas.

¡Adelante con la formalización! 🎯
