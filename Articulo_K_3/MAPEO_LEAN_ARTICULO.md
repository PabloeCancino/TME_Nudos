# Mapeo Artículo TMEN ↔ Código Lean

**Principio:** Código Lean = Fuente de Verdad  
**Objetivo:** Alinear 100% el artículo TMEN con el código verificado

---

## 1. Definiciones Fundamentales

### OrderedPair

**Código Lean** (TCN_01_Fundamentos.lean:50-56):
```lean
structure OrderedPair where
  fst : ZMod 6
  snd : ZMod 6
  distinct : fst ≠ snd
```

**Artículo TMEN:** ✅ ALINEADO
- Sección 1.2: "Pares ordenados $(o_i, u_i)$ con $o_i, u_i \in \mathbb{Z}_{2n}$ y $o_i \neq u_i$"
- Correspondencia: `fst` ↔ $o_i$, `snd` ↔ $u_i$

---

### K3Config

**Código Lean** (TCN_01_Fundamentos.lean:128-135):
```lean
structure K3Config where
  pairs : Finset OrderedPair
  card_eq : pairs.card = 3
  is_partition : ∀ i : ZMod 6, ∃! p ∈ pairs, i = p.fst ∨ i = p.snd
```

**Artículo TMEN:** ⚠️ REQUIERE ACTUALIZACIÓN
- Sección 2.1 (actual): Define configuración pero no especifica propiedad de unicidad
- **Acción:** Añadir axioma explícito de partición con cuantificador `∃!`

---

## 2. Axiomas vs. Código Lean

### Axioma A1: Espacio del Recorrido

**Artículo** (Sección 4, Axioma A1):
```
$$\mathbb{Z}_{2n}=\{1,2,\dots,2n\}$$
```

**Código Lean:**
```lean
ZMod 6 = {0, 1, 2, 3, 4, 5}
```

**Estado:** ❌ **CONFLICTO CRÍTICO**

**Acción requerida:** Actualizar A1 a:
```
$$\mathbb{Z}_{2n} = \{0, 1, \ldots, 2n-1\}$$
```

---

### Axioma A2: Existencia de Cruces

**Artículo** (Sección 4, Axioma A2):
```
Para cada $n$ existe un conjunto de cruces $C=\{c_1,\dots,c_n\}$, y para cada $c_i$ 
existe un par ordenado $(o_i,u_i)\in\mathbb{Z}_{2n}\times\mathbb{Z}_{2n}$
```

**Código Lean:** No hay axioma explícito - es una **construcción**

**Estado:** ⚠️ Formulación inadecuada

**Lean vs. Artículo:**
- Lean: **Construcción** (defines K3Config como estructura)
- Artículo: **Axioma** (postula existencia)

**Acción:** Reformular A2 como **Definición Constructiva** en lugar de axioma

---

### Axioma A3: Interlazado

**Artículo:** Define $a_i < a_j < b_i < b_j$ para interlazado

**Código Lean:** No tiene definición explícitade interlazado en TCN_01

**Estado:** ⚠️ El concepto existe pero NO está implementado formalmente para K₃

**Acción:** Marcar como **concepto auxiliar** no esencial para K₃ (clasificación usa D₆ en su lugar)

---

### Axioma A4: Equivalencia Isotópica

**Artículo:** $K \sim K'$ generada por R1, R2, R3

**Código Lean:**  
- `hasR1`, `hasR2` son **predicados** (TCN_02)
- Clasificación usa **órbitas bajo D₆** (TCN_05, TCN_07)

**Estado:** ⚠️ **DISCREPANCIA METODOLÓGICA**

**Lean vs. Artículo:**
- Lean: Clasificación por **acción de grupo D₆ + filtros R1/R2**
- Artículo: Equivalencia por **movimientos Reidemeister**

**Acción:** Añadir nota explicando que para K₃, la equivalencia vía Reidemeister es **equivalente** a órbitas D₆ módulo R1/R2

---

## 3. Sistema DME/IME

### adjustDelta

**Código Lean** (TCN_01:237-240):
```lean
def adjustDelta (δ : ℤ) : ℤ :=
  if δ > 3 then δ - 6
  else if δ < -3 then δ + 6
  else δ
```

**Artículo TMEN:** ✅ **ALINEADO** (Sección 6_DME_IME.md)

---

### dme

**Código Lean** (TCN_01:267-268):
```lean
noncomputable def dme (K : K3Config) : List ℤ :=
  K.pairsList.map (fun p => adjustDelta (pairDelta p))
```

**Artículo TMEN:** ✅ **ALINEADO** (Sección 6.1)

---

### ime

**Código Lean** (TCN_01:296-297):
```lean
noncomputable def ime (K : K3Config) : List ℕ :=
  K.dme.map Int.natAbs
```

**Artículo TMEN:** ✅ **ALINEADO** (Sección 6.2)

---

### gap

**Código Lean** (TCN_01:340-341):
```lean
noncomputable def gap (K : K3Config) : ℕ :=
  K.ime.foldl (· + ·) 0
```

**Artículo TMEN:** ✅ **ALINEADO** (Sección 6.4)

---

### writhe

**Código Lean** (TCN_01:370-371):
```lean
noncomputable def writhe (K : K3Config) : ℤ :=
  K.dme.foldl (· + ·) 0
```

**Artículo TMEN:** ✅ **ALINEADO** (Sección 6.5)

---

## 4. Teoremas Probados en Lean

### toMatching_card

**Código Lean** (TCN_01):
```lean
theorem toMatching_card (K : K3Config) : K.toMatching.card = 3
```

**Artículo:** ❌ **NO MENCIONADO**

**Acción:** Añadir como Teorema en sección de configuraciones

---

### ime_mirror

**Código Lean** (TCN_01):
```lean
theorem ime_mirror (K : K3Config) : K.mirror.ime = K.ime
```

**Artículo:** ✅ INCLUIDO como Teorema 6.3 en Sección 6_DME_IME.md

---

### k3_classification_strong

**Código Lean** (TCN_07:134-169):
```lean
theorem k3_classification_strong :
  ∀ K : K3Config, ¬hasR1 K → ¬hasR2 K →
    ∃! R, R ∈ {trefoilKnot, mirrorTrefoil} ∧ ∃ g : DihedralD6, g • K = R
```

**Artículo:** ❌ **NO EXISTE** (pendiente Sección 12)

**Acción:** Crear Sección 12: Clasificación K₃ con este teorema

---

## 5. Definiciones en Lean NO en Artículo

| Concepto Lean    | Ubicación      | Estado en Artículo                            |
| ---------------- | -------------- | --------------------------------------------- |
| `mirror`         | TCN_01:534-537 | ✅ Mencionado (D7)                             |
| `is_partition`   | TCN_01:133     | ⚠️ Implícito, no explícito                     |
| `toMatching`     | TCN_01         | ❌ No mencionado                               |
| `DihedralD6`     | TCN_04         | ⚠️ Mencionado vía $\mathcal{P}$, $\mathcal{I}$ |
| `trefoilKnot`    | TCN_06         | ✅ Usado en ejemplos                           |
| `hasR1`, `hasR2` | TCN_02         | ⚠️ Formulación diferente                       |

---

## 6. Acciones Prioritarias

### CRÍTICAS (Inconsistencias)

1. ❌ **Axioma A1:** Cambiar de $\{1, \ldots, 2n\}$ a $\{0, \ldots, 2n-1\}$
2. ❌ **Definición 2.1:** Añadir propiedad de unicidad (`∃!`)
3. ❌ **Reformular A2:** De axioma a definición constructiva

### ALTAS (Adiciones)

4. ⬜ **Sección 12:** Añadir clasificación K₃ con `k3_classification_strong`
5. ⬜ **Teorema toMatching_card:** Añadir a sección de configuraciones
6. ⬜ **Nota A4:** Explicar equivalencia Reidemeister ↔ órbitas D₆

### MEDIAS (Mejoras)

7. ⬜ **Tabla de correspondencias:** Crear referencia cruzada Artículo ↔ Lean
8. ⬜ **Ejemplos:** Verificar que todos usan valores de Lean (ej: trefoilKnot)
9. ⬜ **Referencias:** Añadir líneas específicas de código Lean

---

## 7. Plan de Ejecución

### Fase 1: Correcciones Críticas
1. Actualizar Axioma A1 en Fundamentos_TMEN_v3.0.md
2. Actualizar Definición 2.1 con unicidad
3. Reformular Axioma A2

### Fase 2: Adiciones
4. Crear Sección 12 (Clasificación K₃)
5. Añadir teorema toMatching_card
6. Añadir nota sobre equivalencia A4

### Fase 3: Documentación
7. Crear tabla de referencia cruzada completa
8. Verificar ejemplos contra Lean
9. Añadir líneas de código Lean como referencias

---

**Estado Actual: 70% alineado**  
**Meta: 100% alineado**  
**Tiempo estimado: 2-3 horas de revisión manual**
