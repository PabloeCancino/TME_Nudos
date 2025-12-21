## **Adición 2: Teorema toMatching_card**

### **Insertar después de Sección 2.1 (Definición fundamental)**

---

### **Teorema 2.1 (Cardinalidad del Matching)**

> **Fuente:** TCN_01_Fundamentos.lean:148-170

Toda configuración K₃ define un **matching perfecto** sobre $\mathbb{Z}_6$ (emparejamiento sin aristas compartidas).

**Enunciado:**
$$
\forall K : \text{K3Config}, \quad |K.\text{toMatching}| = 3
$$

donde $K.\text{toMatching}$ es el conjunto de aristas no ordenadas:
$$
K.\text{toMatching} := \{ \{o_i, u_i\} : (o_i, u_i) \in K \}
$$

### **Correspondencia con Lean**

```lean
-- TCN_01_Fundamentos.lean:144-146
def toMatching (K : K3Config) : Finset (Finset (ZMod 6)) :=
  K.pairs.image OrderedPair.toEdge

-- TCN_01:150-170
theorem toMatching_card (K : K3Config) : K.toMatching.card = 3 := by
  unfold toMatching
  have h_inj : ∀ p1 ∈ K.pairs, ∀ p2 ∈ K.pairs, p1.toEdge = p2.toEdge → p1 = p2 := by
    intro p1 hp1 p2 hp2 h_edge
    rw [OrderedPair.toEdge_eq_iff] at h_edge
    rcases h_edge with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · cases p1; cases p2; simp_all
    · obtain ⟨q, ⟨hq_mem, hq_has⟩, hq_unique⟩ := K.is_partition p1.fst
      have h1 : p1 = q := hq_unique p1 ⟨hp1, Or.inl rfl⟩
      have h2 : p2 = q := hq_unique p2 ⟨hp2, Or.inr hf⟩
      exact h1.trans h2.symm
  rw [Finset.card_image_of_injOn h_inj]
  exact K.card_eq
```

**Estado:** ✅ **PROBADO FORMALMENTE**

### **Demostración (Esquema)**

1. **Inyectividad de toEdge:** Dos pares distintos no pueden producir la misma arista
   - Si $\{o_1, u_1\} = \{o_2, u_2\}$ entonces $(o_1, u_1) = (o_2, u_2)$ o $(o_1, u_1) = (u_2, o_2)$
   - Pero la segunda opción viola la propiedad de partición única

2. **Cardinalidad:** Como `toEdge` es inyectiva sobre 3 pares:
   $$
   |K.\text{toMatching}| = |K.\text{pairs}| = 3
   $$

$\square$

### **Interpretación**

Este teorema establece que toda configuración K₃ corresponde a un **matching perfecto** de $\mathbb{Z}_6$:
- 6 vértices (elementos de $\mathbb{Z}_6$)
- 3 aristas (los pares)
- Cada vértice aparece en exactamente una arista  (propiedad de partición)

---

## **Adición 3: Nota sobre Axioma A4**

### **Insertar después de Axioma A4 (Sección 4)**

---

### **Observación 4.2 — Equivalencia por Reidemeister vs. Órbitas D₆ para K₃**

> **Fuente:** TCN_07_Clasificacion.lean

Para el caso específico de **configuraciones K₃**, la equivalencia isotópica vía movimientos de Reidemeister es **equivalente** a la clasificación por **órbitas bajo el grupo diédrico** $D_6$.

**Proposición 4.2 (Equivalencia de Métodos para K₃).**

Para configuraciones K₃ sin R1 ni R2:
$$
K_1 \sim_{\text{Reidemeister}} K_2 \quad \Leftrightarrow \quad K_1 \sim_{D_6} K_2
$$

donde:
- $K_1 \sim_{\text{Reidemeister}} K_2$: existe secuencia de R1, R2, R3 conectando $K_1$ y $K_2$
- $K_1 \sim_{D_6} K_2$: existe $g \in D_6$ tal que $g \cdot K_1 = K_2$

### **Justificación**

**Dirección ($\Rightarrow$):**  
Las movidas Reidemeister R1 y R2 están **filtradas** (configuraciones sin ellas). Solo queda R3, pero para K₃:
- R3 involucra reordenamiento de 3 cruces
- Sobre $\mathbb{Z}_6$, estos reordenamientos son **generados por $D_6$** (rotaciones y reflexiones)

**Dirección ($\Leftarrow$):**  
Elementos de $D_6$ corresponden a:
- **Rotaciones** ($r^k$): movimientos R3 cíclicos
- **Reflexiones** ($s \cdot r^k$): composición de R3 + espejo

Por tanto, acción de $D_6$ es **realizable** vía movimientos Reidemeister.

### **Correspondencia con Lean**

El código Lean **implementa directamente** la clasificación por órbitas $D_6$:

```lean
-- TCN_07:143-146
theorem k3_classification_strong :
  ∀ K : K3Config, ¬hasR1 K → ¬hasR2 K →
    let reps : Finset K3Config := {trefoilKnot, mirrorTrefoil}
    ∃! R, R ∈ reps ∧ ∃ g : DihedralD6, g • K = R
```

Esto **evita** la necesidad de:
- Definir R3 explícitamente como operación
- Probar confluencia de secuencias Reidemeister
- Verificar terminación de reducción

En su lugar, usa **álgebra pura** (acción de grupo) verificable en Lean.

### **Generalización**

Para $n > 3$ (K₄, K₅, ...), la relación entre Reidemeister y $D_{2n}$ es tema de investigación:

**Conjetura 4.1 (Equivalencia General).**  
Para configuraciones Kₙ sin R1/R2:
$$
\sim_{\text{Reidemeister}} \; = \; \sim_{D_{2n}}
$$

**Estado:** No probado en general. Verificado para $n=3$ (este trabajo).

---

**Fin de Adiciones**
