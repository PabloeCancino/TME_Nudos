# **6. Sistema DME/IME: Descriptores Modulares Estructurales**

> **Fuente:** TCN_01_Fundamentos.lean (líneas 222-372)  
> **Estado:** Formalmente verificado en Lean 4

Esta sección establece el **sistema de descriptores modulares** que constituye la contribución fundamental de TMEN. Todas las definiciones provienen directamente del código Lean verificado.

---

## **6.1. Descriptor Modular Estructural (DME)**

### **Definición 6.1 (DME)**  

Para una configuración modular $K = \{(o_1, u_1), (o_2, u_2), (o_3, u_3)\}$ sobre $\mathbb{Z}_6$, el **Descriptor Modular Estructural** es el vector:

$$
\text{DME}(K) = (\delta_1, \delta_2, \delta_3)
$$

donde cada componente se calcula mediante:

$$
\delta_i = \text{adjust}(u_i - o_i)
$$

con $u_i - o_i$ calculado en aritmética entera.

### **Función de Ajuste**

La función $\text{adjust}: \mathbb{Z} \to [-3, 3]$ normaliza desplazamientos al rango canónico:

$$
\text{adjust}(\delta) = \begin{cases}
\delta - 6 & \text{si } \delta > 3 \\
\delta + 6 & \text{si } \delta < -3 \\
\delta & \text{si } -3 \leq \delta \leq 3
\end{cases}
$$

**Ejemplos de ajuste:**
- $\text{adjust}(5) = 5 - 6 = -1$
- $\text{adjust}(-5) = -5 + 6 = 1$
- $\text{adjust}(2) = 2$

### **Correspondencia con Lean**

```lean
-- TCN_01_Fundamentos.lean

/-- Calcula δᵢ = sᵢ - eᵢ en aritmética entera -/
def pairDelta (p : OrderedPair) : ℤ :=
  (p.snd.val : ℤ) - (p.fst.val : ℤ)

/-- Ajusta desplazamiento al rango [-3, 3] -/
def adjustDelta (δ : ℤ) : ℤ :=
  if δ > 3 then δ - 6
  else if δ < -3 then δ + 6
  else δ

/-- DME: Vector de desplazamientos direccionales -/
noncomputable def dme (K : K3Config) : List ℤ :=
  K.pairsList.map (fun p => adjustDelta (pairDelta p))
```

### **Propiedades del DME**

**Teorema 6.1 (Completitud).**  
El DME, junto con el vector de entradas $E$, codifica **completamente** una configuración K₃.

*Demostración:* Dadas $E = (e_1, e_2, e_3)$ y $\text{DME} = (\delta_1, \delta_2, \delta_3)$, podemos reconstruir:
$$
u_i = (e_i + \delta_i) \bmod 6
$$
Por tanto, $(E, \text{DME}) \leftrightarrow K$ es biyectiva. $\square$

**Teorema 6.2 (Rango de valores).**  
Para configuraciones K₃ válidas:
$$
\delta_i \in \{-3, -2, -1, 1, 2, 3\} \quad \text{(excluye 0)}
$$

*Demostración:* La condición de partición requiere $o_i \neq u_i$, por tanto $\delta_i \neq 0$. El rango $[-3, 3]$ viene del ajuste modular. $\square$

---

## **6.2. Invariante Modular Estructural (IME)**

### **Definición 6.2 (IME)**

El **Invariante Modular Estructural** se define como el valor absoluto del DME:

$$
\text{IME}(K) = |\text{DME}(K)| = (|\delta_1|, |\delta_2|, |\delta_3|)
$$

### **Correspondencia con Lean**

```lean
/-- IME: Magnitudes sin signos -/
noncomputable def ime (K : K3Config) : List ℕ :=
  K.dme.map Int.natAbs
```

### **Teorema 6.3 (IME es invariante aquiral)**

Para toda configuración $K$:
$$
\text{IME}(K^*) = \text{IME}(K)
$$
donde $K^*$ denota la reflexión especular.

*Demostración:* 
- Reflexión invierte pares: $(o_i, u_i) \mapsto (u_i, o_i)$
- Por tanto: $\delta_i(K^*) = o_i - u_i = -(u_i - o_i) = -\delta_i(K)$
- Aplicando valor absoluto: $|\delta_i(K^*)| = |-\delta_i(K)| = |\delta_i(K)|$ $\square$

> **Verificación en Lean:** Este teorema está probado como `ime_mirror` en TCN_01_Fundamentos.lean

### **Rol del IME**

IME permite clasificar nudos **sin considerar quiralidad**:
- Nudos espejos tienen **mismo IME**
- Útil para agrupar familias topológicas
- Base para invariantes aquirales

---

## **6.3. Vector de Signos Quirales**

### **Definición 6.3 (Signos Quirales)**

$$
\sigma(K) = (\text{sgn}(\delta_1), \text{sgn}(\delta_2), \text{sgn}(\delta_3))
$$

donde $\text{sgn}(x) = +1$ si $x > 0$, $\text{sgn}(x) = -1$ si $x < 0$.

###  **Correspondencia con Lean**

```lean
/-- Vector de signos quirales -/
noncomputable def chiralSigns (K : K3Config) : List ℤ :=
  K.dme.map Int.sign
```

### **Teorema 6.4 (Descomposición DME)**

El DME se puede  reconstruir desde IME y signos:
$$
\text{DME} = \text{IME} \odot \sigma
$$
donde $\odot$ denota producto componente a componente.

---

## **6.4. Gap: Complejidad Total**

### **Definición 6.4 (Gap)**

El **Gap** mide la complejidad estructural acumulada:

$$
\text{Gap}(K) = \sum_{i=1}^{3} |\delta_i| = \sum_{i=1}^{3} \text{IME}_i
$$

### **Correspondencia con Lean**

```lean
/-- Gap: Complejidad estructural acumulada -/
noncomputable def gap (K : K3Config) : ℕ :=
  K.ime.foldl (· + ·) 0
```

### **Propiedades del Gap**

**Teorema 6.5 (Rango del Gap).**  
Para configuraciones K₃:
$$
\text{Gap}(K) \in \{3, 4, 5, 6, 7, 8, 9\}
$$

*Demostración:*
- Mínimo: $\delta_i = \pm 1$ para todo $i$ → Gap = 3
- Máximo: $\delta_i = \pm 3$ para todo $i$ → Gap = 9
- Valores intermedios son alcanzables. $\square$

**Teorema 6.6 (Gap es invariante aquiral).**
$$
\text{Gap}(K^*) = \text{Gap}(K)
$$

*Demostración:* Como IME es invariante y Gap = Σ IME, el resultado es inmediato. $\square$

### **Interpretación**

El Gap mide la "separación total" entre entradas y salidas:
- **Gap = 3**: Cruces locales (δᵢ = ±1), mínima complejidad
- **Gap = 9**: Cruces máximamente separados (δᵢ = ±3), máxima complejidad

---

## **6.5. Writhe: Suma Algebraica**

### **Definición 6.5 (Writhe)**

El **writhe** es la suma algebraica con signo:

$$
\text{Writhe}(K) = \sum_{i=1}^{3} \delta_i
$$

### **Correspondencia con Lean**

```lean
/-- Writhe: Suma algebraica de desplazamientos -/
noncomputable def writhe (K : K3Config) : ℤ :=
  K.dme.foldl (· + ·) 0
```

### **Teorema 6.7 (Writhe bajo reflexión)**

$$
\text{Writhe}(K^*) = -\text{Writhe}(K)
$$

*Demostración:* Como $\delta_i(K^*) = -\delta_i(K)$:
$$
\text{Writhe}(K^*) = \sum -\delta_i(K) = -\sum \delta_i(K) = -\text{Writhe}(K) \quad \square
$$

### **Teorema 6.8 (Test de quiralidad)**

Si $\text{Writhe}(K) \neq 0$, entonces $K$ es quiral.

*Demostración:* Si $K$ fuera aquiral, existiría transformación $g \in D_6$ tal que $g \cdot K = K^*$. Pero writhe es invariante bajo $D_6$ y anti-invariante bajo reflexión, contradicción. $\square$

> **Nota:** La recíproca NO es cierta: Writhe = 0 es condición necesaria pero no suficiente para aquiralidad.

### **Interpretación**

- **Writhe > 0**: Predominan giros positivos (trébol izquierdo)
- **Writhe < 0**: Predominan giros negativos (trébol derecho)
- **Writhe = 0**: Giros balanceados (posible aquiralidad)

---

## **6.6. Ejemplo Completo: Nudo Trébol**

### **Trébol Derecho**

**Configuración:** $K_{\text{trefoil}} = \{(1,4), (5,2), (3,0)\}$

**Cálculo del DME:**
- $\delta_1 = \text{adjust}(4-1) = \text{adjust}(3) = 3$
- $\delta_2 = \text{adjust}(2-5) = \text{adjust}(-3) = -3$
- $\delta_3 = \text{adjust}(0-3) = \text{adjust}(-3) = -3$

**Resultado:** $\text{DME}(K_{\text{trefoil}}) = (3, -3, -3)$

**Invariantes derivados:**
- $\text{IME} = (3, 3, 3)$
- $\sigma = (+1, -1, -1)$
- $\text{Gap} = 9$ (máximo)
- $\text{Writhe} = 3 + (-3) + (-3) = -3$ (quiral)

### **Trébol Izquierdo (Espejo)**

**Configuración:** $K^* = \{(4,1), (2,5), (0,3)\}$

**DME:** $(−3, 3, 3)$  
**IME:** $(3, 3, 3)$ [mismo que el derecho ✓]  
**Writhe:** $+3$ [opuesto al derecho ✓]

---

## **6.7. Resumen del Sistema DME/IME**

| Descriptor | Definición                       | Rango (K₃)                            | Invariancia |
| ---------- | -------------------------------- | ------------------------------------- | ----------- |
| **DME**    | $(\delta_1, \delta_2, \delta_3)$ | $\{-3,\ldots,3\}^3 \setminus \{0\}^3$ | Primario    |
| **IME**    | $\|\text{DME}\|$                 | $\{1,2,3\}^3$                         | Aquiral     |
| **σ**      | $\text{sgn}(\text{DME})$         | $\{\pm 1\}^3$                         | Quiral      |
| **Gap**    | $\sum \|\delta_i\|$              | $\{3,\ldots,9\}$                      | Aquiral     |
| **Writhe** | $\sum \delta_i$                  | $[-9, 9]$                             | Quiral      |

### **Relaciones Fundamentales**

1. $\text{DME} = \text{IME} \odot \sigma$ (descomposición completa)
2. $\text{Gap} = \sum \text{IME}$ (complejidad escalar)
3. $\text{Writhe} = \sum \text{DME}$ (quiralidad escalar)
4. $K \stackrel{D_6}{\sim} K' \Rightarrow \text{DME}(K) = \text{DME}(K')$ módulo permutación

### **Jerarquía de Invariantes**

```
DME (descriptor primario)
 ├─> IME (invariante topológico aquiral)
 │    └─> Gap (escalar aquiral)
 └─> σ (vector quiral)
      └─> Writhe (escalar quiral)
```

---

## **6.8. Verificación Formal en Lean**

Todos los conceptos de esta sección están formalmente verificados en:

**Archivo:** `TMENudos/TCN_01_Fundamentos.lean`  
**Líneas:** 222-460  
**Estado:** ✅ Compilación exitosa (0 sorry en definiciones principales)

**Teoremas clave probados:**
- `adjustDelta_bounded`: Mantiene valores en $[-3, 3]$
- `adjustDelta_nonzero_of_distinct`: Nunca produce 0 para pares válidos
- `ime_mirror`: IME es invariante bajo reflexión
- `mirror` es involutiva: $(K^*)^* = K$

---

**Fin de Sección 6**

> **Nota metodológica:** Esta sección documenta fielmente el código Lean verificado.  
> Cualquier discrepancia con otras fuentes se resuelve a favor del código Lean.
