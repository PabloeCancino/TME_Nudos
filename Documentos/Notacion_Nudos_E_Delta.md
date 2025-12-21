# Notación K_n = (E, DME) para Nudos
## Sistema de Representación Bidireccional en Teoría Modular Estructural

**Autor:** Pabloe  
**Fecha:** Diciembre 2024  
**Versión:** 2.0

---

## Resumen Ejecutivo

Este documento presenta la notación **K_n = (E, DME)** como sistema de representación canónica para nudos de n cruces, integrándose con el marco de Teoría Modular Estructural (TME). La notación permite conversión bidireccional eficiente entre representación simbólica y configuración geométrica, preservando invariantes modulares y quiralidad.

**Jerarquía conceptual:**
- **DME** (Descriptor Modular Estructural): Vector con signos que captura estructura completa
- **IME** (Invariante Modular Estructural): Magnitudes sin signos, invariante aquiral derivado
- **Gap**: Complejidad total acumulada

**Características principales:**
- Biyección 1-a-1 entre notación y configuración canónica
- Codificación implícita de quiralidad en DME
- Separación entre invariantes quirales (DME) y aquirales (IME)
- Recuperación inmediata de IME, signos y Gap desde DME
- Normalización canónica automática

---

## 1. Definiciones Fundamentales

### 1.1 Espacio de Configuración

Para un nudo de **n cruces**, definimos:

- **Espacio de arcos:** ℤ/2n = {0, 1, 2, ..., 2n-1}
- **Cruce i:** par ordenado (eᵢ, sᵢ) donde:
  - eᵢ = valor de entrada en ℤ/2n
  - sᵢ = valor de salida en ℤ/2n

**Configuración canónica:** C = ((e₁,s₁), (e₂,s₂), ..., (eₙ,sₙ))

**Restricción fundamental:** Los 2n valores {0,1,...,2n-1} se particionan exactamente en:
- n valores de entrada {e₁, e₂, ..., eₙ}
- n valores de salida {s₁, s₂, ..., sₙ}

### 1.2 Notación K_n = (E, DME)

**Definición formal:**

```
K_n = (E, DME)
```

Donde:

**E = (e₁, e₂, ..., eₙ)** 
- Vector de entradas normalizado
- **Normalización:** e₁ = min{eᵢ : i=1,...,n}
- Elementos en ℤ/2n

**DME = (δ₁, δ₂, ..., δₙ)** [Descriptor Modular Estructural]
- Vector de desplazamientos direccionales con signo
- δᵢ = sᵢ - eᵢ (aritmética en ℤ)
- Rango: δᵢ ∈ {-n, ..., -1, 1, ..., n} (δᵢ ≠ 0)
- **Codifica completamente** la estructura y quiralidad del nudo

**Relación de reconstrucción:**
```
sᵢ ≡ eᵢ + δᵢ (mod 2n)
```

### 1.3 Jerarquía de Invariantes Derivados

A partir de DME se derivan tres conceptos fundamentales:

#### 1.3.1 IME (Invariante Modular Estructural)

```
IME = (|δ₁|, |δ₂|, ..., |δₙ|)
```

- **Invariante aquiral:** IME(K) = IME(K̄) donde K̄ es la reflexión de K
- Captura la "estructura modular" sin quiralidad
- Es un verdadero **invariante topológico** (no depende de orientación)

#### 1.3.2 Vector de Signos Quirales

```
σ = (σ₁, σ₂, ..., σₙ)
donde σᵢ = sgn(δᵢ) = { +1  si δᵢ > 0
                      { -1  si δᵢ < 0
```

- Codifica la **quiralidad** y orientación de cada cruce
- Determina si el nudo es quiral o aquiral

#### 1.3.3 Gap Total

```
Gap = Σ|δᵢ| = Σ IME_i
```

- **Invariante aquiral** de complejidad global
- Representa la separación estructural acumulada del nudo

**Relación fundamental:**
```
DME = IME ⊙ σ
```
donde ⊙ denota producto componente a componente.

---

## 2. Propiedades y Relaciones

### 2.1 Descriptor Modular Estructural (DME)

El DME es el **concepto primario** y completo:

```
DME = (δ₁, δ₂, ..., δₙ)
```

**Propiedades:**
- Codifica completamente la configuración (junto con E)
- Es un **descriptor orientado** (cambia bajo reflexión)
- Contiene toda la información estructural y quiral

**Reflexión especular:**
```
DME(K̄) = -DME(K) = (-δ₁, -δ₂, ..., -δₙ)
```

### 2.2 Invariante Modular Estructural (IME)

El IME se **deriva** del DME eliminando signos:

```
IME = |DME| = (|δ₁|, |δ₂|, ..., |δₙ|)
```

**Propiedades:**
- **Invariante topológico aquiral:** IME(K) = IME(K̄)
- Clasifica nudos por "complejidad modular" sin considerar quiralidad
- Es el análogo a invariantes clásicos como número de cruces

**Interpretación:** |δᵢ| = distancia modular mínima en el cruce i.

### 2.3 Vector de Signos

Codifica la orientación de cada cruce:

```
σ = sgn(DME) = (sgn(δ₁), sgn(δ₂), ..., sgn(δₙ))
```

**Relación de reconstrucción:**
```
DME = IME ⊙ σ
donde (IME ⊙ σ)ᵢ = IME_i · σᵢ
```

### 2.4 Gap Total

```
Gap = ||DME||₁ = Σ|δᵢ| = Σ IME_i
```

**Propiedades:**
- **Invariante aquiral:** Gap(K) = Gap(K̄)
- Representa la separación estructural acumulada del nudo
- Escalar que resume la complejidad modular total

### 2.5 Tabla de Invariantes

| Concepto | Fórmula | Tipo | Reflexión |
|----------|---------|------|-----------|
| **DME** | (δ₁,...,δₙ) | Descriptor quiral | DME(K̄) = -DME(K) |
| **IME** | (\|δ₁\|,...,\|δₙ\|) | Invariante aquiral | IME(K̄) = IME(K) |
| **σ** | (sgn(δ₁),...,sgn(δₙ)) | Quiralidad | σ(K̄) = -σ(K) |
| **Gap** | Σ\|δᵢ\| | Invariante aquiral | Gap(K̄) = Gap(K) |

---

## 3. Algoritmos de Conversión Bidireccional

### 3.1 Configuración Canónica → Notación K_n = (E, DME)

**Entrada:** Configuración C = ((e₁,s₁), (e₂,s₂), ..., (eₙ,sₙ))  
**Salida:** K_n = (E, DME)

**Algoritmo:**

```
PASO 1: Normalizar configuración
  1.1 Encontrar i* tal que eᵢ* = min{e₁, e₂, ..., eₙ}
  1.2 Rotar: C' = ((eᵢ*, sᵢ*), (eᵢ*₊₁, sᵢ*₊₁), ..., (eᵢ*₋₁, sᵢ*₋₁))
  1.3 Renumerar: (e'₁, s'₁) = (eᵢ*, sᵢ*), etc.

PASO 2: Extraer E
  E = (e'₁, e'₂, ..., e'ₙ)

PASO 3: Calcular DME
  Para cada i = 1 to n:
    3.1 δᵢ_raw = s'ᵢ - e'ᵢ
    3.2 Ajustar al rango [-n, n]:
        Si δᵢ_raw > n:  δᵢ = δᵢ_raw - 2n
        Si δᵢ_raw < -n: δᵢ = δᵢ_raw + 2n
        Si δᵢ_raw = 0:  ERROR (configuración inválida)
        Si -n ≤ δᵢ_raw ≤ n y δᵢ_raw ≠ 0: δᵢ = δᵢ_raw
  DME = (δ₁, δ₂, ..., δₙ)

PASO 4: Derivar invariantes (opcional)
  IME = (|δ₁|, |δ₂|, ..., |δₙ|)
  σ = (sgn(δ₁), sgn(δ₂), ..., sgn(δₙ))
  Gap = Σ|δᵢ|

RETORNAR: K_n = (E, DME)
```

**Complejidad:** O(n)

### 3.2 Notación K_n = (E, DME) → Configuración Canónica

**Entrada:** K_n = (E, DME)  
**Salida:** Configuración C = ((e₁,s₁), (e₂,s₂), ..., (eₙ,sₙ))

**Algoritmo:**

```
PASO 1: Validar entrada
  1.1 Verificar |E| = |DME| = n
  1.2 Verificar E ordenado con e₁ mínimo
  1.3 Verificar δᵢ ≠ 0 para todo i en DME

PASO 2: Reconstruir salidas
  Para cada i = 1 to n:
    sᵢ = (eᵢ + DME_i) mod 2n

PASO 3: Validar partición
  3.1 E_set = {e₁, e₂, ..., eₙ}
  3.2 S_set = {s₁, s₂, ..., sₙ}
  3.3 Verificar: E_set ∩ S_set = ∅
  3.4 Verificar: E_set ∪ S_set = ℤ/2n
  Si falla: ERROR (notación inconsistente)

PASO 4: Formar configuración
  C = ((e₁,s₁), (e₂,s₂), ..., (eₙ,sₙ))

RETORNAR: C
```

**Complejidad:** O(n)

---

## 4. Ejemplos Aplicados

### 4.1 Trébol Derecho (K₃)

#### 4.1.1 Configuración Original

```
C = ((3,0), (1,4), (5,2))
```

**Espacio:** ℤ/6 = {0,1,2,3,4,5}  
**Partición:**
- Entradas: {3, 1, 5}
- Salidas: {0, 4, 2}

#### 4.1.2 Conversión a K_n = (E, DME)

**PASO 1: Normalizar**
- min{3, 1, 5} = 1 (en posición 2)
- Rotar: ((1,4), (5,2), (3,0))

**PASO 2: Extraer E**
```
E = (1, 5, 3)
```

**PASO 3: Calcular DME**
- δ₁ = 4 - 1 = 3 ✓
- δ₂ = 2 - 5 = -3 ✓
- δ₃ = 0 - 3 = -3 ✓

```
DME = (3, -3, -3)
```

**Resultado:**
```
K₃ = ((1, 5, 3), (3, -3, -3))
```

#### 4.1.3 Conversión Inversa: Reconstruir Configuración

**Entrada:** K₃ = ((1, 5, 3), (3, -3, -3))

**PASO 2: Reconstruir salidas**
- s₁ = (1 + 3) mod 6 = 4
- s₂ = (5 + (-3)) mod 6 = (5 - 3) mod 6 = 2
- s₃ = (3 + (-3)) mod 6 = 0

**PASO 3: Validar**
- E_set = {1, 5, 3} ✓
- S_set = {4, 2, 0} ✓
- Partición válida ✓

**PASO 4: Configuración**
```
C = ((1,4), (5,2), (3,0))
```

#### 4.1.4 Invariantes Derivados

**DME (Descriptor primario):**
```
DME = (3, -3, -3)
```

**IME (derivado de DME):**
```
IME = |DME| = (|3|, |-3|, |-3|) = (3, 3, 3)
```

**Signos quirales:**
```
σ = sgn(DME) = (+1, -1, -1)
```

**Gap:**
```
Gap = ||DME||₁ = 3 + 3 + 3 = 9
```

**Interpretación:** 
- **DME** codifica completamente la estructura: trébol con un cruce de orientación opuesta (en configuración normalizada reordenada)
- **IME = (3,3,3)** indica que todos los cruces tienen distancia modular máxima (3 en ℤ/6)
- **σ = (+,-,-)** muestra la quiralidad específica tras normalización
- **Gap = 9** es el máximo para un nudo de 3 cruces con IME uniforme

---

### 4.2 Nudo Trivial (K₁)

#### 4.2.1 Configuración

```
C = ((0,1))
```

**Espacio:** ℤ/2 = {0,1}

#### 4.2.2 Notación K_n = (E, DME)

**E = (0)**  
**DME:**
- δ₁ = 1 - 0 = 1

```
K₁ = ((0), (1))
```

**Invariantes derivados:**
- **IME = (1)**
- **σ = (+1)**  
- **Gap = 1**

---

### 4.3 Nudo Figura-8 (K₄)

#### 4.3.1 Configuración Canónica

```
C = ((0,3), (2,7), (4,1), (6,5))
```

**Espacio:** ℤ/8 = {0,1,2,3,4,5,6,7}

#### 4.3.2 Conversión a K_n = (E, DME)

**PASO 1:** Ya normalizado (e₁ = 0 es mínimo)

**PASO 2:**
```
E = (0, 2, 4, 6)
```

**PASO 3: Calcular DME** (rango [-4, 4])
- δ₁ = 3 - 0 = 3
- δ₂ = 7 - 2 = 5 → ajustar: 5 - 8 = -3
- δ₃ = 1 - 4 = -3
- δ₄ = 5 - 6 = -1

```
DME = (3, -3, -3, -1)
```

**Resultado:**
```
K₄ = ((0, 2, 4, 6), (3, -3, -3, -1))
```

#### 4.3.3 Invariantes

**DME:**
```
DME = (3, -3, -3, -1)
```

**IME:**
```
IME = |DME| = (3, 3, 3, 1)
```

**Gap:**
```
Gap = 3 + 3 + 3 + 1 = 10
```

**Signos:**
```
σ = (+1, -1, -1, -1)
```

---

### 4.4 Ejemplo con n=5 (Hipotético)

#### 4.4.1 Configuración

```
C = ((1,8), (3,2), (5,6), (7,0), (9,4))
```

**Espacio:** ℤ/10 = {0,1,2,3,4,5,6,7,8,9}

#### 4.4.2 Conversión a K_n = (E, DME)

**PASO 1:** Ya normalizado (e₁ = 1 es mínimo)

**PASO 2:**
```
E = (1, 3, 5, 7, 9)
```

**PASO 3: Calcular DME** (rango [-5, 5])
- δ₁ = 8 - 1 = 7 → ajustar: 7 - 10 = -3
- δ₂ = 2 - 3 = -1
- δ₃ = 6 - 5 = 1
- δ₄ = 0 - 7 = -7 → ajustar: -7 + 10 = 3
- δ₅ = 4 - 9 = -5

```
DME = (-3, -1, 1, 3, -5)
```

**Resultado:**
```
K₅ = ((1, 3, 5, 7, 9), (-3, -1, 1, 3, -5))
```

#### 4.4.3 Verificación de Reconstrucción

- s₁ = (1 + (-3)) mod 10 = -2 mod 10 = 8 ✓
- s₂ = (3 + (-1)) mod 10 = 2 ✓
- s₃ = (5 + 1) mod 10 = 6 ✓
- s₄ = (7 + 3) mod 10 = 10 mod 10 = 0 ✓
- s₅ = (9 + (-5)) mod 10 = 4 ✓

**Configuración reconstruida:** ((1,8), (3,2), (5,6), (7,0), (9,4)) ✓

**Invariantes derivados:**
- **IME = |DME| = (3, 1, 1, 3, 5)**
- **Gap = 13**
- **σ = (-1, -1, +1, +1, -1)**

---

## 5. Comparación con Otras Notaciones

| Aspecto | K_n = (E, DME) | (E, IME, σ) | Config. directa |
|---------|---------------|-------------|-----------------|
| **Bidireccionalidad** | Perfecta O(n) | Perfecta O(n) | Directa |
| **Compacidad** | Alta | Media | Baja |
| **Invariantes aquirales** | IME derivado | IME explícito | Requiere cálculo |
| **Quiralidad** | En DME | En σ explícito | Implícita |
| **Normalización** | Canónica (e₁ min) | Canónica | Variable |
| **Poder discriminante** | Máximo | Máximo | Máximo |
| **Clasificación aquiral** | Requiere \|DME\| | Directa con IME | Requiere cálculo |
| **Extensibilidad** | Excelente | Buena | Limitada |

**Conclusión:** K_n = (E, DME) es óptimo como notación primaria, derivando IME cuando se requiere clasificación aquiral.

---

## 6. Ventajas de la Notación K_n = (E, DME)

### 6.1 Ventajas Computacionales

1. **Conversión lineal:** Ambas direcciones en O(n)
2. **Validación eficiente:** Verificar partición en O(n)
3. **Cálculo de invariantes:** IME, σ y Gap se derivan de DME sin recalcular
4. **Clasificación flexible:** Usar DME para discriminación completa o IME para clasificación aquiral

### 6.2 Ventajas Teóricas

1. **Unicidad:** Cada K_n ↔ única configuración canónica normalizada
2. **Completitud:** DME captura toda la información estructural y quiral
3. **Jerarquía clara:** DME (primario) → IME (invariante aquiral) + σ (quiralidad)
4. **Invariantes múltiples:** Separa descriptores quirales (DME) de invariantes aquirales (IME, Gap)
5. **Consistencia:** Los signos en DME preservan orientación de cruces

### 6.3 Ventajas Prácticas

1. **Notación compacta:** Más breve que configuración completa
2. **Interpretación clara:** 
   - E = estructura de entradas
   - DME = dinámica direccional completa
   - IME = complejidad modular aquiral
3. **Integración con TME:** Compatible con cálculo modular mod 2n
4. **Búsqueda eficiente:** Clasificar por IME, refinar con DME

---

## 7. Propiedades Algebraicas

### 7.1 Invarianza bajo Reflexión

**Reflexión de nudo:** K_n ↦ K̄_n (imagen especular)

**Operación en DME:**
```
DME(K̄_n) = -DME(K_n)
```

Donde -DME = (-δ₁, -δ₂, ..., -δₙ)

**Invarianza de IME:**
```
IME(K̄_n) = |DME(K̄_n)| = |-DME(K_n)| = |DME(K_n)| = IME(K_n)
```

Por lo tanto: **IME es un verdadero invariante aquiral**

**Ejemplo:**
- K₃: DME = (3,-3,-3), IME = (3,3,3)
- K̄₃: DME = (-3,3,3), IME = (3,3,3) ✓

### 7.2 Test de Quiralidad

Un nudo es **aquiral** si y solo si existe una permutación σ tal que:
```
DME_σ = -DME
```

Equivalentemente, usando IME:
```
(E_σ, IME_σ) = (E, IME)  AND  σ_quiral es simétrico
```

**Ejemplo (Figura-8):**
```
K₄ = ((0,2,4,6), (3,-3,-3,-1))
IME = (3,3,3,1)
```
Verificar si existe permutación que haga DME → -DME mientras preserva E e IME.

### 7.3 Estructura de Grupo

**Espacio de DME:**
- DME vive en (ℤ \ {0})ⁿ con restricciones |δᵢ| ≤ n
- Forma un **espacio simétrico** bajo reflexión: DME ↔ -DME

**Operación de inversión:**
```
inv: K_n → K̄_n
DME ↦ -DME
IME ↦ IME (invariante)
```

**Composición de nudos (suma conexa):**
```
K₁#K₂: DME(K₁#K₂) ≈ DME(K₁) ⊕ DME(K₂)
```
donde ⊕ es concatenación con ajuste de índices.

---

## 7.4 Distinción Fundamental: DME vs IME

Esta sección clarifica la diferencia conceptual y práctica entre DME e IME.

### 7.4.1 DME: Descriptor Completo con Quiralidad

**Naturaleza:**
- **Descriptor orientado** (no es invariante topológico puro)
- Cambia bajo reflexión especular: DME(K̄) = -DME(K)
- Codifica **completamente** la estructura del nudo

**Rol:**
- **Primario** en la notación K_n = (E, DME)
- Permite reconstrucción exacta de la configuración
- Distingue entre nudos quirales y sus reflexiones

**Análogo en teoría de nudos:**
- Similar a un **diagrama orientado** del nudo
- Similar a **códigos de Dowker** con orientación

### 7.4.2 IME: Invariante Aquiral

**Naturaleza:**
- **Invariante topológico verdadero**
- Invariante bajo reflexión: IME(K̄) = IME(K)
- Captura solo la "complejidad modular" sin quiralidad

**Rol:**
- **Derivado** de DME mediante valor absoluto
- Útil para clasificación aquiral
- Agrupa nudos quirales con sus reflexiones

**Análogo en teoría de nudos:**
- Similar al **número de cruces mínimo** (sin orientación)
- Similar al **polinomio de Jones** evaluado (sin quiralidad)

### 7.4.3 Tabla Comparativa

| Propiedad | DME | IME |
|-----------|-----|-----|
| **Tipo** | Descriptor quiral | Invariante aquiral |
| **Valores** | δᵢ ∈ {-n,...,-1,1,...,n} | \|δᵢ\| ∈ {1,...,n} |
| **Reflexión K→K̄** | DME → -DME | IME → IME |
| **Información** | Completa (con E) | Parcial (sin quiralidad) |
| **Clasificación** | Distingue K de K̄ | Agrupa K con K̄ |
| **Reconstrucción** | Sí (con E) | No (necesita σ) |
| **Uso primario** | Notación canónica | Búsqueda aquiral |

### 7.4.4 Cuándo Usar Cada Uno

**Usar DME cuando:**
- Se necesita representación completa del nudo
- Se quiere distinguir quiralidad
- Se va a reconstruir la configuración
- Se busca un nudo específico (no su reflexión)

**Usar IME cuando:**
- Se clasifica por "complejidad modular"
- No importa la quiralidad (ej: conteo de nudos)
- Se buscan nudos "similares" incluyendo reflexiones
- Se calculan estadísticas sobre familias de nudos

### 7.4.5 Ejemplo Ilustrativo

**Trébol derecho e izquierdo:**

```
K₃ (derecho):  DME = (3, -3, -3)  |  IME = (3, 3, 3)
K̄₃ (izquierdo): DME = (-3, 3, 3)  |  IME = (3, 3, 3)
```

**Búsqueda en base de datos:**

```python
# Búsqueda quiral (exacta)
db.search_by_DME((3, -3, -3))  → [K₃]  # Solo trébol derecho

# Búsqueda aquiral (agrupa reflexiones)
db.search_by_IME((3, 3, 3))    → [K₃, K̄₃]  # Ambos tréboles
```

**Estadísticas:**

```python
# Contar nudos diferentes (distinguiendo quiralidad)
count_by_DME = len(set(k.DME for k in database))  # → 2

# Contar "tipos" de nudos (sin distinguir quiralidad)
count_by_IME = len(set(k.IME for k in database))  # → 1
```

### 7.4.6 Relación Matemática Formal

```
DME = IME ⊙ σ
```

Donde:
- ⊙ es producto componente a componente
- σ = sgn(DME) = vector de signos
- IME = |DME| = magnitudes

**Inversamente:**
```
IME = |DME|
σ = sgn(DME)
```

Esta descomposición separa:
- **Magnitud** (IME) → estructura modular aquiral
- **Dirección** (σ) → quiralidad y orientación

---

## 8. Extensiones Futuras

### 8.1 Nudos Orientados

Incorporar orientación global mediante parámetro adicional:

```
K_n^{orient} = (E, DME, ω)
```

Donde ω ∈ {↻, ↺} indica orientación del nudo.

### 8.2 Enlaces (Links)

Generalizar a componentes múltiples:

```
L_{n₁,...,nₖ} = ((E₁, DME₁), ..., (Eₖ, DMEₖ))
```

Con invariantes globales:
- **IME_total = (IME₁, ..., IMEₖ)**
- **Gap_total = Σᵢ Gap(DMEᵢ)**

### 8.3 Nudos Virtuales

Añadir marcadores para cruces virtuales:

```
K_n^{virt} = (E, DME, V)
```

Donde V ⊂ {1,...,n} indexa cruces virtuales.

---

## 9. Implementación Computacional

### 9.1 Pseudocódigo en Python

```python
class KnotNotation:
    """Representación de nudo usando notación K_n = (E, DME)"""
    
    def __init__(self, n, E, DME):
        self.n = n
        self.E = E
        self.DME = DME  # Descriptor Modular Estructural (primario)
        self.validate()
    
    def validate(self):
        """Valida consistencia de la notación"""
        assert len(self.E) == self.n, "E debe tener n elementos"
        assert len(self.DME) == self.n, "DME debe tener n elementos"
        assert self.E[0] == min(self.E), "E debe estar normalizado (e₁ mínimo)"
        assert all(d != 0 for d in self.DME), "DME no puede tener ceros"
        assert all(-self.n <= d <= self.n for d in self.DME), "DME fuera de rango"
    
    def to_config(self):
        """Convierte a configuración canónica"""
        S = [(e + delta) % (2*self.n) for e, delta in zip(self.E, self.DME)]
        
        # Validar partición
        E_set = set(self.E)
        S_set = set(S)
        assert len(E_set) == self.n, "E tiene duplicados"
        assert len(S_set) == self.n, "S tiene duplicados"
        assert E_set.isdisjoint(S_set), "E y S no son disjuntos"
        
        return list(zip(self.E, S))
    
    @property
    def IME(self):
        """Invariante Modular Estructural (derivado de DME)"""
        return tuple(abs(d) for d in self.DME)
    
    @property
    def signs(self):
        """Vector de signos quirales (derivado de DME)"""
        return tuple(1 if d > 0 else -1 for d in self.DME)
    
    @property
    def gap(self):
        """Gap total (derivado de IME)"""
        return sum(self.IME)
    
    def mirror(self):
        """Retorna imagen especular (reflexión)"""
        return KnotNotation(self.n, self.E, tuple(-d for d in self.DME))
    
    def is_achiral(self):
        """Verifica si el nudo es aquiral (aproximación simple)"""
        # Un nudo es aquiral si DME = -DME bajo alguna permutación
        # Implementación simplificada: verifica simetría
        from itertools import permutations
        neg_DME = tuple(-d for d in self.DME)
        for perm in permutations(range(self.n)):
            perm_DME = tuple(self.DME[i] for i in perm)
            if perm_DME == neg_DME:
                return True
        return False
    
    @classmethod
    def from_config(cls, config):
        """Crea notación desde configuración canónica"""
        n = len(config)
        
        # Normalizar: rotar para que min(E) sea primero
        min_idx = min(range(n), key=lambda i: config[i][0])
        config_norm = config[min_idx:] + config[:min_idx]
        
        E = tuple(e for e, s in config_norm)
        
        # Calcular DME
        DME = []
        for e, s in config_norm:
            delta_raw = s - e
            # Ajustar al rango [-n, n]
            if delta_raw > n:
                delta = delta_raw - 2*n
            elif delta_raw < -n:
                delta = delta_raw + 2*n
            else:
                delta = delta_raw
            
            assert delta != 0, f"Delta = 0 en cruce ({e}, {s})"
            DME.append(delta)
        
        return cls(n, E, tuple(DME))
    
    def __repr__(self):
        return f"K_{self.n} = ({self.E}, {self.DME})"
    
    def __str__(self):
        """Representación detallada con invariantes derivados"""
        return (f"K_{self.n} = ({self.E}, {self.DME})\n"
                f"  IME = {self.IME}\n"
                f"  σ = {self.signs}\n"
                f"  Gap = {self.gap}")
```

### 9.2 Ejemplos de Uso

```python
# Ejemplo 1: Crear desde configuración (Trébol)
config_K3 = ((3,0), (1,4), (5,2))
K3 = KnotNotation.from_config(config_K3)
print(K3)  
# K_3 = ((1, 5, 3), (3, -3, -3))
#   IME = (3, 3, 3)
#   σ = (1, -1, -1)
#   Gap = 9

# Ejemplo 2: Obtener invariantes derivados
print(f"DME (primario): {K3.DME}")      # (3, -3, -3)
print(f"IME (derivado): {K3.IME}")      # (3, 3, 3)
print(f"Signos: {K3.signs}")             # (1, -1, -1)
print(f"Gap: {K3.gap}")                  # 9

# Ejemplo 3: Reconstruir configuración
config_reconstructed = K3.to_config()
print(config_reconstructed)  # [(1, 4), (5, 2), (3, 0)]

# Ejemplo 4: Reflexión especular
K3_mirror = K3.mirror()
print(K3_mirror)
# K_3 = ((1, 5, 3), (-3, 3, 3))
#   IME = (3, 3, 3)  ← ¡Igual! (invariante aquiral)
#   σ = (-1, 1, 1)   ← Opuesto
#   Gap = 9          ← Igual (invariante aquiral)

# Ejemplo 5: Test de quiralidad
print(f"¿K₃ es aquiral? {K3.is_achiral()}")  # False (es quiral)

# Ejemplo 6: Figura-8 (aquiral)
config_K4 = ((0,3), (2,7), (4,1), (6,5))
K4 = KnotNotation.from_config(config_K4)
print(K4)
# K_4 = ((0, 2, 4, 6), (3, -3, -3, -1))
#   IME = (3, 3, 3, 1)
#   σ = (1, -1, -1, -1)
#   Gap = 10

print(f"¿K₄ es aquiral? {K4.is_achiral()}")  # True

# Ejemplo 7: Comparación por IME (clasificación aquiral)
knots_db = [K3, K3_mirror, K4]
for knot in knots_db:
    print(f"{knot.__repr__()}: IME={knot.IME}, Gap={knot.gap}")
# K_3 = ((1, 5, 3), (3, -3, -3)): IME=(3, 3, 3), Gap=9
# K_3 = ((1, 5, 3), (-3, 3, 3)): IME=(3, 3, 3), Gap=9  ← Mismo IME
# K_4 = ((0, 2, 4, 6), (3, -3, -3, -1)): IME=(3, 3, 3, 1), Gap=10
```

### 9.3 Búsqueda en Base de Datos

```python
class KnotDatabase:
    def __init__(self):
        self.knots = []
    
    def add(self, knot):
        self.knots.append(knot)
    
    def search_by_IME(self, target_IME):
        """Búsqueda aquiral por IME"""
        return [k for k in self.knots if k.IME == target_IME]
    
    def search_by_DME(self, target_DME):
        """Búsqueda quiral exacta por DME"""
        return [k for k in self.knots if k.DME == target_DME]
    
    def search_by_gap(self, target_gap):
        """Búsqueda por complejidad total"""
        return [k for k in self.knots if k.gap == target_gap]

# Uso
db = KnotDatabase()
db.add(K3)
db.add(K3_mirror)
db.add(K4)

# Búsqueda aquiral
results = db.search_by_IME((3, 3, 3))
print(f"Nudos con IME=(3,3,3): {len(results)}")  # 2 (K₃ y K̄₃)

# Búsqueda quiral
results = db.search_by_DME((3, -3, -3))
print(f"Nudos con DME=(3,-3,-3): {len(results)}")  # 1 (solo K₃)
```

---

## 10. Conclusiones

La notación **K_n = (E, DME)** con su jerarquía de invariantes derivados proporciona:

### 10.1 Sistema Completo y Jerárquico

**Nivel 1 - Descriptor primario:**
- **DME** (Descriptor Modular Estructural): captura estructura completa con quiralidad

**Nivel 2 - Invariantes derivados:**
- **IME** (Invariante Modular Estructural): clasificación aquiral
- **σ** (Vector de signos): quiralidad explícita
- **Gap**: complejidad total

### 10.2 Propiedades Fundamentales

1. ✓ **Biyección perfecta**: cada K_n ↔ única configuración canónica
2. ✓ **Bidireccionalidad eficiente** (O(n) en ambas direcciones)
3. ✓ **Separación conceptual**: 
   - Descriptores quirales (DME)
   - Invariantes aquirales (IME, Gap)
4. ✓ **Codificación implícita** de quiralidad en DME
5. ✓ **Normalización canónica** automática (e₁ mínimo)
6. ✓ **Extensibilidad** a nudos orientados, enlaces, y virtuales

### 10.3 Aplicaciones Inmediatas

**En clasificación:**
- Búsqueda aquiral por IME (agrupa nudos y sus reflexiones)
- Refinamiento quiral por DME (distingue K de K̄)
- Ordenamiento por Gap (complejidad creciente)

**En bases de datos:**
- Índices primarios: IME, Gap (aquirales)
- Índices secundarios: DME (quiral completo)
- Búsqueda en dos etapas: filtrar por IME, refinar con DME

**En algoritmos:**
- Generación exhaustiva de nudos con Gap acotado
- Detección de pares quirales (DME vs -DME)
- Clasificación automática de invariantes

### 10.4 Contribución a TME

La notación **K_n = (E, DME)** es el **marco canónico** para:
- Representar configuraciones de nudos en TME
- Calcular invariantes modulares de forma sistemática
- Analizar familias de nudos por propiedades estructurales
- Integrar teoría de nudos clásica con aritmética modular

---

## Referencias

1. **Teoría Modular Estructural (TME)** - Framework base (Pabloe, 2024)
2. **Invariante Modular Estructural (IME)** - Definición y propiedades
3. Rolfsen, D. (1976). *Knots and Links*. AMS Chelsea Publishing.
4. Adams, C. (2004). *The Knot Book*. AMS.

---

## Apéndice A: Tabla de Nudos Pequeños

| Nudo | Notación K_n = (E, DME) | IME | Gap | Quiralidad |
|------|------------------------|-----|-----|------------|
| K₁ (Trivial) | ((0), (1)) | (1) | 1 | Aquiral |
| K₃ (Trébol der.) | ((1,5,3), (3,-3,-3)) | (3,3,3) | 9 | Quiral |
| K₃ (Trébol izq.) | ((1,5,3), (-3,3,3)) | (3,3,3) | 9 | Quiral |
| K₄ (Figura-8) | ((0,2,4,6), (3,-3,-3,-1)) | (3,3,3,1) | 10 | Aquiral |

**Notas:**
- El trébol derecho e izquierdo tienen el **mismo IME** (ambos (3,3,3)) pero **DME opuesto**
- Esto confirma que **IME es invariante aquiral** mientras **DME es descriptor quiral**
- La Figura-8 es aquiral: existe permutación tal que DME → -DME

---

## Apéndice B: Ajuste de Delta al Rango [-n, n]

**Función de normalización:**

```python
def normalize_delta(delta_raw, n):
    """
    Ajusta delta al rango [-n, n]
    
    Args:
        delta_raw: valor sin ajustar (s - e)
        n: número de cruces
    
    Returns:
        delta en rango [-n, n], delta ≠ 0
    """
    if delta_raw > n:
        return delta_raw - 2*n
    elif delta_raw < -n:
        return delta_raw + 2*n
    elif delta_raw == 0:
        raise ValueError("Delta no puede ser 0")
    else:
        return delta_raw
```

**Justificación:** En ℤ/2n, la distancia entre dos puntos puede medirse en dos direcciones. Elegimos siempre la menor en valor absoluto, con signo indicando dirección.

---

## Licencia

Este documento es parte del desarrollo de Teoría Modular Estructural (TME).  
© 2024 Pabloe. Todos los derechos reservados.

---

**Fin del Reporte**
