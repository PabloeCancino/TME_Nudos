# Evaluación de 4 Configuraciones de K_3

## 📋 Configuraciones Evaluadas

Evaluamos 4 configuraciones de nudos de **3 cruces** en módulo **m = 6**:

1. **K_3_1** = {V₁(0,3), V₂(4,1), V₃(2,5)}
2. **K_3_2** = {V₁(0,5), V₂(2,1), V₃(4,3)}
3. **K_3_3** = {V₁(0,3), V₂(1,4), V₃(2,5)}
4. **K_3_4** = {V₁(0,5), V₂(1,4), V₃(2,3)}

---

## 🔧 Criterios Aplicados

### Reidemeister I (R1)
Un cruce V(o,u) es reducible si **o y u son consecutivos en mod 6**:
```
|o - u| mod 6 ∈ {1, 5}
```

### Reidemeister II (R2)
Dos cruces V₁(o₁,u₁) y V₂(o₂,u₂) son reducibles si **ambos pares son consecutivos**:
```
|o₁ - o₂| mod 6 ∈ {1, 5}  Y  |u₁ - u₂| mod 6 ∈ {1, 5}
```

---

## 📊 Resultados Detallados

### K_3_1 = {V₁(0,3), V₂(4,1), V₃(2,5)}

#### Análisis de Cruces

| Cruce | (over, under) | Consecutivos?      | Orientación | R1  |
| ----- | ------------- | ------------------ | ----------- | --- |
| V₁    | (0, 3)        | \|0-3\| = 3 → ❌ NO | +           | ❌   |
| V₂    | (4, 1)        | \|4-1\| = 3 → ❌ NO | +           | ❌   |
| V₃    | (2, 5)        | \|2-5\| = 3 → ❌ NO | +           | ❌   |

#### Análisis R2 entre Pares

| Par   | Overs         | Unders        | R2  |
| ----- | ------------- | ------------- | --- |
| V₁-V₂ | \|0-4\| = 4 ❌ | \|3-1\| = 2 ❌ | ❌   |
| V₁-V₃ | \|0-2\| = 2 ❌ | \|3-5\| = 2 ❌ | ❌   |
| V₂-V₃ | \|4-2\| = 2 ❌ | \|1-5\| = 4 ❌ | ❌   |

#### Resultados

- **Etapa 1:** 1 componente → **NUDO**
- **Etapa 2:** Sin R1 ni R2 → **NO TRIVIAL**
- **Writhe:** +3

---

### K_3_2 = {V₁(0,5), V₂(2,1), V₃(4,3)}

#### Análisis de Cruces

| Cruce | (over, under) | Consecutivos?      | Orientación | R1  |
| ----- | ------------- | ------------------ | ----------- | --- |
| V₁    | (0, 5)        | \|0-5\| = 5 → ✅ SÍ | -           | ✅   |
| V₂    | (2, 1)        | \|2-1\| = 1 → ✅ SÍ | +           | ✅   |
| V₃    | (4, 3)        | \|4-3\| = 1 → ✅ SÍ | +           | ✅   |

#### Resultados

- **Etapa 1:** 1 componente → **NUDO**
- **Etapa 2:** R1 en los 3 cruces → **TRIVIAL**
- **Writhe:** +1
- **Razón:** Reducible mediante R1 (todos los cruces tienen arcos consecutivos)

---

### K_3_3 = {V₁(0,3), V₂(1,4), V₃(2,5)}

#### Análisis de Cruces

| Cruce | (over, under) | Consecutivos?      | Orientación | R1  |
| ----- | ------------- | ------------------ | ----------- | --- |
| V₁    | (0, 3)        | \|0-3\| = 3 → ❌ NO | +           | ❌   |
| V₂    | (1, 4)        | \|1-4\| = 3 → ❌ NO | +           | ❌   |
| V₃    | (2, 5)        | \|2-5\| = 3 → ❌ NO | +           | ❌   |

#### Análisis R2 entre Pares

| Par   | Overs         | Unders        | R2  |
| ----- | ------------- | ------------- | --- |
| V₁-V₂ | \|0-1\| = 1 ✅ | \|3-4\| = 1 ✅ | ✅   |
| V₁-V₃ | \|0-2\| = 2 ❌ | \|3-5\| = 2 ❌ | ❌   |
| V₂-V₃ | \|1-2\| = 1 ✅ | \|4-5\| = 1 ✅ | ✅   |

#### Resultados

- **Etapa 1:** 1 componente → **NUDO**
- **Etapa 2:** R2 entre V₁-V₂ y V₂-V₃ → **TRIVIAL**
- **Writhe:** +3
- **Razón:** Reducible mediante R2 (pares consecutivos)
- **Pares con R2:** (1,2), (2,3)

---

### K_3_4 = {V₁(0,5), V₂(1,4), V₃(2,3)}

#### Análisis de Cruces

| Cruce | (over, under) | Consecutivos?      | Orientación | R1  |
| ----- | ------------- | ------------------ | ----------- | --- |
| V₁    | (0, 5)        | \|0-5\| = 5 → ✅ SÍ | -           | ✅   |
| V₂    | (1, 4)        | \|1-4\| = 3 → ❌ NO | +           | ❌   |
| V₃    | (2, 3)        | \|2-3\| = 1 → ✅ SÍ | -           | ✅   |

#### Análisis R2 entre Pares

| Par   | Overs         | Unders        | R2  |
| ----- | ------------- | ------------- | --- |
| V₁-V₂ | \|0-1\| = 1 ✅ | \|5-4\| = 1 ✅ | ✅   |
| V₁-V₃ | \|0-2\| = 2 ❌ | \|5-3\| = 2 ❌ | ❌   |
| V₂-V₃ | \|1-2\| = 1 ✅ | \|4-3\| = 1 ✅ | ✅   |

#### Resultados

- **Etapa 1:** 1 componente → **NUDO**
- **Etapa 2:** R1 en V₁ y V₃, R2 entre V₁-V₂ y V₂-V₃ → **TRIVIAL**
- **Writhe:** 0
- **Razón:** Reducible mediante R1 y R2
- **Pares con R2:** (1,2), (2,3)

---

## 📈 Resumen Comparativo

| Config    | Componentes | Clasificación | R1           | R2          | Trivial | Writhe |
| --------- | ----------- | ------------- | ------------ | ----------- | ------- | ------ |
| **K_3_1** | 1           | Nudo          | ❌            | ❌           | **NO**  | +3     |
| **K_3_2** | 1           | Nudo          | ✅ (3 cruces) | ❌           | **SÍ**  | +1     |
| **K_3_3** | 1           | Nudo          | ❌            | ✅ (2 pares) | **SÍ**  | +3     |
| **K_3_4** | 1           | Nudo          | ✅ (2 cruces) | ✅ (2 pares) | **SÍ**  | 0      |

---

## 🎯 Conclusiones

### 1. Todas son Nudos (1 Componente)

✅ Las 4 configuraciones tienen **1 componente conexa** → Son nudos, no enlaces

### 2. Solo 1 Configuración es No Trivial

❌ **K_3_1** es el único nudo **no trivial**
- Sin R1 ni R2 aplicable
- Writhe = +3
- **Primer ejemplo de nudo no trivial** en nuestro análisis

✅ **K_3_2, K_3_3, K_3_4** son triviales

### 3. Distribución de Mecanismos

| Mecanismo   | Configuraciones |
| ----------- | --------------- |
| **Solo R1** | K_3_2           |
| **Solo R2** | K_3_3           |
| **R1 y R2** | K_3_4           |
| **Ninguno** | K_3_1           |

### 4. Relación Writhe-Trivialidad

⚠️ **No hay correlación directa:**
- K_3_3: Writhe +3, **trivial**
- K_3_1: Writhe +3, **no trivial**

El writhe **no determina** la trivialidad por sí solo.

---

## 🔬 Análisis Especial: K_3_1 (No Trivial)

### Características Únicas

K_3_1 = {V₁(0,3), V₂(4,1), V₃(2,5)}

1. **Simetría perfecta:** Todos los cruces tienen la misma "distancia" (3 en mod 6)
2. **Patrón uniforme:** |oᵢ - uᵢ| = 3 para todo i
3. **Sin consecutividad:** Ni interna (R1) ni correspondiente (R2)

### Posible Identificación

Este patrón podría corresponder al **trébol** (trefoil knot, 3₁):
- 3 cruces
- Writhe +3
- No trivial
- Primer nudo no trivial en la tabla de nudos

---

## ✅ Validación de las Etapas

### ETAPA 1: Teoría de Grafos

✅ **Funcionó correctamente:**
- Todas las configuraciones: 1 componente
- Clasificación: Nudos (no enlaces)
- Algoritmo BFS: Decidible

### ETAPA 2: Movimientos de Reidemeister

✅ **Funcionó correctamente:**
- Detectó R1 en 5 cruces (de 12 totales)
- Detectó R2 en 4 pares
- Clasificó correctamente: 3 triviales, 1 no trivial
- Algoritmos R1 y R2: Decidibles

### AMBAS ETAPAS SON NECESARIAS

> [!IMPORTANT]
> - **Etapa 1** distingue nudos de enlaces
> - **Etapa 2** distingue nudos triviales de no triviales
> - **Juntas** proporcionan clasificación completa

---

## 📁 Archivos Generados

- **[evaluar_K3_configuraciones.py](file:///c:/Users/pablo/OneDrive/Documentos/TME_Nudos/scripts/evaluar_K3_configuraciones.py)** - Script de evaluación
- **[evaluacion_K3_4_configuraciones.json](file:///c:/Users/pablo/OneDrive/Documentos/TME_Nudos/data/evaluacion_K3_4_configuraciones.json)** - Resultados detallados

---

*Evaluación completada: 2026-01-23*
*Primer nudo no trivial identificado: K_3_1*
