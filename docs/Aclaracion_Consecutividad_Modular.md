# Aclaración: Definición Correcta de Consecutividad en Módulo m

## ❌ Error Común

### Definición Incorrecta
```
|o - u| mod m ∈ {0, m-1}
```

**Problema:** `{0}` significaría que `o = u`, lo cual es **imposible** en un cruce válido (un arco no puede pasar sobre sí mismo).

---

## ✅ Definición Correcta

### Para Módulo m General

Dos valores `a, b ∈ ℤₘ` son **consecutivos** si:

```
|a - b| mod m ∈ {1, m-1}
```

### Explicación

- **{1}**: Consecutivos hacia adelante
  - Ejemplos en ℤ₆: (0,1), (1,2), (2,3), (3,4), (4,5)

- **{m-1}**: Consecutivos hacia atrás (vecinos en el círculo)
  - Ejemplos en ℤ₆: (0,5), (1,0), (2,1), (3,2), (4,3), (5,4)

---

## 📊 Ejemplos Específicos

### Para m = 4 (nudos de 2 cruces)

```
|a - b| mod 4 ∈ {1, 3}
```

**Consecutivos:**
- (0,1): |0-1| = 1 ✅
- (1,2): |1-2| = 1 ✅
- (2,3): |2-3| = 1 ✅
- (3,0): |3-0| = 3 ✅
- (0,3): |0-3| = 3 ✅

**NO Consecutivos:**
- (0,2): |0-2| = 2 ❌
- (1,3): |1-3| = 2 ❌

### Para m = 6 (nudos de 3 cruces)

```
|a - b| mod 6 ∈ {1, 5}
```

**Consecutivos:**
- (0,1): |0-1| = 1 ✅
- (1,2): |1-2| = 1 ✅
- (2,3): |2-3| = 1 ✅
- (3,4): |3-4| = 1 ✅
- (4,5): |4-5| = 1 ✅
- (5,0): |5-0| = 5 ✅
- (0,5): |0-5| = 5 ✅

**NO Consecutivos:**
- (0,2): |0-2| = 2 ❌
- (0,3): |0-3| = 3 ❌
- (0,4): |0-4| = 4 ❌
- (1,3): |1-3| = 2 ❌
- (1,4): |1-4| = 3 ❌
- (2,4): |2-4| = 2 ❌
- (2,5): |2-5| = 3 ❌

---

## 🔧 Aplicación a Reidemeister I

### Definición Correcta de R1

Un cruce `V(o,u)` es reducible mediante R1 si:

```
|o - u| mod m ∈ {1, m-1}
```

### Para K_2 (m=4)
```
|o - u| mod 4 ∈ {1, 3}
```

### Para K_3 (m=6)
```
|o - u| mod 6 ∈ {1, 5}
```

### Para K_n (m=2n)
```
|o - u| mod 2n ∈ {1, 2n-1}
```

---

## 🎯 Verificación de las Configuraciones K_3

Aplicando la definición **correcta** `{1, 5}`:

### K_3_1 = {V₁(0,3), V₂(4,1), V₃(2,5)}

- V₁(0,3): |0-3| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos
- V₂(4,1): |4-1| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos
- V₃(2,5): |2-5| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos

**Resultado:** Sin R1 ✅ (correcto)

### K_3_2 = {V₁(0,5), V₂(2,1), V₃(4,3)}

- V₁(0,5): |0-5| = 5 → 5 ∈ {1,5} → ✅ Consecutivos
- V₂(2,1): |2-1| = 1 → 1 ∈ {1,5} → ✅ Consecutivos
- V₃(4,3): |4-3| = 1 → 1 ∈ {1,5} → ✅ Consecutivos

**Resultado:** R1 en los 3 cruces ✅ (correcto)

### K_3_3 = {V₁(0,3), V₂(1,4), V₃(2,5)}

- V₁(0,3): |0-3| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos
- V₂(1,4): |1-4| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos
- V₃(2,5): |2-5| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos

**Resultado:** Sin R1 ✅ (correcto)

### K_3_4 = {V₁(0,5), V₂(1,4), V₃(2,3)}

- V₁(0,5): |0-5| = 5 → 5 ∈ {1,5} → ✅ Consecutivos
- V₂(1,4): |1-4| = 3 → 3 ∉ {1,5} → ❌ NO consecutivos
- V₃(2,3): |2-3| = 1 → 1 ∈ {1,5} → ✅ Consecutivos

**Resultado:** R1 en V₁ y V₃ ✅ (correcto)

---

## ✅ Conclusión

La definición correcta de consecutividad es:

```
|a - b| mod m ∈ {1, m-1}
```

**Nunca** `{0, m-1}` porque:
- `0` implica `a = b` (imposible en un cruce)
- Solo `1` y `m-1` representan vecindad en el círculo ℤₘ

---

*Aclaración generada: 2026-01-23*
