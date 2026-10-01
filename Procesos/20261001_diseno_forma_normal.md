# Diseño: forma normal única para la reducción R1/R2 (A6 y A7 como teoremas)

**Fecha:** 2026-10-01 · **Estado:** DISEÑO (no implementado). Respaldo empírico: sondas 20 y 21 (plan, secciones 3.6 y 3.7).
**Objetivo:** demostrar en Lean, para TODO n, que el sistema de reducción R1/R2 sobre diagramas con signos es
terminante y confluente, de modo que cada clase de equivalencia tiene una forma normal única salvo rotación y
reetiquetado. De ahí salen, como teoremas, la versión fiel de A6 («irreducible ⇒ grado mínimo») y de A7 («dos
diagramas de grado mínimo de la misma clase son el mismo salvo rotación y reetiquetado»).

## 1. Alcance honesto
* Es la clasificación de DIAGRAMAS módulo R1/R2 y rotación. NO es la clasificación de nudos: sin R3 ni flypes, dos
  diagramas del mismo nudo pueden tener formas normales distintas (sondas 19 y 19b: desde n = 7).
* No sustituye los axiomas A6/A7 de `Basic` (que hablan de la relación laxa `Isotopic`); los reemplaza como
  teoremas de un modelo nuevo. Cambiar `Basic` para usarlo es un paso posterior y opcional.
* Incluye el diagrama VACÍO (nudo trivial), que `Basic` no puede representar.

## 2. Modelo (lista de pasos, sin renumeración de posiciones)
Se usa la representación de palabra de Gauss con signos, en listas:

```
structure Letter where  label : ℕ ;  over : Bool ;  pos : Bool      -- como Etapa1_GaussWord.Letter
abbrev W := List Letter                                              -- lista CÍCLICA
```
Buena formación `Wf w`: cada etiqueta aparece exactamente dos veces, una con `over = true` y otra con
`over = false`, con el mismo signo. Quitar un cruce = `w.filter (· .label ≠ c)`: NO hace falta renumerar.
Esto evita el problema central de las posiciones (`ZMod (2n)` con rangos). Rotación = `List.rotate`.

Equivalencia `w ≈ w'`: existen una rotación de `w` y una biyección de etiquetas que la llevan a `w'`.

Movimientos (equivalentes a `is_R1_candidate` e `is_R2_candidate` de Basic, ya validados en las sondas):
* R1 en la etiqueta `c`: las dos letras de `c` son CÍCLICAMENTE consecutivas. Se quita `c`.
* R2 en `(a, b)`: `a ≠ b`, los pasos superiores de `a` y `b` son consecutivos, los inferiores son consecutivos,
  las cuerdas se entrelazan, y los signos son opuestos. Se quitan `a` y `b`.
Un paso reduce el número de cruces (1 o 2). El diagrama vacío `[]` es válido.

## 3. Teoremas objetivo
1. `Red` es bien fundada (por el número de cruces).
2. Local confluencia módulo `≈`: si `w → x` y `w → y`, existen `x →* x'`, `y →* y'` con `x' ≈ y'`.
3. Forma normal única (lema de Newman módulo `≈`): `w →* n`, `w →* n'` irreducibles ⇒ `n ≈ n'`.
4. A6 fiel: `w` irreducible ⇒ `w` tiene el menor número de cruces de su clase `EqvGen (Red ∪ Red⁻¹ ∪ ≈)`.
5. A7 fiel: `w, w'` equivalentes, ambos de grado mínimo ⇒ `w ≈ w'`.

## 4. Descomposición en etapas
**Etapa 1 (infraestructura, sin geometría):**
* modelo, `Wf`, `crossings`, `Red`, `≈` y su carácter de equivalencia;
* lema abstracto de Newman módulo una equivalencia compatible, para un tipo `α`, una relación `R` bien fundada y
  una equivalencia `E` con: (a) `R` es compatible con `E` (si `x E x'` y `x → y` entonces `∃ y', x' → y' ∧ y E y'`);
  (b) local confluencia módulo `E`. Conclusión: confluencia módulo `E`.
* persistencia de candidatos: si `c` es candidato R1 (o `(a,b)` R2) en `w` y `d ∉ {c}` (resp. `∉ {a,b}`), sigue
  siéndolo en `w` sin `d`;
* conmutación de reducciones disjuntas: `(w∖S)∖T = (w∖T)∖S`.

**Etapa 2 (el único solapamiento):**
* dos pares R2 `(a,b)` y `(b,c)` con `a ≠ c`: `w` es, salvo rotación, `X ++ [a_o,b_o,c_o] ++ Y ++ [a_u,b_u,c_u] ++ Z`
  (o su simétrica) con signos `(s,−s,s)`; entonces `w∖{a,b} ≈ w∖{b,c}`;
* un candidato R1 no se solapa con uno R2.

**Etapa 3 (ensamblaje):** teoremas 1 a 5, y comprobación cruzada con las sondas 20 y 21 en n = 2, 3, 4 (los conteos de
clases de equivalencia y de formas normales deben coincidir con el cálculo).

## 5. Riesgos
| Riesgo | Mitigación |
|---|---|
| La adyacencia CÍCLICA complica las pruebas de lista (envolvimiento) | Trabajar módulo rotación y usar la forma `X ++ [..] ++ Y ++ [..] ++ Z`; tratar el envolvimiento rotando |
| Newman módulo una equivalencia no está en Mathlib | Lema propio en abstracto (Etapa 1), reutilizable |
| El entrelazado en listas es incómodo | Definirlo por posiciones de letras (`findIdx`) y probar lemas de invariancia por rotación |
| Que aparezcan solapamientos que el análisis de papel omitió | La sonda 21 es exhaustiva hasta n = 4 y no halló ninguno; si la prueba formal tropieza, el contraejemplo se busca por cálculo |

## 6. Qué NO promete
No demuestra la clasificación de nudos racionales; no toca `Basic`; no incluye R3 ni flypes. Si sale, el resultado
honesto es: «la reducción R1/R2 de diagramas con signos tiene forma normal única», con A6 y A7 fieles como corolarios.
