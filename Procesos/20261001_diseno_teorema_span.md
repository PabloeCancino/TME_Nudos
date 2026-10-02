# Diseño por etapas: el teorema del span (minimalidad real de cruces a nivel de nudo)

**Fecha:** 2026-10-01 · **Estado:** DISEÑO, no implementado · **Camino:** (B) (ver `20261001_diseno_camino_B_nudos_racionales.md`)
**Respaldo empírico:** sonda 22 (span = 4n en el 100 % de los alternantes planares reducidos, n = 2 a 7; menor en los no reducidos) y sonda 22c.

## 1. Enunciado objetivo
Sea `w` una palabra de Gauss con signos, de UNA sola curva, planar, alternante, con `n` cruces y **sin cuerdas aisladas** (reducida). Entonces:
1. `span ⟨w⟩ = 4n`.
2. **Corolario (minimalidad de cruces a nivel de nudo):** si un diagrama `D'` de una sola curva con `c` cruces es equivalente a `ofWord w` por
   `GRel` (R1, R2, R3 e isomorfismo), entonces `c ≥ n`.

El corolario es lo que el axioma A6 de `Basic` pretendía y no podía dar: `n` es el número de cruces del nudo, no solo el mínimo bajo R1/R2.

## 2. Esquema matemático (clásico: Kauffman, Murasugi, Thistlethwaite)
Corchete: `⟨D⟩ = Σ_S A^{a(S) − b(S)} d^{|S| − 1}`, con `d = −A² − A⁻²`; `a`, `b` = número de suavizaciones A y B del estado `S`, `|S|` = círculos.
* **Cota superior de grado (cualquier diagrama).** Un estado con `k` suavizaciones B tiene exponente A `c − 2k` y `|S| ≤ s_A + k`
  (cambiar UNA suavización cambia el número de círculos en como mucho 1). Luego `deg ≤ c + 2 s_A − 2`; simétricamente `mindeg ≥ −c − 2 s_B + 2`.
  Entonces `span ≤ 2c + 2(s_A + s_B) − 4`.
* **Desigualdad de género (cualquier diagrama de una curva):** `s_A + s_B ≤ c + 2`. Luego `span ≤ 4c`.
* **Igualdad (reducido alternante planar):** `s_A + s_B = n + 2` (los círculos del estado todo-A son las caras de un color del tablero, los del todo-B
  las del otro, y juntas son las `n + 2` caras de Euler) y el diagrama es A-adecuado y B-adecuado (cambiar una suavización desde todo-A BAJA los círculos
  en exactamente 1; falla justo cuando hay un cruce nugatorio). Entonces el estado todo-A es el único de grado máximo, con coeficiente ±1, y lo mismo
  el todo-B: `span = 2n + 2(n + 2) − 4 = 4n`.
* **Corolario:** el Jones es invariante bajo `GRel` salvo un factor unidad `±A^{k}` (ya demostrado), que desplaza el grado pero NO el span. Así
  `4n = span(w) = span(D') ≤ 4c`.

## 3. Etapas
Cada etapa deja el archivo compilando, sin `sorry`, axiomas ni `native_decide`, y se verifica antes de pasar a la siguiente.

**S0. Comprobaciones previas por cálculo (Python).** Decide si el plan es viable antes de invertir en Lean.
* Sonda 23 (HECHA): `s_A + s_B ≤ n + 2` en TODOS los diagramas de una curva (incluidos no planares), n ≤ 5 (967 680 diagramas en n = 5): el déficit nunca es negativo. La paridad par es FALSA (aparecen déficits impares: superficies no orientables); no se necesita.
* Sonda 24 (HECHA): entre los alternantes planares (n = 2..6), TODOS los reducidos son A- y B-adecuados (4, 8, 24 y 168 en n = 3..6; 0 excepciones) y NINGUNO de los no reducidos lo es (80, 512, 3 568 y 26 624). En esta familia, reducido ⇔ adecuado.
* Sonda 25: en alternantes planares, los círculos del estado todo-A son las caras de un color (identificación explícita).

**S1. Corchete como polinomio de Laurent.** Definir `bracketPoly` sobre `GDiag` (o sobre `Word`) con valores en `LaurentPolynomial ℤ` y
probar que su evaluación es el `bracket` de cuerpo existente. Como la invariancia ya está para todo cuerpo y todo `A ≠ 0`, se deduce la invariancia
polinomial evaluando en infinitos racionales (un polinomio de Laurent con coeficientes enteros que se anula en todo racional no nulo es cero).
Definir `maxdeg`, `mindeg`, `span`. *Riesgo bajo-medio; es infraestructura.*

**S2. Cota por estados (cualquier diagrama).** `|S| ≤ s_A + k`, es decir que cambiar una suavización cambia los círculos en a lo sumo 1; de ahí
`maxdeg ≤ c + 2 s_A − 2` y `mindeg ≥ −c − 2 s_B + 2`. *Riesgo medio: manejo de los grafos de estados del modelo existente.*

**S3. Desigualdad de género `s_A + s_B ≤ c + 2` (el hueco principal).** Resultado puramente combinatorio, SIN topología. OJO (sonda 23): los signos libres de `GDiag` dan superficies de Turaev NO ORIENTABLES (hay déficits `(n+2) − (s_A + s_B)` impares: 1, 3, 5), así que la ruta de permutaciones `ciclos(σ) + ciclos(α) + ciclos(φ) ≤ |X| + 2` (conteo de transposiciones) solo cubre el caso orientable y NO basta. Ruta principal: **inducción sobre el número de cruces** con la desigualdad generalizada `s_A + s_B ≤ c + 2k`, `k` = componentes conexas del diagrama, eligiendo en cada paso la suavización que conserva la conexión (en un cruce de corte, una de las dos suavizaciones lo mantiene conexo; la otra lo parte en dos) y usando que cambiar UNA suavización cambia los círculos en a lo sumo 1. Se prueba como lema independiente y reutilizable. *Riesgo ALTO: no está en Mathlib; es la etapa que decide la viabilidad.*

**S4. Puente al modelo.** Expresar `s_A`, `s_B` y los círculos de un estado como ciclos de permutaciones del `GDiag`, y probar que una sola curva
(`next` con un único ciclo) da un grupo transitivo. Combinar S2 y S3: `span ≤ 4c` para todo diagrama de una curva. *Riesgo medio.*

**S5. Igualdad para reducidos alternantes planares.** (a) `s_A + s_B = n + 2`: identificar los círculos de todo-A con las caras de un color
usando la planaridad (`Etapa1_Planaridad.lean`) y la alternancia; (b) adecuación: cambiar una suavización desde todo-A baja los círculos en 1 si y solo si
la cuerda no es aislada; (c) coeficiente extremo ±1. *Riesgo ALTO: la identificación con caras es la parte más técnica.*

**S6. Ensamblaje y corolario.** `span(ofWord w) = 4n`; invariancia del span bajo `GRel`; y de ahí `c ≥ n` para todo diagrama de una curva de la clase.
*Riesgo bajo si S1 a S5 están.*

## 4. Dependencias entre etapas
`S1, S2, S3` son independientes entre sí; `S4` necesita S2 y S3; `S5` necesita S1 y la planaridad; `S6` necesita todas.
**Orden recomendado:** S0 (cálculo) → S3 (decide la viabilidad; si no sale, el teorema general no se podrá) → S1 → S2 → S4 → S5 → S6.

## 5. Punto de decisión (go / no-go) tras S0 y S3
* Si la sonda 23 falla (algún diagrama con `s_A + s_B > n + 2`), el enunciado de S3 es falso para el modelo y hay que revisar la definición de estado.
* Si S3 resulta inabordable en un esfuerzo razonable, se degrada el objetivo: probar el span SOLO para diagramas PLANARES (donde `s_A + s_B ≤ c + 2` sale de la
  característica de Euler del propio diagrama planar con sus caras, usando lo ya construido en `Etapa1_Planaridad.lean`), con la clase de competidores
  restringida a la de `ClassicalKnot` (pasos entre planares). Es un teorema algo más débil pero sigue dando minimalidad de cruces entre diagramas CLÁSICOS.

## 6. Qué NO promete
No demuestra el teorema de Reidemeister ni la clasificación de Schubert; no cubre diagramas con circunferencias libres ni de varias componentes; el
resultado vale para nudos (una curva). No sustituye a (A): lo complementa (los reducidos son irreducibles de (A), no al revés).

## 7. Estado de S0 (2026-10-01)
| Sonda | Qué comprueba | Resultado |
|---|---|---|
| 22 | span = 4n en reducidos, < 4n en no reducidos | 100 % para n = 2..7 |
| 23 | `s_A + s_B ≤ n + 2` en toda palabra de una curva | se cumple (n ≤ 5, 967 680 diagramas); la paridad es falsa |
| 24 | adecuación de los alternantes planares | reducido ⇔ A- y B-adecuado (n = 2..6) |
| 25 | círculos de todo-A = caras de un color | pendiente |

Con esto, S0 está casi cerrada: queda la sonda 25. El enunciado de S3 (desigualdad de género) es VERDADERO por cálculo y S5 (adecuación) está respaldada.
