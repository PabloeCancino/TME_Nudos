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

**S3. Desigualdad de género `s_A + s_B ≤ c + 2k` (el hueco principal).** Combinatoria pura sobre permutaciones, SIN topología. Formulación abstracta (sonda 26, validada: exhaustivo c ≤ 4 con 2 027 025 involuciones, muestreo c = 5, 6; 0 violaciones): sobre un conjunto finito `H` de `4c` extremos de aristas, tres involuciones sin puntos fijos `ε` (empareja los extremos de cada arista), `a` y `b` (las suavizaciones A y B, con `a∘b` de ciclos de longitud 2); `s_A = órbitas ⟨ε,a⟩`, `s_B = órbitas ⟨ε,b⟩`, `k = órbitas ⟨ε,a,b⟩`. Con `p = εa`, `q = εb`, `x = ab` se cumple `cyc(p) = 2 s_A`, `cyc(q) = 2 s_B` y `p·x·q⁻¹ = 1`; el trío `(p, x, q⁻¹)` genera un grupo con `k'` órbitas, `k ≤ k' ≤ 2k`.
* **L1 (tipo Riemann-Hurwitz):** `σ τ ρ = 1` ⇒ `cyc σ + cyc τ + cyc ρ ≤ |X| + 2·órbitas⟨σ,τ,ρ⟩`. Se prueba contando trasposiciones: multiplicar por una trasposición cambia los ciclos en exactamente ±1; un producto de trasposiciones igual a la identidad cuyo grafo tiene `k` componentes sobre `m` vértices necesita al menos `2(m − k)` factores.
* **L2:** `2·(cyc p + cyc q) ≤ |H| + 8k`, es decir `s_A + s_B ≤ c + 2k`.
**CORRECCIÓN respecto a una versión anterior de este diseño:** se había descartado la ruta de permutaciones por creer que solo cubría mapas orientables (la sonda 23 mostró déficits impares). Eso era un error: aplicando L1 al trío PAR `(εa, ab, (εb)⁻¹)`, cuyo grupo es de índice ≤ 2 en `⟨ε,a,b⟩`, la no orientabilidad solo significa que ese subgrupo par tiene hasta DOS órbitas por cada órbita de `⟨ε,a,b⟩`, y la cota `k' ≤ 2k` ya la absorbe. La inducción sobre cruces queda como plan B. *Riesgo ALTO: no está en Mathlib; es la etapa que decide la viabilidad.*

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
| 25 | círculos de todo-A y todo-B = caras del mapa | alternantes planares: 100 % (4, 16, 84, 520, 3 592 en n = 1..5); no alternantes planares: nunca |
| 26 | forma abstracta de S3 con tres involuciones | 0 violaciones (c ≤ 4 exhaustivo, c = 5, 6 muestreo) |

**S0 CERRADA.** El enunciado de S3 es VERDADERO por cálculo en su forma abstracta, y S5 (adecuación, igualdad de caras) está respaldada.

## 8. Estado de S3: HECHA y verificada (rama `span-s3`, 2026-10-01)

`TMENudos/SpanGenero.lean` (849 líneas, solo `import Mathlib`) compila desde el código fuente (~20 s con los linters del proyecto), sin `sorry`, axiomas
ni `native_decide`; los teoremas clave dependen solo de `propext`, `Classical.choice` y `Quot.sound`.

* **Definiciones:** `ncs` (clases de un `Setoid`), `cyc π` (ciclos de `π`, con puntos fijos), `orb S` (órbitas del subgrupo generado por `S`).
  Justificadas con Mathlib: `cyc_eq_card_zpowers` (`cyc π` = órbitas de `zpowers π`) y `orb_eq_card_orbitRel` (`orb S` = cociente de órbitas de `Subgroup.closure S`).
* **L1 (tipo Riemann-Hurwitz), en general:** `σ * τ * ρ = 1 → cyc σ + cyc τ + cyc ρ ≤ card X + 2 * orb {σ, τ, ρ}`.
  Ruta distinta a la sugerida: inducción sobre `card X − cyc σ`, con las trasposiciones `s = (x0 σx0)` y `t = (σ⁻¹x0 x0)`, y dos casos (mismo ciclo de `τ`, o
  ciclos distintos). Los lemas clave sobre multiplicar por una trasposición usan `Equiv.Perm.SameCycle` y primer retorno.
* **L2:** `2 * (cyc (ε*a) + cyc (ε*b)) ≤ card X + 8 * orb {ε, a, b}`, es decir `s_A + s_B ≤ c + 2k`. NO necesita que `ε`, `a`, `b` ni `a∘b` carezcan de puntos
  fijos: basta que sean involuciones (se usa `cyc (a∘b) ≥ card X / 2`). La ruta del diseño (el trío par `(ε a, a b, b ε)` con `k' ≤ 2k`) funcionó sin cambios.
* **Corolario:** `L2_conexo`: con `orb {ε,a,b} = 1`, `cyc (ε*a) + cyc (ε*b) ≤ card X / 2 + 4`.
* **Sanidad con `decide`:** instancias concretas de L1 (`Fin 4`, género 0 con igualdad) y de L2 (`Fin 8`, caso justo `16 = 8 + 8·1`).

**Lo que queda del teorema del span:** S1 (corchete como polinomio de Laurent), S2 (cota de grado por estados), S4 (puente de `GDiag`/`Word` a esta formulación con
permutaciones), S5 (igualdad y adecuación en reducidos alternantes planares) y S6 (ensamblaje). La etapa de mayor riesgo, S3, está resuelta; el punto de decisión de
degradar a diagramas planares NO hace falta.

## 9. Estado de S2: HECHA y verificada (2026-10-01, noche)

`TMENudos/SpanEstados.lean` (310 líneas; importa `Mathlib`, `Etapa1_Invariancia`, `SpanGenero` y, solo para la sanidad, `Etapa1_Puente`) compila desde el código
fuente (~27 s con los linters), sin `sorry`, axiomas ni `native_decide`; los teoremas clave dependen solo de `propext`, `Classical.choice` y `Quot.sound`.
Los teoremas viven en `TMENudos.Invariancia.GDiag`, para CUALQUIER `GDiag` (no solo planares).

* **Lema clave `lazos_le_succ`:** dos estados que difieren a lo sumo en un cruce tienen `lazos σ ≤ lazos σ' + 1`. Se pasa de `lazos` a `ncs` de la clausura de
  equivalencia de `rel σ` (`lazos_eq`, `reachableSetoid_fromRel`), lo que absorbe los casos degenerados (bucles, vértices repetidos). Ruta más simple que la
  sugerida: sin grafo auxiliar `K`, con `join1` y `ncs_le_join1` de `SpanGenero`.
* **Cotas por estados:** `lazos_le_allA : lazos σ ≤ lazos allA + nB σ` y `lazos_le_allB : lazos σ ≤ lazos allB + nA σ`.
* **Cotas de exponente en ℤ:** `expo_upper : expo σ + 2*(lazos σ − 1) ≤ c + 2*lazos allA − 2` y `expo_lower : −c − 2*lazos allB + 2 ≤ expo σ − 2*(lazos σ − 1)`;
  `expo_allA = c`, `expo_allB = −c`.
* **Sanidad:** `sanidad_trefoil`: `c = 3`, `lazos allA = 2`, `lazos allB = 3` (`s_A + s_B = 5 = c + 2`, el caso de igualdad).

**Efecto en el plan:** con S2 y S3 queda lista la cota GENERAL `span ≤ 2c + 2(s_A + s_B) − 4 ≤ 4c` a nivel de estados. Falta S1 (hacerla una cota sobre un polinomio de Laurent), S4 (unirla
con `SpanGenero` mediante las permutaciones del modelo), S5 y S6.

## 10. Estado de S1: HECHA y verificada (2026-10-01, noche)

`TMENudos/SpanLaurent.lean` (416 líneas; importa `SpanEstados` y `Etapa1_Nudos`) compila desde el código fuente (~25 s con los linters), sin `sorry`, axiomas ni
`native_decide`; los 10 teoremas clave dependen solo de `propext`, `Classical.choice` y `Quot.sound`.

* **Corchete como polinomio de Laurent:** `bracketL D : LaurentPolynomial ℤ` (la suma de estados con `A = T`) y `jonesL D`. `evalL_bracketL` y `evalL_jonesL`
  prueban que su evaluación en un cuerpo es el `bracket`/`jones` ya existente.
* **Inyectividad:** `evalL_injective`: dos polinomios de Laurent que coinciden al evaluar en todo racional no nulo son iguales (`exists_T_pow`, raíces de un
  polinomio sobre un dominio infinito).
* **Invariancia polinomial:** `jonesL_rel : GRel d d' → jonesL d.D = jonesL d'.D` y `bracketL_rel : bracketL d'.D = s * T k * bracketL d.D` con `s = ±1`.
* **Span:** `span p = (maxExp p − minExp p).toNat`; `span_unit_mul` (las unidades `±T^k` no lo cambian) y **`span_bracketL_rel : GRel d d' → span (bracketL d.D) = span (bracketL d'.D)`**.
* **Cota por estados en el polinomio:** `inBox_bracketL` y **`span_bracketL_le_of_nonempty : span (bracketL D) ≤ 2c + 2(s_A + s_B) − 4`** si hay algún cruce.
* **Borde:** con `Cross` vacío y `free = 0`, `bracketL = 1` y la cota de S2 no aplica (el span real es 0); se trata aparte.
* **Sanidad:** `span_trefoil_le : span (bracketL (ofWord trefoil _)) ≤ 12 = 4·3`.

**Efecto en el plan:** con S1, S2 y S3 queda la cota general **por demostrar solo el puente (S4)**: `span ≤ 2c + 2(s_A + s_B) − 4 ≤ 4c` para diagramas de una curva. Faltan S4, S5 y S6.

## 11. Estado de S4: HECHA y verificada (2026-10-01, noche)

`TMENudos/SpanPuente.lean` (523 líneas; importa `SpanGenero` y `SpanEstados`) compila desde el código fuente (~22 s con los linters), sin `sorry`, axiomas ni `native_decide`;
los teoremas clave dependen solo de `propext`, `Classical.choice` y `Quot.sound`.

* **Teorema final:** `lazos_allA_add_allB_le (D : GDiag ι) (hfree : D.free = 0) (hcurve : ∀ i j, D.next.SameCycle i j) (hne : Nonempty D.Cross) :
  D.lazos D.allA + D.lazos D.allB ≤ Fintype.card D.Cross + 2` (es `s_A + s_B ≤ c + 2`, para toda palabra de Gauss de una curva, planar o no, orientable o no).
* **Lema abstracto:** `two_orb_le_cyc : 2 * orb {ε,a} ≤ cyc (ε*a)` para involuciones sin puntos fijos (`x` y `ε x` están en ciclos distintos de `ε*a`, `not_cyc_eps`).
* **Modelo:** `X = ι × Bool` (`false` = entrada, `true` = salida); `ε (j,true) = (next j,false)`; emparejamiento genérico `sm ori (j,s) = (partner j, xor s (ori j))`;
  `a = sm sign`, `b = sm (!sign)`; `a*b` es el paso por el cruce `(j,s) ↦ (j,!s)`. Sin puntos fijos sin hipótesis extra.
* **Lazos = órbitas:** `lazos_allA_eq`, `lazos_allB_eq` (con `free = 0`) vía `phi (j,true) = j`, `phi (j,false) = prev j`; cardinal `card_modelo : |ι × Bool| = 4c`; conexión `orb_eq_one`.
* **Sanidad:** `genero_trefoil` aplica el teorema al trébol SIN hipótesis pendientes (`2 + 3 ≤ 3 + 2`, igualdad).

**Efecto:** con S1, S2, S3 y S4 queda la cota general `span (bracketL D) ≤ 2c + 2(s_A + s_B) − 4 ≤ 4c` para todo diagrama de una curva. Faltan S5 (igualdad en reducidos alternantes) y S6.

## 12. Estado de S5a: HECHA y verificada, con el PRIMER TEOREMA DE MINIMALIDAD (2026-10-02)

`TMENudos/SpanAdecuado.lean` (~560 líneas; importa `SpanLaurent` y `SpanPuente`) compila desde el código fuente (~27 s con los linters), sin `sorry`, axiomas ni `native_decide`;
los teoremas clave dependen solo de `propext`, `Classical.choice` y `Quot.sound`. Álgebra y combinatoria GENERAL sobre cualquier `GDiag`, sin geometría.

* **Adecuación:** `AAdequate D := ∀ x, lazos (update allA x false) < lazos allA` y `BAdequate` análogo. `lazos_lt_of_AAdequate`: si `1 ≤ nB σ`, `lazos σ + 1 ≤ lazos allA + nB σ`.
* **Coeficientes extremos:** `coeff_dL_pow_top/bot` (el coeficiente extremo de `dL^m` es `(-1)^m`), `coeff_top`, `coeff_bot` y **`maxExp_bracketL`**, **`minExp_bracketL`**
  (exponentes extremos exactos del corchete de un diagrama adecuado).
* **Span exacto:** `span_bracketL_eq : (span (bracketL D) : ℤ) = 2c + 2(s_A + s_B) − 4` si `AAdequate`, `BAdequate` y `Nonempty Cross`;
  `span_bracketL_eq_four_mul : span = 4c` si además `s_A + s_B = c + 2`. Caso sin cruces: `span_bracketL_of_isEmpty` (el corchete es 1, span 0).
* **Trébol:** `trefoil_AAdequate`, `trefoil_BAdequate` (por `decide +kernel` sobre los 3 + 3 estados de un solo cambio) y **`span_trefoil_eq : span (bracketL (ofWord trefoil _)) = 12`**.
* **`trefoil_minimal`** (teorema piloto): si `GRel ⟨_, ofWord trefoil _⟩ d'`, `d'.D.free = 0` y `d'` es de una sola curva (`∀ i j, d'.D.next.SameCycle i j`), entonces
  **`3 ≤ Fintype.card d'.D.Cross`**: todo diagrama de una curva del trébol tiene al menos 3 cruces. Ruta: `span_bracketL_rel` (el span es invariante por `GRel`) da `span = 12`;
  si `Cross` es vacío el span es 0 (contradicción); si no, `span ≤ 4 c'` por `span_bracketL_le_of_nonempty` y la desigualdad de género de `SpanPuente`.

**Incidente resuelto:** `import SpanLaurent` y `import SpanPuente` chocaban por `GDiag.phi` (ya definido en `Etapa1_R3`). Se renombró `phi`, `phi_surj`, `phi_eps`, `phi_fib` a `phiS...` en
`SpanPuente.lean` (27 reemplazos, todo dentro de ese archivo); `SpanPuente` y `SpanAdecuado` recompilan sin problema.

**Lo que falta:** (i) S5b: probar que los diagramas alternantes planares REDUCIDOS son A- y B-adecuados y cumplen `s_A + s_B = n + 2`; en general (geometría: caras monocromáticas por la alternancia,
planar = `F = n + 2`, reducido ⇒ cada cruce toca dos caras distintas) o, de forma verificable, por un **verificador computable** que compruebe ambas cosas sobre una palabra concreta con su teorema de
corrección, y lo aplique a todas las palabras alternantes reducidas planares hasta n = 6 o 7 (4, 8, 24, 168, 676) y a los nudos con nombre; (ii) S6: enunciar el teorema general
(`GRel` + una curva ⇒ `c' ≥ n`) para toda palabra con esas propiedades, que es exactamente el esquema de `trefoil_minimal`.

## 13. Estado de S5b: HECHA y verificada, verificador computable y censo (2026-10-02)

`TMENudos/SpanCensos.lean` (859 líneas; importa `SpanAdecuado`; NO importa `Etapa1_Planaridad`) y la sonda `27_palabras_lean.py`. Compila (build de ~26 min con picos de ~7,4 GB de RAM; ver nota
operativa), sin `sorry`, axiomas ni `native_decide`. Los teoremas centrales dependen solo de `propext`, `Classical.choice` y `Quot.sound` (los censos, solo de `propext` y `Quot.sound`).

* **Verificador:** `checkW (w : Word) : Bool` = al menos un cruce, `s_A + s_B = n + 2` y, para cada cruce, cambiar UNA suavización desde todo-A (resp. todo-B) baja estrictamente los lazos.
* **Corrección general (el entregable central):** `checkW_correct` (`AAdequate ∧ BAdequate ∧ Nonempty Cross ∧ s_A + s_B = c + 2`), `span_of_check : span (bracketL (ofWord w)) = 4 · n` y
  **`minimal_of_check`**: si `checkW w = true`, todo diagrama de UNA curva sin libres equivalente por `GRel` a `ofWord w` tiene al menos `n` cruces. El trébol se recupera (`trefoil_minimal'`).
* **Nudos con nombre (cota inferior de cruces):** `minimal_41` (4), `minimal_51` (5), `minimal_52` (5), `minimal_61`, `minimal_62`, `minimal_63` (6), con spans 16, 20, 20, 24, 24, 24. La cota superior es trivial.
* **Censo `wordOfData`/`passes`:** `pasan_3` (4 datos, el trébol y su espejo con otra paridad), `pasan_4` (8, el nudo de ocho), `pasan_5` (24, en 10 trozos de ~70 s). Conteos de Lean = conteos de la sonda 22 de Python.
  Para n = 6 y 7, listas explícitas de Python (168 y 676 palabras): `censo6_passes`, `censo7_passes` y `*_length`, `*_nodup`.

**Qué NO está demostrado (declarado en el docstring del módulo):**
1. Que TODO diagrama alternante reducido planar pase `checkW` (la parte geométrica general de S5b). Solo se verifica caso por caso.
2. La COMPLETITUD de `censo6` y `censo7` (que sean todos los reducidos de 6 y 7 cruces): es un hecho de Python. Enumerarlos en el kernel costaría ~2 h (n = 6) y ~30 h (n = 7).
3. Que `checkW` fallido implique no-minimal: no es cierto en general.
4. El puente "toda palabra alternante arbitraria es, salvo rotación y renombrado, una `wordOfData`".

**Nota operativa.** Esta build es PESADA (26 min, ~7,4 GB). No está en la raíz. No recompilarla sin necesidad; construir de una en una. El agente cerró una vez `lake.exe`/`lean.exe` genéricos (pudo cerrar servidores
Lean del editor): reiniciar el servidor de Lean en VS Code si hace falta.

## 14. S5c: la adecuación sale del género cero, sin geometría (sonda 28, 2026-10-02)

**Idea.** Para un diagrama de UNA curva con `s_A + s_B = c + 2` (género de Turaev cero) y un cruce `x` que no sea de corte, la A- y la B-adecuación en `x` se deducen de la desigualdad
de género aplicada al estado DESACOPLADO en `x`: usar en `x` el emparejamiento B también en `a` deja la terna `(ε, a_x, b)` con `a_x ∘ b` involución con exactamente 4 puntos fijos (el bloque de `x`).
Un L2 refinado (`2(cyc p + cyc q) + f ≤ |X| + 8·orb`, con `f` los puntos fijos de `a·b`) da `lazos(σ_x) + s_B ≤ (c − 1) + 2·orb{ε,a_x,b}`; con `orb = 1` y `s_A + s_B = c + 2` sale `lazos(σ_x) ≤ s_A − 1`.
La condición `orb{ε, a_x, b} = 1` (el cruce no desconecta la estructura al desacoplarlo) equivale a que la cuerda de `x` esté entrelazada con alguna otra.

**Respaldo por cálculo (sonda 28, exhaustiva hasta n = 5, 967 680 palabras en n = 5):** en TODA palabra de una curva con `s_A + s_B = n + 2` (planar o no, alternante o no, orientable o no), si la cuerda de `x`
está entrelazada con otra, hay adecuación en `x` en los estados A y B: 0 violaciones. Además, los diagramas con `s_A + s_B = n + 2` son exactamente los PLANARES (336, 4 160 y 57 472 en n = 3, 4, 5, igual que la sonda 25).
El recíproco falla (una cuerda aislada puede ser adecuada en uno de los dos estados, pero no en ambos de forma sistemática).

**Qué cambia.** La parte geométrica general de S5b se reduce a dos propiedades limpias: (a) `s_A + s_B = c + 2` para los alternantes planares (caras monocromáticas por la alternancia, planar = F = n + 2),
y (b) toda cuerda entrelazada con otra implica no-nugatorio. La adecuación deja de ser un cálculo caso por caso. Teorema objetivo de S5c: `D` de una curva, `free = 0`, `s_A + s_B = c + 2`, `NonNugatory D` ⇒ A- y B-adecuado
⇒ `span = 4c` ⇒ minimalidad de cruces. Archivo previsto: `TMENudos/SpanNoNugatorio.lean`.

## 15. Estado de S5c: HECHA y verificada, adecuación desde género cero y no-nugatorio (2026-10-02)

`TMENudos/SpanNoNugatorio.lean` (483 líneas; importa `SpanAdecuado`, `SpanPuente`, `SpanGenero`) compila desde el código fuente (~24 s con los linters), sin `sorry`, axiomas ni `native_decide`;
los teoremas clave dependen solo de `propext`, `Classical.choice` y `Quot.sound`. Confirma lo que la sonda 28 anticipaba por cálculo.

* **L2 refinado (abstracto):** `card_add_fixed_le_two_cyc : card X + #fijos(x) ≤ 2 · cyc x` para una involución y
  **`L2_refinado : 2 (cyc(ε a) + cyc(ε b)) + #fijos(a b) ≤ card X + 8 · orb{ε,a,b}`**. (Solo la desigualdad; la igualdad `2 cyc x = |X| + f` no se necesita.)
* **Estado desacoplado:** `aX x`, `bX x` (el emparejamiento `a`/`b` con el otro tipo en el cruce `x`); involuciones sin puntos fijos; `aX x * b` es involución con **exactamente 4 puntos fijos**
  (`card_fixed_aX_b`, `card_fixed_a_bX`: los extremos del cruce `x`).
* **Adecuación en un cruce:** `lazos_update_allA_lt` (si `s_A + s_B = c + 2` y `orb{ε,aX x,b} = 1`, cambiar `x` desde todo-A baja los lazos) y `lazos_update_allB_lt`.
* **Definición y teoremas generales:** `NonNugatory D := ∀ x, orb{ε,aX x,b} = 1 ∧ orb{ε,a,bX x} = 1`; `adequate_of_nonNugatory`; **`span_eq_four_mul_of_nonNugatory : span = 4 c`**;
  **`minimal_of_nonNugatory`**: si `d` es de una curva, sin libres, con algún cruce, `s_A + s_B = c + 2` y `NonNugatory`, todo `d'` de una curva sin libres con `GRel d d'` tiene `c(d) ≤ c(d')`.
* **Trébol:** `trefoil_nonNugatory` (por `orb_eq_one_of_path`, caminos hallados por BFS y comprobados con `decide +kernel`), `span_trefoil_eq_of_nonNugatory` (span 12 por la vía nueva) y `trefoil_minimal_nonNugatory`.

**Qué NO está probado:** que "toda cuerda tiene otra entrelazada" implique `NonNugatory` para palabras (la conexión combinatoria es abierta); que `s_A + s_B = c + 2` se cumpla en los alternantes planares (S5d, en curso);
la igualdad `2 cyc x = |X| + f`.
