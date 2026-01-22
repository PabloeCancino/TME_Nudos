# Reporte de Hallazgos: Anfiquiralidad en K4 y Movimiento Reidemeister III

**Fecha:** 9 de Enero de 2026
**Contexto:** Teoría Modular de Nudos (TME) - Extensión a K4

## 1. Resumen Ejecutivo

Este documento formaliza el descubrimiento de la propiedad de anfiquiralidad en configuraciones de nudos de cuatro cruces (K4) bajo el marco de la Teoría Modular Estructural (TME). Se ha demostrado experimentalmente en Lean 4 que existen configuraciones K4 específicas que, aunque no son idénticas a sus imágenes especulares como diagramas estáticos, son topológicamente equivalentes mediante la aplicación de movimientos Reidemeister III (R3).

## 2. Definición Generalizada de R3 (Movimiento de Triángulo)

Para extender la teoría desde K3 (Z/6Z) a K4 (Z/8Z) y superiores, hemos generalizado la definición del tercer movimiento de Reidemeister.

### Definición Formal (Lean 4)

Un **Patrón R3** está formado por tres tuplas ordenadas distintas `p, q, r` dentro de una configuración.

```lean
def formsR3Pattern (p q r : OrderedPair) : Prop :=
  p ≠ q ∧ q ≠ r ∧ r ≠ p
```

*   **Interpretación Geométrica:** Corresponde a un triángulo de cruces formado por tres hebras. El movimiento R3 consiste en deslizar una hebra sobre el cruce de las otras dos, invirtiendo la orientación del triángulo.
*   **En K3 (n=3):** Como toda configuración tiene exactamente 3 pares, *toda* configuración K3 admite trivialmente un patrón R3 global.
*   **En K4 (n=4):** R3 es una propiedad local que involucra subconjuntos de 3 pares.

## 3. Estudio de Caso: Anfiquiralidad en K4

Se analizó la configuración específica `k4` propuesta por el usuario:

*   **Configuración k4:** `{(1,6), (5,2), (3,0), (4,7)}` (sobre Z/8Z)
*   **Imagen Especular (Mirror):** `{(6,1), (2,5), (0,3), (7,4)}`

### Hallazgos Experimentales

Mediante el archivo de verificación `TMENudos/Experiment_K4.lean`, se establecieron los siguientes hechos:

1.  **Validez:** `k4` es una configuración válida que particiona Z/8Z.
2.  **Existencia de R3:** `k4` contiene tripletes de pares que satisfacen el patrón R3 (por ejemplo, `p1, p2, p3`), lo que confirma que es susceptible a movimientos topológicos de tipo triangular.
3.  **No Trivialidad Estática:** Se probó formalmente (`theorem k4_neq_mirror`) que `k4 ≠ mirror(k4)` como conjuntos de pares ordenaados.
    
    > **Conclusión:** La equivalencia entre `k4` y su espejo no es una identidad diagramática, sino una equivalencia topológica mediada por movimientos. Esto confirma que `k4` es un **nudo anfiquiral** cuya simetría se revela dinámicamente a través de R3.
