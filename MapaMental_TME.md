# Mapa Mental: Teoría Modular Estructural de Nudos (TME)

Este diagrama visualiza el eje discursivo de la teoría, desde sus axiomas fundamentales hasta los teoremas de clasificación. Refleja el estado del código a **2026-10-01** (`master` en `211d1d6`), tras migrar la teoría al **signo del cruce como dato**.

**Cómo leerlo.** Cada resultado lleva una marca de estado:
`«P»` demostrado en Lean (solo con `propext`, `Classical.choice`, `Quot.sound`) ·
`«A»` descansa en un axioma declarado · `«S»` contiene un `sorry` · `«C»` axioma citado de la literatura · `«Cálculo»` verificado por `decide +kernel` sobre un espacio finito.

```mermaid
mindmap
  root((TME Nudos))
    Fundamentos Axiomáticos
      A1: Espacio del Recorrido
        Z_2n cíclico «P»
        Suma Modular «P»
      A2: Doble Modularidad
        Trayectoria (Mod 2n)
        Nivel (Mod 2 - Alternancia)
      A3: Interlazado
        Intervalos Discretos
        Matriz de Interlazado
    Objetos con signo como dato
      Cruce firmado
        Posición superior e inferior
        Signo pos Bool, dato
        60 cruces en n=3 «P»
        Signo derivado = caso particular
      Configuración Racional
        Cobertura Total
        K3 firmada 960 configuraciones «Cálculo»
      Invariantes modulares
        IME Razón Modular [o,u]
        SIME razón y signo
    Dinámica e Isotopía
      A4: Equivalencia Isotópica
        Movimientos Reidemeister
          R1 (Bucles)
          R2 Bigones, con signos opuestos
          R3 (Deslizamiento)
        Las transiciones conservan el signo
        Rotaciones, conservan signo
      Operaciones
        Espejo swap, invierte over-under y signo
        El trébol y su espejo son clases distintas «Cálculo»
        Progresión
    Teoremas Principales
      Reconstrucción
        Mismas razones y signos implica rotación «A», refutado en n=3
      Forma Normal (T5)
        Existencia y Unicidad «A»
        Irreducibilidad = Minimalidad, L5 «A»
      Completitud
        Isotopía <=> mismo SIME en irreducibles «A»
        Con el IME solo la vuelta es falsa
    Realizabilidad y Planaridad
      K3 firmado
        172 irreducibles en 18 órbitas «Cálculo»
        336 con índice cero «Cálculo»
        4 realizables, trébol derecho e izquierdo «Cálculo»
        Clasificación en dos clases «Cálculo»
      Planaridad exacta
        Género cero por caras de sigma y alpha «P»
        K3: índice cero equivale a planar «Cálculo»
        Índice cero NO basta en general, contraejemplo n=4 «P»
    Capa Computable de Gauss
      Palabras de Gauss con signos
      Corchete de Kauffman por estados
        Invariancia R1 R2 R3 «P»
      Polinomio de Jones «P»
        Trébol distinto de su espejo «P»
      ClassicalKnot
        Diagramas planares módulo movimientos entre planares «P»
        Sin suma conexa clásica
    Conexión con Nudos Abstractos
      Schubert 1949 «C»
        Unicidad y existencia de factorización
        jones2 como axioma de la capa abstracta «A»
        Granny distinto de Square «A»
      Bridge
        rational_to_diagram es definición inyectiva «P»
        Consistencia con la isotopía «A»
      Reidemeister abstracto
        Equivalencia inductiva
        apply_R1 R2 R3 «S»
    Conexión Aritmética
      Fracciones Continuas «A»
      Clasificación de Schubert «C»
      Equivalencia Aritmética
```

## Estado de la formalización (conteos verificados)

| Capa | Estado |
|---|---|
| Módulos de `TMENudos/` | 47 compilan por nombre, 0 errores |
| Axiomas declarados | 50 (Schubert 25, Reidemeister 11, Basic 5, KN_01 5, Bridge 1, y uno en `KN_00`, `TCN_01` y `TCN_08_Uniformity`) |
| `sorry` | 17 (Schubert 11, Reidemeister 4, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1) |
| Capa de Gauss, planaridad y `ClassicalKnot` | sin `sorry` ni axiomas propios; fuera de la build por defecto (módulos `Etapa1_*`) |

## Descripción del Eje Discursivo

1. **Fundamentación**: La teoría parte de definir un espacio discreto y finito (`ℝ[n]`) donde "habitan" los nudos, regido por aritmética modular.
2. **Estructuración**: Sobre este espacio se definen los **Cruces** y su **Interlazado**, creando la `RationalConfiguration`. Cada cruce lleva ahora un **signo como dato**: derivarlo de las posiciones perdía la quiralidad, porque en las parejas antipodales el intercambio no cambia el signo y el trébol y su espejo se confundían.
3. **Caracterización**: Se extrae la esencia del nudo en el **IME** (razones modulares) y, con el signo como dato, en el **SIME** (razón y signo de cada cruce).
4. **Dinámica**: Se define cuándo dos nudos son equivalentes (`Isotopic`) mediante movimientos locales (R1, R2 con signos opuestos, R3) y globales (rotación). Todas las transiciones conservan el signo.
5. **Clasificación**: Dos nudos irreducibles son iguales si y solo si sus SIME son iguales, bajo los axiomas de reconstrucción, minimalidad y unicidad (`«A»`). Con el IME solo, la implicación recíproca es falsa.
6. **Realizabilidad**: Entre las configuraciones de tres cruces, las realizables (irreducibles, de paridad de Gauss par y de **índice cero**) son exactamente el trébol derecho y el izquierdo. El índice cero es una condición necesaria de planaridad que coincide con ella para K₃, pero **no basta en general**: hay un contraejemplo con cuatro cruces.
7. **Capa computable**: Las palabras de Gauss con signos, el corchete de Kauffman y el polinomio de Jones están demostrados invariantes bajo R1, R2 y R3. Con el Jones se prueba que el trébol y su espejo son nudos distintos. La noción de nudo clásico (`ClassicalKnot`) exige pasar solo por diagramas planares.
8. **Puente Aritmético y abstracto**: Se conecta esta visión combinatoria con la teoría clásica de fracciones continuas y con el teorema de Schubert (axiomas citados), y con los nudos abstractos mediante `Bridge`.

## Límites que el mapa no debe ocultar

- Los teoremas de clasificación general (forma normal, completitud, reconstrucción) descansan en **axiomas**, no están demostrados desde cero.
- La factorización de Schubert y el Jones de la capa abstracta (`jones2`) son **axiomas** de la capa abstracta; solo el cálculo concreto sobre palabras de Gauss está demostrado.
- Que *planar implica índice cero* se comprobó solo hasta n = 4 por cálculo; no es teorema.
- `ClassicalKnot` no tiene operación espejo general ni suma conexa (exige pegar en la misma cara).
