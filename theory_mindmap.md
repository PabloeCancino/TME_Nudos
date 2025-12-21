# Mapa Mental: Teoría Modular Estructural de Nudos (TME)

Este diagrama visualiza el eje discursivo de la teoría, desde sus axiomas fundamentales hasta los teoremas de clasificación, basado en la formalización en `Basic.lean`.

```mermaid
mindmap
  root((TME Nudos))
    Fundamentos Axiomáticos
      A1: Espacio del Recorrido
        Z_2n (Cíclico)
        Suma Modular
      A2: Doble Modularidad
        Trayectoria (Mod 2n)
        Nivel (Mod 2 - Alternancia)
      A3: Interlazado
        Intervalos Discretos
        Matriz de Interlazado
    Objetos
      Configuración Racional
        Cruces (Over/Under)
        Cobertura Total
      Invariante Modular (IME)
        Razón Modular [o,u]
        Secuencia de Razones
    Dinámica e Isotopía
      A4: Equivalencia Isotópica
        Movimientos Reidemeister
          R1 (Bucles)
          R2 (Bigones)
          R3 (Deslizamiento)
        Rotaciones (Simetría Cíclica)
      Operaciones
        Espejo (Involución)
        Progresión
    Teoremas Principales
      Reconstrucción
        IME determina posiciones salvo rotación
      Forma Normal (T5)
        Existencia y Unicidad
        Irreducibilidad = Minimalidad (L5)
      Completitud del IME
        Isotopía <=> Mismo IME (en irreducibles)
    Conexión Aritmética
      Fracciones Continuas
      Clasificación de Schubert
      Equivalencia Aritmética
```

## Descripción del Eje Discursivo

1.  **Fundamentación**: La teoría parte de definir un espacio discreto y finito (`ℝ[n]`) donde "habitan" los nudos, regido por aritmética modular.
2.  **Estructuración**: Sobre este espacio se definen los **Cruces** y su **Interlazado**, creando la `RationalConfiguration`.
3.  **Caracterización**: Se extrae la esencia del nudo en el **IME** (Invariante Modular Estructural), una lista de números que codifica la geometría.
4.  **Dinámica**: Se define cuándo dos nudos son equivalentes (`Isotopic`) mediante movimientos locales (R1, R2, R3) y globales (Rotación).
5.  **Clasificación**: El punto culminante es demostrar que el IME es un "código de barras" perfecto: dos nudos irreducibles son iguales si y solo si sus IMEs son iguales.
6.  **Puente Aritmético**: Finalmente, se conecta esta visión combinatoria con la teoría clásica de fracciones continuas.
