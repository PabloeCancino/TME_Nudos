# Clasificación Formal de Nudos de Tres Cruces: Primera Verificación Completa en Lean 4

[![CI Build](https://github.com/PabloeCancino/TME_Nudos/actions/workflows/build.yml/badge.svg)](https://github.com/PabloeCancino/TME_Nudos/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Public](https://img.shields.io/badge/Repository-Public-green)](https://github.com/PabloeCancino/TME_Nudos)

## Descripción General del Proyecto

Este proyecto presenta la **primera clasificación formalmente verificada** de configuraciones de nudos de tres cruces (K₃) utilizando el asistente de pruebas Lean 4. El trabajo establece, mediante verificación mecánica completa, que existen exactamente **dos nudos no equivalentes** de tres cruces: el nudo trefoil derecho y su imagen especular, el trefoil izquierdo.

## Marco Teórico: Teoría Modular Estructural (TME)

La investigación desarrolla un enfoque innovador basado en **aritmética modular** sobre el anillo Z/6Z, donde cada configuración de tres cruces se representa mediante pares ordenados de elementos. Este marco combina herramientas de álgebra moderna (grupos diedrales, teoría de órbitas) con teoría de nudos clásica, permitiendo una clasificación algorítmica con complejidad O(n).

Los **invariantes modulares** desarrollados (DME, IME, Gap, Writhe) capturan propiedades geométricas fundamentales de los nudos, incluyendo quiralidad y simetría. La acción del grupo diedral D₆ sobre las configuraciones modela rotaciones y reflexiones en el plano, estableciendo relaciones de equivalencia entre nudos.

## Metodología y Estructura

El proyecto se organiza en **siete bloques modulares** que construyen progresivamente la teoría completa:

1. **Fundamentos**: Estructuras básicas, invariantes modulares y propiedades (38 teoremas)
2. **Movimientos Reidemeister**: Definición formal de simplificaciones locales R1 y R2
3. **Matchings Perfectos**: Caracterización combinatoria de configuraciones
4. **Grupo Diedral D₆**: Formalización de simetría con 12 elementos
5. **Órbitas y Estabilizadores**: Teorema órbita-estabilizador y cálculo de clases
6. **Representantes Canónicos**: Identificación de los dos nudos únicos
7. **Teorema de Clasificación**: Prueba formal del resultado principal con unicidad

Cada bloque fue verificado completamente en Lean 4, eliminando todos los marcadores `sorry` y alcanzando **100% de completitud formal**.

## Resultados y Descubrimientos

El proyecto establece formalmente que a partir de $D_6$, su espacio combinatorio de 120 configuraciones K₃ se reduce a **8 configuraciones irreducibles** (sin movimientos Reidemeister locales), agrupadas en **dos órbitas de 4 elementos** cada una bajo la acción de D₆. Un descubrimiento importante durante la verificación fue la detección y corrección de un error conceptual: una configuración previamente considerada válida (specialClass) resultó contener movimientos R2, demostrando el valor práctico de la verificación formal.

El código resultante comprende **~3,500 líneas de Lean 4** con **150+ teoremas probados**, respaldado por documentación técnica exhaustiva de más de 200 páginas que incluye estrategias de prueba, patrones reutilizables y guías de extensión.

## Impacto y Proyecciones

Este trabajo establece un precedente metodológico para la verificación formal en teoría de nudos, proporcionando un framework extensible a clasificaciones superiores (K₄, K₅, ...). La combinación de técnicas algebraicas, análisis computacional y verificación mecánica abre nuevas posibilidades para abordar problemas abiertos en topología de baja dimensión con garantías de corrección absoluta.

---

**Institución**: Universidad Autónoma de Nayarit  
Unidad Académica de Ciencias Básicas e Ingenierías  
Programa Académico de Licenciatura en Matemáticas  
**Autor**: Dr. Pablo Eduardo Cancino Marentes  
**Verificación**: Lean 4.25.0 + Mathlib  
**Estado**: Proyecto completado (Diciembre 2025)

