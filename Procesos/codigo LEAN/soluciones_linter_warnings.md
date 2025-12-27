# Soluciones para los Warnings del Linter (líneas 299, 303)

## Contexto

Después de `unfold OrderedPairN.reverse at hi_qfst`, tenemos:
```lean
hi_qfst : i = { fst := r.snd, snd := r.fst, ... }.fst
```

Que `simp` simplifica a:
```lean
hi_qfst : i = r.snd
```

## OPCIÓN 1: Usar simp only (Más explícito)

Reemplaza las líneas 296-304 con:

```lean
      · rcases hq_has with hi_qfst | hi_qsnd
        · right
          unfold OrderedPairN.reverse at hi_qfst
          simp only at hi_qfst
          exact hi_qfst
        · left
          unfold OrderedPairN.reverse at hi_qsnd
          simp only at hi_qsnd
          exact hi_qsnd
```

**Ventaja**: Mínimo cambio, `simp only` sin argumentos es aceptable para el linter.
**Desventaja**: Todavía usa simplificación implícita.

## OPCIÓN 2: Usar show (Más claro)

Reemplaza las líneas 296-304 con:

```lean
      · rcases hq_has with hi_qfst | hi_qsnd
        · right
          show i = r.snd
          unfold OrderedPairN.reverse at hi_qfst
          exact hi_qfst
        · left
          show i = r.fst
          unfold OrderedPairN.reverse at hi_qsnd
          exact hi_qsnd
```

**Ventaja**: Más declarativo, muestra explícitamente qué estamos probando.
**Desventaja**: Requiere saber de antemano el resultado de la simplificación.

## OPCIÓN 3: Directamente sin simp (Más directo)

Reemplaza las líneas 296-304 con:

```lean
      · rcases hq_has with hi_qfst | hi_qsnd
        · right
          exact hi_qfst
        · left
          exact hi_qsnd
```

**Ventaja**: Más simple, elimina el `unfold` y `simp` completamente.
**Desventaja**: Depende de que Lean infiera automáticamente que `r.reverse.fst = r.snd`.

## OPCIÓN 4: Deshabilitar el linter (No recomendado generalmente)

Agrega al inicio del archivo (después de los imports):

```lean
set_option linter.flexible false
```

**Ventaja**: No requiere cambios en el código.
**Desventaja**: Oculta el warning, no mejora el código.

## MI RECOMENDACIÓN

**OPCIÓN 1** (`simp only` sin argumentos) es el mejor balance:
- Cambio mínimo
- Satisface al linter
- Funciona en Lean 4.26.0

Si quieres código más limpio y declarativo, usa **OPCIÓN 2** (`show`).
