"""
Validación del Algoritmo de Género Modular
===========================================

Este script implementa el algoritmo de género modular (g_mod) descrito en
H_Shubert.txt y lo valida contra la base de datos de nudos DB_knotinfo.json.

Autor: Sistema de validación basado en la teoría Cancino-modular
Fecha: 2025-11-30
"""

import json
import ast
from collections import defaultdict
from typing import List, Tuple, Dict, Any, Optional


def genus_mod_rational(knot: List[Tuple[int, int]]) -> Dict[str, Any]:
    """
    Calcula el género modular g_mod(K) de un nudo racional a partir de su
    representación modular en términos de pares (over, under).
    
    Basado en el algoritmo formal de H_Shubert.txt usando ciclos de Seifert
    modulares calculados mediante la permutación σ = τ ∘ β.
    
    Parameters
    ----------
    knot : List[Tuple[int, int]]
        Lista de pares (over, under) con posiciones enteras en Z/(2n)Z
        
    Returns
    -------
    Dict[str, Any]
        {
            'g_mod': género modular (float),
            's_mod': número de ciclos de Seifert modulares,
            'n_crossings': número de cruces,
            'orbits': lista de órbitas (listas de IDs de extremos),
            'arcs': información de arcos,
            'success': bool indicando si el cálculo fue exitoso,
            'error': mensaje de error si success=False
        }
    """
    try:
        n = len(knot)
        if n == 0:
            return {
                'success': False,
                'error': 'El nudo debe tener al menos un cruce',
                'g_mod': None,
                's_mod': None,
                'n_crossings': 0
            }
        
        mod = 2 * n
        
        # Normalizamos over/under módulo 2n
        overs = [o % mod for (o, u) in knot]
        unders = [u % mod for (o, u) in knot]
        
        # Verificación: n under distintos
        if len(set(unders)) != n:
            return {
                'success': False,
                'error': f'Los under no son {n} valores distintos en Z/{mod}Z',
                'g_mod': None,
                's_mod': None,
                'n_crossings': n
            }
        
        # 1) Ordenamos los under para definir los arcos
        sorted_u = sorted(unders)
        
        # 2) Construimos los arcos A_j = [u_j, u_{j+1}) en Z/(2n)Z
        arcs = []
        for j in range(n):
            start = sorted_u[j]
            end = sorted_u[(j + 1) % n]
            positions = []
            kpos = start
            while True:
                positions.append(kpos)
                kpos = (kpos + 1) % mod
                if kpos == end:
                    break
            arcs.append(positions)
        
        # 3) Construimos el conjunto de extremos E = {(arc, sign)}
        extremes = []
        pos_to_extremes = defaultdict(list)
        
        for j in range(n):
            u_start = sorted_u[j]
            u_end = sorted_u[(j + 1) % n]
            for sign, pos in [('-', u_start), ('+', u_end)]:
                eid = len(extremes)
                extremes.append({
                    'id': eid,
                    'arc': j,
                    'sign': sign,
                    'pos': pos
                })
                pos_to_extremes[pos].append(eid)
        
        # Verificación: cada under tiene exactamente 2 extremos
        for u in sorted_u:
            if len(pos_to_extremes[u]) != 2:
                return {
                    'success': False,
                    'error': f'El under {u} tiene {len(pos_to_extremes[u])} extremos (debería tener 2)',
                    'g_mod': None,
                    's_mod': None,
                    'n_crossings': n
                }
        
        m_ext = len(extremes)  # debería ser 2n
        
        # 4) Involución beta: conecta los dos extremos del mismo arco
        beta = [None] * m_ext
        for e in extremes:
            eid = e['id']
            j = e['arc']
            sign = e['sign']
            for f in extremes:
                if f['arc'] == j and f['sign'] != sign:
                    beta[eid] = f['id']
                    break
            if beta[eid] is None:
                return {
                    'success': False,
                    'error': f'No se encontró pareja beta para el extremo {eid}',
                    'g_mod': None,
                    's_mod': None,
                    'n_crossings': n
                }
        
        # 5) Involución tau: smoothing en under
        #    Empareja los dos extremos que comparten la misma posición 'pos'
        tau = [None] * m_ext
        for u, eids in pos_to_extremes.items():
            a, b = eids
            tau[a] = b
            tau[b] = a
        
        # 6) sigma = tau ∘ beta
        sigma = [tau[beta[eid]] for eid in range(m_ext)]
        
        # 7) Órbitas de sigma sobre E (ciclos de Seifert modulares)
        visited = [False] * m_ext
        orbits = []
        for eid in range(m_ext):
            if not visited[eid]:
                orb = []
                cur = eid
                while not visited[cur]:
                    visited[cur] = True
                    orb.append(cur)
                    cur = sigma[cur]
                orbits.append(orb)
        
        s_mod = len(orbits)
        g_mod = (n - s_mod + 1) / 2
        
        return {
            'success': True,
            'error': None,
            'g_mod': g_mod,
            's_mod': s_mod,
            'n_crossings': n,
            'orbits': orbits,
            'arcs': arcs,
            'sorted_u': sorted_u
        }
    
    except Exception as e:
        return {
            'success': False,
            'error': f'Error inesperado: {str(e)}',
            'g_mod': None,
            's_mod': None,
            'n_crossings': len(knot) if knot else 0
        }


def parse_rational_config(config_str: str) -> Optional[List[Tuple[int, int]]]:
    """
    Parsea la configuración racional desde el formato JSON string.
    
    Ejemplo: "[[1,4],[3,0],[5,2]]" -> [(1,4), (3,0), (5,2)]
    """
    try:
        if not config_str or config_str == "NULL":
            return None
        
        config_list = json.loads(config_str)
        if not isinstance(config_list, list):
            return None
        
        # Convertimos [[o1,u1], [o2,u2], ...] a [(o1,u1), (o2,u2), ...]
        knot_pairs = []
        for pair in config_list:
            if not isinstance(pair, list) or len(pair) != 2:
                return None
            o, u = pair
            knot_pairs.append((int(o), int(u)))
        
        return knot_pairs
    
    except (json.JSONDecodeError, ValueError, TypeError):
        return None


def validate_all_knots(json_path: str) -> Dict[str, Any]:
    """
    Valida el algoritmo de género modular contra toda la base de datos.
    
    Parameters
    ----------
    json_path : str
        Ruta al archivo DB_knotinfo.json
        
    Returns
    -------
    Dict[str, Any]
        Resultados completos de la validación
    """
    print(f"Leyendo base de datos: {json_path}")
    
    with open(json_path, 'r', encoding='utf-8') as f:
        knots_db = json.load(f)
    
    print(f"Total de nudos en DB: {len(knots_db)}\n")
    
    results = {
        'total': len(knots_db),
        'processed': 0,
        'successes': [],
        'discrepancies': [],
        'errors': [],
        'skipped': []
    }
    
    for i, knot_data in enumerate(knots_db, start=1):
        knot_id = knot_data.get('id', f'unknown_{i}')
        
        # Progreso
        if i % 50 == 0:
            print(f"Procesando nudo {i}/{len(knots_db)}...")
        
        # Extraer datos relevantes
        config_str = knot_data.get('configuracion_Racional')
        three_genus_str = knot_data.get('three_genus')
        
        # Parsear género clásico
        try:
            if three_genus_str and three_genus_str != "NULL":
                three_genus = int(three_genus_str)
            else:
                three_genus = None
        except (ValueError, TypeError):
            three_genus = None
        
        # Si no hay configuración racional, skip
        if not config_str or config_str == "NULL":
            results['skipped'].append({
                'id': knot_id,
                'reason': 'No tiene configuracion_Racional'
            })
            continue
        
        # Parsear configuración racional
        knot_pairs = parse_rational_config(config_str)
        
        if knot_pairs is None:
            results['skipped'].append({
                'id': knot_id,
                'reason': 'Error al parsear configuracion_Racional'
            })
            continue
        
        # Calcular g_mod
        result = genus_mod_rational(knot_pairs)
        results['processed'] += 1
        
        # Clasificar resultado
        if not result['success']:
            results['errors'].append({
                'id': knot_id,
                'config': config_str,
                'error': result['error'],
                'three_genus': three_genus
            })
        else:
            g_mod = result['g_mod']
            
            if three_genus is None:
                # No podemos comparar
                results['skipped'].append({
                    'id': knot_id,
                    'reason': 'No tiene three_genus para comparar',
                    'g_mod': g_mod
                })
            elif abs(g_mod - three_genus) < 0.01:  # Tolerancia para float
                # ✅ Coincidencia
                results['successes'].append({
                    'id': knot_id,
                    'g_mod': g_mod,
                    'three_genus': three_genus,
                    's_mod': result['s_mod'],
                    'n_crossings': result['n_crossings']
                })
            else:
                # ⚠️ Discrepancia
                results['discrepancies'].append({
                    'id': knot_id,
                    'g_mod': g_mod,
                    'three_genus': three_genus,
                    'difference': abs(g_mod - three_genus),
                    's_mod': result['s_mod'],
                    'n_crossings': result['n_crossings'],
                    'config': config_str
                })
    
    return results


def generate_analysis_report(results: Dict[str, Any], output_path: str):
    """
    Genera un documento markdown con el análisis de resultados.
    """
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write("# Reporte de Validación: Género Modular vs. Género Clásico\n\n")
        f.write("## Resumen Ejecutivo\n\n")
        
        total = results['total']
        processed = results['processed']
        successes = len(results['successes'])
        discrepancies = len(results['discrepancies'])
        errors = len(results['errors'])
        skipped = len(results['skipped'])
        
        f.write(f"- **Total de nudos en DB**: {total}\n")
        f.write(f"- **Nudos procesados**: {processed}\n")
        f.write(f"- **✅ Coincidencias (g_mod = three_genus)**: {successes}\n")
        f.write(f"- **⚠️ Discrepancias (g_mod ≠ three_genus)**: {discrepancies}\n")
        f.write(f"- **❌ Errores de cálculo**: {errors}\n")
        f.write(f"- **⏭️ Omitidos**: {skipped}\n\n")
        
        if processed > 0:
            accuracy = (successes / processed) * 100
            f.write(f"**Precisión**: {accuracy:.2f}% de coincidencia\n\n")
        
        f.write("---\n\n")
        
        # Sección de Éxitos
        f.write("## ✅ Nudos con Coincidencia Perfecta\n\n")
        f.write(f"Total: {successes} nudos\n\n")
        
        if successes > 0:
            f.write("| ID | g_mod | three_genus | s_mod | Cruces |\n")
            f.write("|---|---|---|---|---|\n")
            for s in results['successes'][:20]:  # Primeros 20
                f.write(f"| {s['id']} | {s['g_mod']} | {s['three_genus']} | {s['s_mod']} | {s['n_crossings']} |\n")
            
            if successes > 20:
                f.write(f"\n*... y {successes - 20} más.*\n")
        
        f.write("\n---\n\n")
        
        # Sección de Discrepancias
        f.write("## ⚠️ Nudos con Discrepancias\n\n")
        f.write(f"Total: {discrepancies} nudos\n\n")
        
        if discrepancies > 0:
            f.write("| ID | g_mod | three_genus | Diferencia | s_mod | Cruces |\n")
            f.write("|---|---|---|---|---|---|\n")
            for d in results['discrepancies']:
                f.write(f"| {d['id']} | {d['g_mod']} | {d['three_genus']} | {d['difference']} | {d['s_mod']} | {d['n_crossings']} |\n")
        
        f.write("\n---\n\n")
        
        # Sección de Errores
        f.write("## ❌ Errores de Cálculo\n\n")
        f.write(f"Total: {errors} nudos\n\n")
        
        if errors > 0:
            f.write("| ID | Error | three_genus |\n")
            f.write("|---|---|---|\n")
            for e in results['errors']:
                f.write(f"| {e['id']} | {e['error']} | {e['three_genus']} |\n")
        
        f.write("\n---\n\n")
        
        # Análisis de Patrones
        f.write("## 📊 Análisis de Patrones\n\n")
        
        # Por número de cruces
        if successes > 0:
            f.write("### Distribución de Éxitos por Número de Cruces\n\n")
            crossings_dist = defaultdict(int)
            for s in results['successes']:
                crossings_dist[s['n_crossings']] += 1
            
            f.write("| Cruces | Cantidad |\n")
            f.write("|---|---|\n")
            for n_cross in sorted(crossings_dist.keys()):
                f.write(f"| {n_cross} | {crossings_dist[n_cross]} |\n")
        
        f.write("\n---\n\n")
        
        # Conclusiones
        f.write("## 🎯 Conclusiones\n\n")
        
        if processed == 0:
            f.write("No se pudieron procesar nudos. Revisar formato de datos.\n")
        elif accuracy >= 95:
            f.write("✅ El algoritmo de género modular muestra **excelente precisión** (≥95%).\n\n")
            f.write("Las discrepancias probablemente se deben a:\n")
            f.write("- Necesidad de refinar la involución τ con información de signos de cruce\n")
            f.write("- Nudos no-racionales que requieren tratamiento especial\n")
        elif accuracy >= 70:
            f.write("⚠️ El algoritmo muestra **precisión aceptable** (70-95%).\n\n")
            f.write("Se requiere:\n")
            f.write("- Implementar la versión completa de τ con orientación\n")
            f.write("- Analizar casos de discrepancia en detalle\n")
        else:
            f.write("❌ El algoritmo requiere **revisión significativa** (<70% precisión).\n\n")
            f.write("Acciones necesarias:\n")
            f.write("- Validar la construcción de configuraciones racionales\n")
            f.write("- Revisar la implementación de las involuciones β y τ\n")
        
        f.write("\n---\n\n")
        f.write("## 📝 Próximos Pasos\n\n")
        f.write("1. Analizar en detalle los nudos con discrepancias\n")
        f.write("2. Implementar τ refinada con signos de cruce y orientación\n")
        f.write("3. Validar contra casos conocidos de la literatura\n")
        f.write("4. Documentar casos especiales y excepciones\n")


if __name__ == "__main__":
    # Rutas
    json_path = r"E:\Nudos_LEAN\Scrape_Knotinfo\DB_knotinfo.json"
    output_path = r"E:\Nudos_LEAN\Scrape_Knotinfo\genus_validation_report.md"
    
    print("=" * 70)
    print("VALIDACIÓN DEL ALGORITMO DE GÉNERO MODULAR")
    print("=" * 70)
    print()
    
    # Ejecutar validación
    results = validate_all_knots(json_path)
    
    print("\n" + "=" * 70)
    print("GENERANDO REPORTE DE ANÁLISIS")
    print("=" * 70)
    print()
    
    # Generar reporte
    generate_analysis_report(results, output_path)
    
    print(f"✓ Reporte generado: {output_path}")
    print()
    print("RESUMEN:")
    print(f"  Total procesado: {results['processed']}")
    print(f"  ✅ Éxitos: {len(results['successes'])}")
    print(f"  ⚠️  Discrepancias: {len(results['discrepancies'])}")
    print(f"  ❌ Errores: {len(results['errors'])}")
    print(f"  ⏭️  Omitidos: {len(results['skipped'])}")
    
    if results['processed'] > 0:
        accuracy = (len(results['successes']) / results['processed']) * 100
        print(f"\n  PRECISIÓN: {accuracy:.2f}%")
    
    print()
    print("=" * 70)
