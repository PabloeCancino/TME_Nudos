"""
Cálculo de Perfiles de Writhe para Nudos Anfiquirales
Basado en Liang & Mislow (1994)

Teoría:
- Para nudos anfiquirales: wp = 0 para TODO p
- Para nudos quirales: primer wp ≠ 0 determina D/L
"""

from rational_knot_theory import RationalKnot, RationalCrossing
from typing import List, Tuple
import json

def expand_diagram(knot: RationalKnot, order: int) -> RationalKnot:
    """
    Expande diagrama de nudo a orden p.
    
    Según Liang & Mislow:
    - Cada cruce se reemplaza por una "escalera" de (order+1) cruces
    - Los signos se preservan en la expansión
    
    Args:
        knot: Nudo original
        order: Orden de expansión (p)
        
    Returns:
        Nudo expandido
    """
    if order == 0:
        return knot
    
    expanded_crossings = []
    crossing_counter = 1
    segment_counter = 1
    
    # Mapa de segmentos originales a nuevos segmentos
    segment_map = {}
    
    for crossing in knot.crossings:
        # Cada cruce original se expande en (order+1) cruces
        # formando una "escalera" o "ladder"
        
        # Crear nuevos segmentos para este cruce expandido
        if crossing.over not in segment_map:
            segment_map[crossing.over] = []
        if crossing.under not in segment_map:
            segment_map[crossing.under] = []
        
        # Generar escalera de cruces
        for i in range(order + 1):
            # Asignar segmentos para esta expansión
            if i == 0:
                # Primer cruce usa segmento original
                over_seg = crossing.over if not segment_map[crossing.over] else segment_counter
                segment_counter += 1
            else:
                over_seg = segment_counter
                segment_counter += 1
            
            if i == 0:
                under_seg = crossing.under if not segment_map[crossing.under] else segment_counter
                segment_counter += 1
            else:
                under_seg = segment_counter
                segment_counter += 1
            
            # Crear cruce expandido con mismo signo
            expanded_crossing = RationalCrossing(
                index=crossing_counter,
                over=over_seg,
                under=under_seg,
                sign=crossing.sign
            )
            expanded_crossings.append(expanded_crossing)
            crossing_counter += 1
    
    return RationalKnot(expanded_crossings)

def writhe(knot: RationalKnot) -> int:
    """
    Calcula el writhe (suma de signos de cruces).
    
    Args:
        knot: Nudo
        
    Returns:
        Writhe (suma de signos)
    """
    return sum(c.sign for c in knot.crossings)

def writhe_profile(knot: RationalKnot, max_order: int = 5) -> List[int]:
    """
    Calcula perfil de writhe para órdenes 0 a max_order.
    
    Según Liang & Mislow:
    - Para nudos anfiquirales: todos los wp deben ser 0
    - Para nudos quirales: primer wp ≠ 0 determina quiralidad
    
    Args:
        knot: Nudo a analizar
        max_order: Orden máximo de expansión
        
    Returns:
        Lista [w₀, w₁, w₂, ..., w_max_order]
    """
    profile = []
    
    for p in range(max_order + 1):
        expanded = expand_diagram(knot, p)
        wp = writhe(expanded)
        profile.append(wp)
    
    return profile

def is_amphichiral_by_writhe(profile: List[int]) -> bool:
    """
    Determina si un nudo es anfiqueiral basado en perfil de writhe.
    
    Criterio de Liang: wp = 0 para todo p
    
    Args:
        profile: Perfil de writhe
        
    Returns:
        True si todos los wp son 0
    """
    return all(wp == 0 for wp in profile)

def classify_chirality(profile: List[int]) -> str:
    """
    Clasifica quiralidad según perfil de writhe.
    
    Reglas de Liang:
    - Todos wp = 0 → Anfiqueiral
    - Primer wp ≠ 0 positivo → D (dextro)
    - Primer wp ≠ 0 negativo → L (levo)
    
    Args:
        profile: Perfil de writhe
        
    Returns:
        "Amphichiral", "D", o "L"
    """
    for p, wp in enumerate(profile):
        if wp != 0:
            return "D" if wp > 0 else "L"
    
    return "Amphichiral"

def test_amphichiral_knots():
    """
    Test de perfiles de writhe para nudos anfiquirales conocidos.
    """
    print("=" * 80)
    print("TEST DE PERFILES DE WRITHE - Nudos Anfiquirales")
    print("=" * 80)
    print("\nTeoría de Liang & Mislow: Para nudos anfiquirales, wp = 0 ∀p")
    print()
    
    # Cargar base de datos actualizada
    try:
        from rolfsen_database_updated import ROLFSEN_KNOTS
        print("✅ Usando rolfsen_database_updated.py")
    except:
        from rolfsen_database import ROLFSEN_KNOTS
        print("⚠️ Usando rolfsen_database.py (original)")
    
    # Lista de nudos anfiquirales conocidos
    amphichiral_knot_ids = ['4_1', '6_3', '8_3', '8_9', '8_12', '8_17', '8_18']
    
    results = {}
    
    for knot_id in amphichiral_knot_ids:
        if knot_id not in ROLFSEN_KNOTS:
            print(f"\n{knot_id}: ❌ No encontrado en base de datos")
            continue
        
        knot_info = ROLFSEN_KNOTS[knot_id]
        print(f"\n{knot_id} ({knot_info.common_name}):")
        
        try:
            # Crear nudo desde configuración en base de datos
            knot = RationalKnot.from_pairs(
                knot_info.rational_config,
                knot_info.signs
            )
            
            # Calcular perfil de writhe (solo hasta orden 2 para eficiencia)
            profile = writhe_profile(knot, max_order=2)
            
            # Clasificar
            classification = classify_chirality(profile)
            is_amph = is_amphichiral_by_writhe(profile)
            
            print(f"  Cruces: {knot.n_crossings()}")
            print(f"  Perfil de writhe [w₀, w₁, w₂]: {profile}")
            print(f"  Clasificación: {classification}")
            print(f"  ¿Anfiqueiral? {'✅ SÍ' if is_amph else '❌ NO'}")
            
            results[knot_id] = {
                'profile': profile,
                'classification': classification,
                'is_amphichiral': is_amph,
                'n_crossings': knot.n_crossings()
            }
            
        except Exception as e:
            print(f"  ❌ Error: {e}")
            import traceback
            traceback.print_exc()
            results[knot_id] = {'error': str(e)}
    
    # Resumen
    print("\n" + "=" * 80)
    print("RESUMEN")
    print("=" * 80)
    
    total = len([r for r in results.values() if 'error' not in r])
    amphichiral_count = sum(1 for r in results.values() 
                           if 'is_amphichiral' in r and r['is_amphichiral'])
    
    print(f"\nTotal nudos analizados: {total}")
    print(f"Nudos con wp = 0 ∀p: {amphichiral_count}")
    if total > 0:
        print(f"Tasa de confirmación: {amphichiral_count}/{total} ({100*amphichiral_count/total:.1f}%)")
    
    # Guardar resultados
    with open('writhe_profiles_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n✅ Resultados guardados en: writhe_profiles_results.json")
    
    return results

if __name__ == "__main__":
    results = test_amphichiral_knots()
