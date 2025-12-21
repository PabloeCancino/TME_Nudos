"""
Script de Diagnóstico de Colisión de Firmas
Investiga por qué 3_1 y 5_2 tienen la misma firma modular.
"""

from rational_knot_theory import RationalKnot
from rolfsen_database_updated import ROLFSEN_KNOTS

def get_canonical_rep(knot: RationalKnot) -> str:
    """Obtiene la representación canónica (cadena) antes del hash."""
    n = knot.n_crossings
    mod = 2 * n
    pairs = [(c.over, c.under) for c in knot.crossings]
    
    canonical_forms = []
    for k in range(mod):
        shifted_pairs = []
        for o, u in pairs:
            new_o = (o + k - 1) % mod + 1
            new_u = (u + k - 1) % mod + 1
            shifted_pairs.append((new_o, new_u))
        shifted_pairs.sort()
        s = "|".join([f"{o},{u}" for o, u in shifted_pairs])
        canonical_forms.append(s)
        
    return min(canonical_forms)

def debug_collision():
    knots_to_check = ['3_1', '5_2']
    
    print("=" * 60)
    print("DIAGNÓSTICO DE COLISIÓN 3_1 vs 5_2")
    print("=" * 60)
    
    reps = {}
    
    for knot_id in knots_to_check:
        if knot_id not in ROLFSEN_KNOTS:
            print(f"❌ {knot_id} no encontrado en DB")
            continue
            
        info = ROLFSEN_KNOTS[knot_id]
        knot = RationalKnot.from_pairs(info.rational_config, info.signs)
        
        print(f"\nNudo {knot_id}:")
        print(f"  Cruces (n): {knot.n_crossings}")
        print(f"  Pares Originales: {[(c.over, c.under) for c in knot.crossings]}")
        
        canonical = get_canonical_rep(knot)
        print(f"  Rep. Canónica:    {canonical}")
        reps[knot_id] = canonical

    print("\nCOMPARACIÓN:")
    if reps['3_1'] == reps['5_2']:
        print("❌ ¡LAS REPRESENTACIONES CANÓNICAS SON IDÉNTICAS!")
        print("Esto es matemáticamente imposible si n es diferente (3 vs 5).")
        print("Posible causa: ¿El objeto RationalKnot de 5_2 se construyó mal?")
    else:
        print("✅ Las representaciones son diferentes. El hash colisionó (muy improbable) o hubo error lógico previo.")

if __name__ == "__main__":
    debug_collision()
