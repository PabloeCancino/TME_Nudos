"""
Script de Prueba para Clave Criptológica (Firma Modular)
Verifica la invarianza de la firma bajo transformaciones del nudo.
"""

import hashlib
from rational_knot_theory import RationalKnot, RationalCrossing
from rolfsen_database_updated import ROLFSEN_KNOTS

def calculate_modular_signature(knot: RationalKnot) -> str:
    """
    Calcula una firma criptográfica basada en la configuración modular del nudo.
    
    Estrategia:
    1. Normalizar la configuración para eliminar variaciones por rotación cíclica.
    2. Generar una representación canónica de los pares (o, u).
    3. Calcular hash SHA-256.
    """
    n = knot.n_crossings
    mod = 2 * n
    
    # Obtener pares originales
    pairs = [(c.over, c.under) for c in knot.crossings]
    
    # Generar todas las rotaciones cíclicas posibles
    # Shift k: x -> (x + k - 1) % mod + 1
    canonical_forms = []
    
    for k in range(mod):
        shifted_pairs = []
        for o, u in pairs:
            new_o = (o + k - 1) % mod + 1
            new_u = (u + k - 1) % mod + 1
            shifted_pairs.append((new_o, new_u))
        
        # Ordenar pares para tener una representación determinista del conjunto
        # Ordenamos por el primer elemento del par (over)
        shifted_pairs.sort()
        
        # Convertir a cadena
        s = "|".join([f"{o},{u}" for o, u in shifted_pairs])
        canonical_forms.append(s)
        
    # Elegir la representación léxicamente mínima como la canónica
    canonical_rep = min(canonical_forms)
    
    # Calcular hash
    return hashlib.sha256(canonical_rep.encode()).hexdigest()

def apply_cyclic_shift(knot: RationalKnot, k: int) -> RationalKnot:
    """Aplica un shift cíclico k a los índices del nudo."""
    n = knot.n_crossings
    mod = 2 * n
    new_crossings = []
    
    for c in knot.crossings:
        new_o = (c.over + k - 1) % mod + 1
        new_u = (c.under + k - 1) % mod + 1
        new_crossings.append(RationalCrossing(c.index, new_o, new_u, c.sign))
        
    return RationalKnot(new_crossings)

def apply_reversal(knot: RationalKnot) -> RationalKnot:
    """Invierte la dirección del recorrido: x -> 2n + 1 - x."""
    n = knot.n_crossings
    mod = 2 * n
    new_crossings = []
    
    for c in knot.crossings:
        new_o = mod + 1 - c.over
        new_u = mod + 1 - c.under
        new_crossings.append(RationalCrossing(c.index, new_o, new_u, c.sign))
        
    return RationalKnot(new_crossings)

def test_crypto_key():
    print("=" * 60)
    print("PRUEBA DE ROBUSTEZ DE CLAVE CRIPTOLÓGICA (FIRMA MODULAR)")
    print("=" * 60)
    
    test_knots = [f'8_{i}' for i in range(1, 22)]
    
    for knot_id in test_knots:
        if knot_id not in ROLFSEN_KNOTS:
            continue
            
        print(f"\nNudo {knot_id}:")
        info = ROLFSEN_KNOTS[knot_id]
        knot = RationalKnot.from_pairs(info.rational_config, info.signs)
        
        # 1. Firma Base
        sig_base = calculate_modular_signature(knot)
        print(f"  Firma Base:      {sig_base[:16]}...")
        
        # 2. Prueba de Rotación (Shifts)
        print("  Probando rotaciones cíclicas...")
        shifts_ok = True
        for k in range(1, 2 * knot.n_crossings):
            shifted_knot = apply_cyclic_shift(knot, k)
            sig_shifted = calculate_modular_signature(shifted_knot)
            if sig_shifted != sig_base:
                print(f"    [FAIL] Fallo en shift k={k}")
                shifts_ok = False
                break
        if shifts_ok:
            print("    [OK] Invariante bajo rotación")
            
        # 3. Prueba de Reversión
        reversed_knot = apply_reversal(knot)
        sig_reversed = calculate_modular_signature(reversed_knot)
        
        # Nota: La reversión podría generar una firma diferente si el nudo no es reversible
        # Pero para nudos invertibles (como todos los primos hasta 8 cruces), debería ser igual?
        # Ojo: La firma modular tal como la definí solo normaliza rotaciones, no reversiones.
        # Vamos a ver qué pasa.
        print(f"  Firma Reversión: {sig_reversed[:16]}...")
        if sig_reversed == sig_base:
            print("    [OK] Invariante bajo reversión")
        else:
            print("    [WARN] Cambia bajo reversión (Esperado si no normalizamos dirección)")
            
        # 4. Prueba de Espejo
        mirror_knot = knot.mirror()
        sig_mirror = calculate_modular_signature(mirror_knot)
        print(f"  Firma Espejo:    {sig_mirror[:16]}...")
        
        if sig_mirror == sig_base:
            print("    [OK] Invariante bajo espejo (Anfiqueiral detectado por firma)")
        else:
            print("    [INFO] Cambia bajo espejo (Quiral o firma sensible)")
            
        # 5. Firma Simétrica (Propuesta)
        # S_sym = min(Sig(K), Sig(K*))
        # Debería ser igual para K y K*
        sig_sym_K = min(sig_base, sig_mirror)
        
        mirror_of_mirror = mirror_knot.mirror()
        sig_mirror_base = calculate_modular_signature(mirror_knot)
        sig_mirror_mirror = calculate_modular_signature(mirror_of_mirror)
        sig_sym_Mirror = min(sig_mirror_base, sig_mirror_mirror)
        
        if sig_sym_K == sig_sym_Mirror:
             print("    [OK] Firma Simétrica Robusta (S_sym(K) == S_sym(K*))")
        else:
             print("    [FAIL] Error en Firma Simétrica")

if __name__ == "__main__":
    test_crypto_key()
