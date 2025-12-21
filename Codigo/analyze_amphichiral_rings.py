"""
Ring-Theoretic Analysis of Amphichiral Knots

This script analyzes amphichiral knots using the modular ring framework
to understand why R(K) ≠ R(K*) for certain representations.

Key questions:
1. What are the modular sequences for amphichiral knots?
2. How do their signatures differ from chiral knots?
3. Can we find a canonical form where R(K) = R(K*)?
"""

import json
from typing import List, Tuple, Dict
from fractions import Fraction
import rolfsen_database as rdb
from ring_theoretic_invariants import ModularKnot, RingTheoreticInvariants


def load_amphichiral_dictionary():
    """Load the amphichiral knots dictionary."""
    with open("amphichiral_knots_dictionary.json", "r") as f:
        return json.load(f)


def analyze_amphichiral_knot(knot_id: str, amphichiral_data: Dict) -> Dict:
    """Detailed analysis of a single amphichiral knot."""
    
    print(f"\n{'='*100}")
    print(f"  ANÁLISIS: {knot_id}")
    print(f"{'='*100}")
    
    # Get knot from database
    rat_knot = rdb.get_knot(knot_id)
    if not rat_knot:
        print(f"⚠️  Nudo {knot_id} no encontrado en la base de datos")
        return None
    
    # Create modular knot
    mod_knot = ModularKnot.from_rational_knot(rat_knot)
    
    # Basic info
    print(f"\n### INFORMACIÓN BÁSICA ###")
    print(f"Nombre común: {amphichiral_data.get('common_name', 'N/A')}")
    print(f"Número de cruces: {mod_knot.n}")
    print(f"Anillo: ℤ/{mod_knot.ring_modulus}ℤ")
    print(f"Estado: Anfiqueiral (K ≅ K*)")
    
    # Calculate R(K) and R(K*)
    R_K = rat_knot.rational_product()
    K_mirror = rat_knot.mirror()
    R_K_mirror = K_mirror.rational_product()
    
    print(f"\n### INVARIANTE RACIONAL ###")
    print(f"R(K) = {R_K} ≈ {float(R_K):.6f}")
    print(f"R(K*) = {R_K_mirror} ≈ {float(R_K_mirror):.6f}")
    print(f"R(K) = R(K*)? {R_K == R_K_mirror}")
    
    if R_K != R_K_mirror:
        print(f"⚠️  FALSO POSITIVO: R(K) ≠ R(K*) pero el nudo es anfiqueiral")
        R_K_inverse = Fraction(1) / R_K
        print(f"R(K)⁻¹ = {R_K_inverse}")
        print(f"R(K*) = R(K)⁻¹? {R_K_mirror == R_K_inverse}")
    
    # Modular sequences
    S_K = RingTheoreticInvariants.modular_sequence(mod_knot)
    
    # Create mirror modular knot
    mod_knot_mirror = ModularKnot.from_rational_knot(K_mirror)
    S_K_mirror = RingTheoreticInvariants.modular_sequence(mod_knot_mirror)
    
    print(f"\n### SECUENCIAS MODULARES ###")
    print(f"S(K):  {S_K}")
    print(f"S(K*): {S_K_mirror}")
    print(f"S(K) = S(K*)? {S_K == S_K_mirror}")
    
    # Signatures
    sigma_K = RingTheoreticInvariants.modular_signature(mod_knot)
    sigma_K_mirror = RingTheoreticInvariants.modular_signature(mod_knot_mirror)
    
    print(f"\n### FIRMAS MODULARES ###")
    print(f"σ(K):  {sigma_K[:32]}...")
    print(f"σ(K*): {sigma_K_mirror[:32]}...")
    print(f"σ(K) = σ(K*)? {sigma_K == sigma_K_mirror}")
    
    # Ordered pairs
    P_K = RingTheoreticInvariants.ordered_pair_set(mod_knot)
    P_K_mirror = RingTheoreticInvariants.ordered_pair_set(mod_knot_mirror)
    
    print(f"\n### CONJUNTOS DE PARES ORDENADOS ###")
    print(f"P(K):  {sorted(P_K)}")
    print(f"P(K*): {sorted(P_K_mirror)}")
    
    # Check if P(K*) is the "inverse" of P(K)
    P_K_inverted = {(u, o) for o, u in P_K}
    print(f"\nP(K*) = {{(u,o) : (o,u) ∈ P(K)}}? {P_K_mirror == P_K_inverted}")
    
    # Cosets
    cosets_K = RingTheoreticInvariants.coset_decomposition(mod_knot)
    cosets_K_mirror = RingTheoreticInvariants.coset_decomposition(mod_knot_mirror)
    
    print(f"\n### DESCOMPOSICIÓN EN COSETS ###")
    print(f"K - Coset derecho:  {cosets_K['right']}")
    print(f"K - Coset izquierdo: {cosets_K['left']}")
    print(f"\nK* - Coset derecho:  {cosets_K_mirror['right']}")
    print(f"K* - Coset izquierdo: {cosets_K_mirror['left']}")
    
    # Check symmetry
    print(f"\n### ANÁLISIS DE SIMETRÍA ###")
    
    # For amphichiral knots, we expect some symmetry
    # Check if reversing the sequence gives the mirror
    S_K_reversed = list(reversed(S_K))
    print(f"S(K) invertida: {S_K_reversed}")
    print(f"S(K) invertida = S(K*)? {S_K_reversed == S_K_mirror}")
    
    # Check if there's a rotation that maps K to K*
    for shift in range(len(S_K)):
        S_K_rotated = S_K[shift:] + S_K[:shift]
        if S_K_rotated == S_K_mirror:
            print(f"✓ Rotación de {shift} posiciones: S(K) rotada = S(K*)")
            break
    
    # Store results
    results = {
        'knot_id': knot_id,
        'common_name': amphichiral_data.get('common_name', 'N/A'),
        'n_crossings': mod_knot.n,
        'ring_modulus': mod_knot.ring_modulus,
        'R_K': str(R_K),
        'R_K_mirror': str(R_K_mirror),
        'R_K_equals_R_K_mirror': R_K == R_K_mirror,
        'false_positive': R_K != R_K_mirror,
        'S_K': S_K,
        'S_K_mirror': S_K_mirror,
        'sigma_K': sigma_K,
        'sigma_K_mirror': sigma_K_mirror,
        'P_K': sorted(P_K),
        'P_K_mirror': sorted(P_K_mirror),
        'cosets_K': cosets_K,
        'cosets_K_mirror': cosets_K_mirror
    }
    
    return results


def analyze_all_amphichiral_knots():
    """Analyze all amphichiral knots in the dictionary."""
    
    print("="*100)
    print("  ANÁLISIS DE NUDOS ANFIQUIRALES - TEORÍA DE ANILLOS MODULARES")
    print("="*100)
    
    # Load dictionary
    amphichiral_dict = load_amphichiral_dictionary()
    amphichiral_knots = amphichiral_dict['amphichiral_knots']
    
    print(f"\nTotal de nudos anfiquirales en el diccionario: {len(amphichiral_knots)}")
    
    # Filter knots available in our database
    available_knots = []
    for knot_id, data in amphichiral_knots.items():
        if rdb.get_knot(knot_id):
            available_knots.append((knot_id, data))
    
    print(f"Nudos disponibles en la base de datos Rolfsen: {len(available_knots)}")
    
    # Analyze each knot
    results = {}
    false_positives = []
    true_amphichiral = []
    
    for knot_id, data in available_knots:
        result = analyze_amphichiral_knot(knot_id, data)
        if result:
            results[knot_id] = result
            
            if result['false_positive']:
                false_positives.append(knot_id)
            else:
                true_amphichiral.append(knot_id)
    
    # Summary
    print(f"\n{'='*100}")
    print(f"  RESUMEN")
    print(f"{'='*100}")
    
    print(f"\nNudos analizados: {len(results)}")
    print(f"R(K) = R(K*): {len(true_amphichiral)}")
    print(f"R(K) ≠ R(K*) (falsos positivos): {len(false_positives)}")
    
    if true_amphichiral:
        print(f"\n### Nudos con R(K) = R(K*) ###")
        for knot_id in true_amphichiral:
            print(f"  ✓ {knot_id}: {results[knot_id]['common_name']}")
    
    if false_positives:
        print(f"\n### Nudos con R(K) ≠ R(K*) (Falsos Positivos) ###")
        for knot_id in false_positives:
            r = results[knot_id]
            print(f"  ⚠️  {knot_id}: {r['common_name']}")
            print(f"      R(K) = {r['R_K']}, R(K*) = {r['R_K_mirror']}")
    
    # Comparative table
    print(f"\n{'='*100}")
    print(f"  TABLA COMPARATIVA")
    print(f"{'='*100}")
    
    print(f"\n{'Nudo':<8} {'Nombre':<20} {'n':<4} {'R(K)=R(K*)':<12} {'σ(K)=σ(K*)':<12} {'S(K)=S(K*)':<12}")
    print("-"*100)
    
    for knot_id in sorted(results.keys()):
        r = results[knot_id]
        name = r['common_name'][:18]
        n = r['n_crossings']
        R_eq = '✓' if r['R_K_equals_R_K_mirror'] else '✗'
        sigma_eq = '✓' if r['sigma_K'] == r['sigma_K_mirror'] else '✗'
        S_eq = '✓' if r['S_K'] == r['S_K_mirror'] else '✗'
        
        print(f"{knot_id:<8} {name:<20} {n:<4} {R_eq:<12} {sigma_eq:<12} {S_eq:<12}")
    
    # Save results
    output = {
        'metadata': {
            'total_analyzed': len(results),
            'true_amphichiral': len(true_amphichiral),
            'false_positives': len(false_positives)
        },
        'knots': results,
        'true_amphichiral_list': true_amphichiral,
        'false_positive_list': false_positives
    }
    
    with open("amphichiral_ring_analysis.json", "w") as f:
        json.dump(output, f, indent=2)
    
    print(f"\n{'='*100}")
    print(f"  Resultados guardados en: amphichiral_ring_analysis.json")
    print(f"{'='*100}")
    
    return results


def main():
    """Main analysis routine."""
    results = analyze_all_amphichiral_knots()
    
    print(f"\n{'='*100}")
    print(f"  CONCLUSIONES")
    print(f"{'='*100}")
    
    print("\n1. **Nudos anfiquirales con R(K) = R(K*)**:")
    print("   Estos tienen representaciones donde la simetría es evidente")
    print("   en el invariante racional.")
    
    print("\n2. **Nudos anfiquirales con R(K) ≠ R(K*) (Falsos Positivos)**:")
    print("   Estos requieren una representación canónica diferente.")
    print("   La simetría existe topológicamente pero no en la representación actual.")
    
    print("\n3. **Implicación para la teoría**:")
    print("   - R(K) depende de la representación específica")
    print("   - Se necesita una forma canónica para nudos anfiquirales")
    print("   - La firma modular σ(K) también depende de la representación")
    
    print("\n4. **Solución propuesta**:")
    print("   - Usar whitelist de nudos anfiquirales conocidos")
    print("   - Desarrollar algoritmo de forma canónica")
    print("   - Definir invariante simétrico R_sym(K) = min(R(K), R(K*))")


if __name__ == "__main__":
    main()
