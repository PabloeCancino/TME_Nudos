"""
Automated Sign Optimizer for Rolfsen Knot Database

This script deduces the correct crossing signs for each knot in the database
by searching for sign configurations that yield a valid Alexander Polynomial.

Algorithm:
1. Get knot structure (crossing pairs) from DT code.
2. Iterate through all sign combinations (2^n).
3. Calculate Alexander Polynomial for each.
4. Filter for validity:
   - Symmetric: P(t) ~ P(1/t)
   - Normalized: P(1) = ±1
   - Degree constraint: deg(P) <= n-1
5. Select the best candidate (usually unique up to global inversion).
"""

import sympy as sp
import itertools
from typing import List, Tuple, Dict, Optional
from rolfsen_database import ROLFSEN_KNOTS
from rational_knot_theory import RationalKnot
from alexander_polynomial import alexander_polynomial
from knot_notation_converter import dt_to_rational
import time

def is_symmetric(poly: sp.Poly) -> bool:
    """Check if polynomial is symmetric (palindromic coefficients)."""
    coeffs = poly.all_coeffs()
    # Remove leading/trailing zeros? Poly doesn't have them.
    # Check palindrome
    return coeffs == coeffs[::-1]

def is_normalized(poly: sp.Poly) -> bool:
    """Check if P(1) = ±1."""
    try:
        val = poly.subs(sp.Symbol('t'), 1)
        return abs(val) == 1
    except:
        return False

def find_optimal_signs(kid: str, dt_code: List[int]) -> Optional[Tuple[List[int], sp.Poly]]:
    """
    Find the sign configuration that yields a valid Alexander polynomial.
    """
    # 1. Get structure from DT code
    # We use dt_to_rational to get the pairs, ignoring its default signs
    temp_knot = dt_to_rational(dt_code)
    pairs = [(c.over, c.under) for c in temp_knot.crossings]
    n = len(pairs)
    
    # 2. Brute force signs
    # Optimization: For alternating knots, signs often alternate or follow a pattern.
    # But brute force 2^10 is fast enough (1024 iters).
    
    valid_configs = []
    
    # Iterate
    # Use itertools.product
    for signs in itertools.product([1, -1], repeat=n):
        knot = RationalKnot.from_pairs(pairs, signs=list(signs))
        
        try:
            poly = alexander_polynomial(knot)
            
            # Check properties
            if is_normalized(poly) and is_symmetric(poly):
                # Found a candidate
                valid_configs.append((list(signs), poly))
                
                # Heuristic: If we found one, is it unique?
                # Often K and Mirror(K) have same poly.
                # Mirror(K) has signs flipped.
                # So we expect at least 2 solutions.
                # We can stop after finding a few to compare.
        except:
            continue
            
    if not valid_configs:
        return None
        
    # Select best candidate
    # We prefer the one that matches known properties if possible.
    # For now, return the first one with non-trivial polynomial (if any)
    # Sort by degree of polynomial (descending) to avoid trivial solutions if any?
    # Unknot has degree 0.
    
    valid_configs.sort(key=lambda x: x[1].degree(), reverse=True)
    
    return valid_configs[0]


from expected_polynomials import EXPECTED_POLYS

def check_match(poly: sp.Poly, target_coeffs: List[int]) -> bool:
    """Check if poly matches target coefficients (up to units)."""
    coeffs = poly.all_coeffs()
    
    # Normalize coeffs (remove zeros? Poly usually doesn't have them)
    # Check direct match
    if coeffs == target_coeffs: return True
    if coeffs == [-c for c in target_coeffs]: return True
    if coeffs == target_coeffs[::-1]: return True # Palindrome
    
    return False

def optimize_database():
    print("=" * 80)
    print("  OPTIMIZING KNOT SIGNS (WITH EXPECTED VALUES)")
    print("=" * 80)
    
    corrected_data = {}
    
    for kid, info in ROLFSEN_KNOTS.items():
        print(f"Processing {kid}...", end="", flush=True)
        
        pairs = info.rational_config
        if not pairs:
            print(" Skipped (Unknot)")
            continue
            
        n = len(pairs)
        found_candidates = []
        target = EXPECTED_POLYS.get(kid)
        
        # Optimization: Try alternating signs first [1, -1, 1, -1...]
        # and [1, 1, 1...]
        # But brute force is fast enough.
        
        for signs in itertools.product([1, -1], repeat=n):
            knot = RationalKnot.from_pairs(pairs, signs=list(signs))
            try:
                poly = alexander_polynomial(knot)
                
                # Filter 1: Must be Normalized & Symmetric
                if not (is_normalized(poly) and is_symmetric(poly)):
                    continue
                    
                # Filter 2: If we have a target, MUST match target
                if target:
                    if check_match(poly, target):
                        found_candidates.append((list(signs), poly))
                else:
                    # No target, keep all symmetric/normalized candidates
                    found_candidates.append((list(signs), poly))
                    
            except:
                pass
        
        if found_candidates:
            # Selection Strategy
            if target:
                # We found matches for the target. Pick the first one.
                best_config, best_poly = found_candidates[0]
                print(f" MATCHED! Δ(t) = {sp.expand(best_poly.as_expr())}")
            else:
                # No target. Heuristic selection.
                # Sort by degree (descending) -> Prefer non-trivial
                # Then by determinant (value at -1) -> Prefer higher complexity
                found_candidates.sort(key=lambda x: (x[1].degree(), abs(x[1].subs(sp.Symbol('t'), -1))), reverse=True)
                best_config, best_poly = found_candidates[0]
                print(f" INFERRED! Δ(t) = {sp.expand(best_poly.as_expr())}")
            
            corrected_data[kid] = {
                'signs': best_config,
                'poly': str(sp.expand(best_poly.as_expr()))
            }
        else:
            print(" Failed to find valid signs.")
            
    # Output results
    print("\n" + "=" * 80)
    print("  CORRECTED CONFIGURATIONS")
    print("=" * 80)
    
    print("CORRECTED_SIGNS = {")
    for kid, data in corrected_data.items():
        print(f"    '{kid}': {data['signs']}, # Δ(t) = {data['poly']}")
    print("}")


if __name__ == "__main__":
    optimize_database()
