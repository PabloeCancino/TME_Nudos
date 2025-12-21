import sympy as sp
import math
from typing import List, Tuple, Dict, Optional
from rational_knot_theory import RationalKnot
from burau_alexander import alexander_polynomial_from_braid
from expected_polynomials import EXPECTED_POLYS
from rolfsen_database import ROLFSEN_KNOTS

def get_determinant(coeffs: List[int]) -> int:
    """Calculate determinant |P(-1)| from coefficients."""
    val = 0
    for i, c in enumerate(coeffs):
        if i % 2 == 0:
            val += c
        else:
            val -= c
    return abs(val)

def check_match(poly: sp.Poly, target_coeffs: List[int]) -> bool:
    """Check if poly matches target coefficients (up to units/shift)."""
    if poly == 0: return False
    coeffs = poly.all_coeffs()
    
    # Normalize coeffs (remove leading zeros)
    while coeffs and coeffs[0] == 0: coeffs.pop(0)
    while coeffs and coeffs[-1] == 0: coeffs.pop()
    if not coeffs: return False
    
    # Target is also a list of coeffs.
    # We check if they match forward or backward, and +/-
    
    targets = [
        target_coeffs,
        [-c for c in target_coeffs],
        target_coeffs[::-1],
        [-c for c in target_coeffs[::-1]]
    ]
    
    return coeffs in targets

def reverse_engineer():
    print("=" * 80)
    print("  REVERSE ENGINEERING RATIONAL KNOTS (BURAU METHOD)")
    print("=" * 80)
    
    corrected_db = {}
    
    for kid, target_coeffs in EXPECTED_POLYS.items():
        print(f"Processing {kid}...", end="", flush=True)
        
        det = get_determinant(target_coeffs)
        if det == 0:
            print(" Det 0. Skipping.")
            continue
            
        p = det
        found = False
        
        # Search q
        # We search up to p.
        # For 2-bridge, q is odd? No. gcd(p,q)=1.
        # We also check -q (equivalent to p-q).
        
        # Optimization: q and p-q give same knot type (maybe mirror/inverse).
        # We check range(1, p).
        
        for q in range(1, p):
            if math.gcd(p, q) != 1:
                continue
                
            try:
                # 2. Calculate Alexander Polynomial via Minkus Formula
                # Formula: Delta(t) = Sum_{k=0}^{p-1} (-1)^k t^{S_k}
                # where S_k = Sum_{j=1}^k (-1)^{floor(j*q/p)}
                
                # Calculate S_k sequence
                S = [0] # S_0 = 0
                current_s = 0
                for j in range(1, p):
                    exponent = math.floor(j * q / p)
                    term = 1 if exponent % 2 == 0 else -1
                    current_s += term
                    S.append(current_s)
                    
                # Construct Polynomial
                # Poly = Sum (-1)^k t^{S_k}
                # We sum coefficients for each power
                coeffs_map = {}
                for k, s_val in enumerate(S):
                    sign = 1 if k % 2 == 0 else -1
                    coeffs_map[s_val] = coeffs_map.get(s_val, 0) + sign
                    
                # Convert to sympy Poly
                # Handle negative powers by shifting
                min_power = min(coeffs_map.keys())
                shift = -min_power if min_power < 0 else 0
                
                t = sp.Symbol('t')
                expr = 0
                for power, coeff in coeffs_map.items():
                    expr += coeff * t**(power + shift)
                    
                poly = sp.Poly(expr, t)
                
                if kid == "3_1" or kid == "4_1":
                    print(f"DEBUG {kid}: p={p}, q={q}")
                    print(f"DEBUG {kid}: S={S}")
                    print(f"DEBUG {kid}: Poly={poly.as_expr()}")
                    print(f"DEBUG {kid}: Coeffs={poly.all_coeffs()}")
                    print(f"DEBUG {kid}: Target={target_coeffs}")
                
                if check_match(poly, target_coeffs):
                    print(f" MATCH! p/q = {p}/{q}.")
                    corrected_db[kid] = {'p': p, 'q': q}
                    found = True
                    break
                    
            except Exception as e:
                # print(f"Err {p}/{q}: {e}")
                continue

    # Output results
    print("\n" + "=" * 80)
    print("  CORRECTED RATIONAL CONFIGURATIONS")
    print("=" * 80)
    
    print("CORRECTED_RATIONALS = {")
    for kid, data in corrected_db.items():
        print(f"    '{kid}': {{'p': {data['p']}, 'q': {data['q']}}},")
    print("}")

if __name__ == "__main__":
    reverse_engineer()
