
import sys
import os
from typing import Dict, List

# Add current directory to path
sys.path.append(os.getcwd())

# Import the UPDATED database
try:
    from rolfsen_database_updated import ROLFSEN_KNOTS
except ImportError:
    print("Error: rolfsen_database_updated.py not found. Please run update_database.py first.")
    sys.exit(1)

from rational_knot_theory import RationalKnot, RationalCrossing
from alexander_polynomial import alexander_polynomial
from expected_polynomials import EXPECTED_POLYS
import sympy as sp

def verify_findings():
    print("==================================================")
    print("VERIFYING FINDINGS: Testing Updated Database")
    print("==================================================")
    
    results = {
        "match": [],
        "mismatch": [],
        "error": []
    }
    
    # Sort keys for consistent output
    sorted_keys = sorted(ROLFSEN_KNOTS.keys())
    
    for kid in sorted_keys:
        # Skip unknot for now or handle it
        if kid == "0_1": continue
        
        info = ROLFSEN_KNOTS[kid]
        
        print(f"Testing {kid} ({info.common_name})...", end=" ")
        
        if not info.rational_config:
            print("SKIPPED (No config)")
            continue
            
        try:
            # Reconstruct knot from stored config
            # The config is a list of (over, under) pairs
            # We need to reconstruct RationalCrossings
            
            # Check format of rational_config
            # It should be a list of tuples (over, under)
            # But wait, RationalKnot.from_pairs expects pairs and signs
            
            pairs = info.rational_config
            signs = info.signs
            
            if not pairs or not signs:
                 print("SKIPPED (Empty data)")
                 continue

            # Construct knot
            knot = RationalKnot.from_pairs(pairs, signs)
            
            # Calculate Polynomial
            poly = alexander_polynomial(knot)
            
            # Normalize and Compare
            # Expected poly is a list of coeffs
            expected_coeffs = EXPECTED_POLYS.get(kid)
            
            if not expected_coeffs:
                print(f"SKIPPED (No expected poly for {kid})")
                continue
                
            # Convert calculated poly to list of coeffs
            # Poly is a sympy Poly object or Expr
            if isinstance(poly, sp.Poly):
                coeffs = poly.all_coeffs()
            else:
                # It might be an expression
                poly = sp.Poly(poly)
                coeffs = poly.all_coeffs()
                
            # Normalize calculated coeffs (divide by max, handle sign)
            # Alexander poly is defined up to units (+- t^k)
            # We usually normalize so symmetric and positive leading?
            # Or just compare absolute values of coeffs?
            
            # Simple check: Check if expected coeffs (or their negative/reverse) match
            
            def normalize_list(lst):
                # Remove leading zeros
                while lst and lst[0] == 0: lst.pop(0)
                while lst and lst[-1] == 0: lst.pop()
                return lst
            
            c1 = normalize_list([int(c) for c in coeffs])
            c2 = normalize_list(expected_coeffs)
            
            # Check match
            match = False
            
            # Direct match
            if c1 == c2: match = True
            
            # Negative match
            if not match:
                c1_neg = [-x for x in c1]
                if c1_neg == c2: match = True
                
            # Reverse match (should be symmetric for knots, but good to check)
            if not match:
                if c1[::-1] == c2: match = True
                
            # Negative Reverse
            if not match:
                c1_neg_rev = [-x for x in c1[::-1]]
                if c1_neg_rev == c2: match = True
                
            if match:
                print("MATCH!")
                results["match"].append(kid)
            else:
                print(f"MISMATCH. Calc: {c1}, Exp: {c2}")
                results["mismatch"].append(kid)
                
        except Exception as e:
            print(f"ERROR: {e}")
            results["error"].append(kid)
            
    print("\n==================================================")
    print("SUMMARY")
    print("==================================================")
    print(f"Total Tested: {len(results['match']) + len(results['mismatch']) + len(results['error'])}")
    print(f"Matches: {len(results['match'])}")
    print(f"Mismatches: {len(results['mismatch'])}")
    print(f"Errors: {len(results['error'])}")
    
    if results["mismatch"]:
        print("\nMismatched Knots:")
        for k in results["mismatch"]:
            print(f"- {k}")
            
    if results["error"]:
        print("\nKnots with Errors:")
        for k in results["error"]:
            print(f"- {k}")

if __name__ == "__main__":
    verify_findings()
