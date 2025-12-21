"""
Enhanced Update Rolfsen Database with Comprehensive Search Strategy.

Improvements:
1. Tests CF with sign variations
2. Tests mirror images
3. Tests different closure orientations
4. Validates symmetry of Alexander polynomial
5. Creates list of problematic knots
"""

from rolfsen_database import ROLFSEN_KNOTS
from rational_knot_theory import RationalKnot
from alexander_polynomial import alexander_polynomial
from expected_polynomials import EXPECTED_POLYS
import sympy as sp
import numpy as np
from typing import List, Tuple, Optional

CORRECTED_RATIONALS = {
    # Verified values (already correct)
    '3_1': {'p': 3, 'q': 1},      # Conway: 3
    '4_1': {'p': 5, 'q': 3},      # Conway: 212 (verified correct)
    '5_1': {'p': 5, 'q': 1},      # Conway: 5
    '6_2': {'p': 11, 'q': 3},     # Conway: 341 (verified correct)
    '6_3': {'p': 13, 'q': 5},     # Conway: 232 (verified correct)
    '7_1': {'p': 7, 'q': 1},      # Conway: 7
    '9_1': {'p': 9, 'q': 1},      # Conway: 9
    
    # Corrected values from Conway notation research
    '5_2': {'p': 7, 'q': 2},      # Conway: 32 -> 7/2 (was 7/3)
    '7_2': {'p': 11, 'q': 2},     # Conway: 52 -> 11/2 (was 25/9)
    '7_3': {'p': 13, 'q': 3},     # Conway: 43 -> 13/3 (correct)
    '7_4': {'p': 15, 'q': 4},     # Conway: 313 -> 15/4 (was 29/9)
    '7_5': {'p': 17, 'q': 5},     # Conway: 322 -> 17/5 (correct)
    '8_1': {'p': 13, 'q': 2},     # Conway: 62 -> 13/2 (was 13/7)
    '8_2': {'p': 17, 'q': 3},     # Conway: 512 -> 17/3 (was 13/7)
    '9_2': {'p': 37, 'q': 7},     # Conway: 532 -> 37/7 (was 49/11)
    
    # NOTE: The following are NOT 2-bridge/rational knots:
    # '6_1': Stevedore knot = Pretzel(5, -1, -1) - cannot be represented as p/q
    # '7_6': Unknown type - needs further research
    # '7_7': Unknown type - needs further research
}

t = sp.Symbol('t')

def get_coeffs(knot: RationalKnot) -> List[int]:
    """Extract polynomial coefficients."""
    try:
        poly = alexander_polynomial(knot)
        if isinstance(poly, sp.Poly):
            coeffs = poly.all_coeffs()
        else:
            coeffs = sp.Poly(poly, t).all_coeffs()
        
        coeffs = [int(c) for c in coeffs]
        while coeffs and coeffs[0] == 0: coeffs.pop(0)
        while coeffs and coeffs[-1] == 0: coeffs.pop()
        return coeffs if coeffs else [0]
    except:
        return []

def is_symmetric(coeffs: List[int]) -> bool:
    """Check if polynomial coefficients are symmetric."""
    if not coeffs:
        return False
    coeffs_rev = coeffs[::-1]
    return (coeffs == coeffs_rev) or (coeffs == [-c for c in coeffs_rev])

def check_match(coeffs: List[int], expected: List[int]) -> bool:
    """Check if coefficients match expected (with normalization)."""
    if not coeffs or not expected:
        return False
    
    c1 = [c for c in coeffs]
    c2 = [c for c in expected]
    
    if c1 == c2: return True
    if [-x for x in c1] == c2: return True
    if c1[::-1] == c2: return True
    if [-x for x in c1[::-1]] == c2: return True
    return False

def generate_cf_variations(p: int, q: int) -> List[Tuple[str, List[int]]]:
    """
    Generate variations of continued fraction expansion.
    
    Returns list of (description, cf) tuples.
    """
    variations = []
    
    # Base CF
    cf_base = RationalKnot._fraction_to_cf(p, q)
    variations.append(("base", cf_base))
    
    # Expanded CF (change parity)
    if cf_base[-1] > 1:
        cf_expanded = cf_base[:-1] + [cf_base[-1]-1, 1]
        variations.append(("expanded", cf_expanded))
    
    # Negative last term (for mirror image)
    cf_neg_last = cf_base[:-1] + [-cf_base[-1]]
    variations.append(("neg_last", cf_neg_last))
    
    # All negative (full mirror)
    cf_all_neg = [-a for a in cf_base]
    variations.append(("all_neg", cf_all_neg))
    
    # Alternating signs starting negative
    cf_alt_neg = [(-1)**(i+1) * abs(a) for i, a in enumerate(cf_base)]
    variations.append(("alt_neg", cf_alt_neg))
    
    return variations

def create_knot_from_braid(cf: List[int], n_strands: int, closure: str, 
                           gen_pattern: str) -> Optional[RationalKnot]:
    """
    Create knot from CF using specified braid parameters.
    
    gen_pattern: "12" for alternating 1,2 or "21" for alternating 2,1
    """
    from braid_conversion import braid_to_rational_knot
    
    try:
        word = []
        for i, a in enumerate(cf):
            if gen_pattern == "12":
                gen = 1 if i % 2 == 0 else 2
            else:  # "21"
                gen = 2 if i % 2 == 0 else 1
            
            # Sign: positive for even index, negative for odd
            sign = 1 if i % 2 == 0 else -1
            word.append((gen, sign * a))
        
        return braid_to_rational_knot(word, n_strands=n_strands, closure_type=closure)
    except:
        return None

def exhaustive_search(p: int, q: int, kid: str) -> Tuple[Optional[RationalKnot], str]:
    """
    Exhaustive search for correct knot configuration.
    
    Returns (best_knot, method_description)
    """
    expected = EXPECTED_POLYS.get(kid)
    best_knot = None
    best_method = "none"
    best_score = -1
    
    # Generate CF variations
    cf_variations = generate_cf_variations(p, q)
    
    # Test all combinations
    test_configs = [
        (3, 'standard', '12', '3-braid-std-12'),
        (3, 'standard', '21', '3-braid-std-21'),
        (4, 'plat', '12', '4-plat-12'),
        (4, 'plat', '21', '4-plat-21'),
    ]
    
    for cf_desc, cf in cf_variations:
        for n_strands, closure, gen_pattern, config_desc in test_configs:
            knot = create_knot_from_braid(cf, n_strands, closure, gen_pattern)
            if knot is None:
                continue
            
            coeffs = get_coeffs(knot)
            if not coeffs:
                continue
            
            # Score this candidate
            score = 0
            
            # Check symmetry (required for knots)
            if is_symmetric(coeffs):
                score += 10
            
            # Check match with expected
            if expected and check_match(coeffs, expected):
                score += 100
            
            # Prefer simpler configurations
            if cf_desc == "base":
                score += 1
            
            if score > best_score:
                best_score = score
                best_knot = knot
                best_method = f"{cf_desc}/{config_desc}"
                
                # If we have perfect match, stop searching
                if score >= 110:  # symmetric + match
                    return best_knot, best_method
    
    return best_knot, best_method

def update_database():
    """
    Update database with enhanced search strategy.
    """
    print("=" * 80)
    print("ENHANCED DATABASE UPDATE - Comprehensive Search Strategy")
    print("=" * 80)
    
    lines = []
    lines.append("ROLFSEN_KNOTS = {")
    
    all_keys = sorted(list(set(list(ROLFSEN_KNOTS.keys()) + list(CORRECTED_RATIONALS.keys()))))
    if "0_1" in all_keys:
        all_keys.remove("0_1")
        all_keys.insert(0, "0_1")
    
    # Track problematic knots
    problematic_knots = []
    successful_knots = []
    
    for kid in all_keys:
        info = ROLFSEN_KNOTS.get(kid)
        
        # Determine p, q
        p, q = 0, 0
        if kid in CORRECTED_RATIONALS:
            p, q = CORRECTED_RATIONALS[kid]['p'], CORRECTED_RATIONALS[kid]['q']
        
        if p == 0:
            # Keep existing
            if info:
                rational_config_str = str(info.rational_config)
                signs_str = str(info.signs)
                line = f'    "{kid}": KnotInfo(rolfsen_id="{kid}", common_name="{info.common_name}", rational_config={rational_config_str}, signs={signs_str}, is_chiral={info.is_chiral}, is_alternating={info.is_alternating}, crossing_number={info.crossing_number}, description="{info.description}"),'
                lines.append(line)
            continue
        
        print(f"\nProcessing {kid} ({p}/{q})...")
        
        # Exhaustive search
        found_knot, method = exhaustive_search(p, q, kid)
        
        if found_knot is None:
            print(f"  ❌ FAILED: No valid configuration found")
            problematic_knots.append({
                'id': kid,
                'p': p,
                'q': q,
                'reason': 'No valid configuration found'
            })
            continue
        
        # Validate the knot
        coeffs = get_coeffs(found_knot)
        is_sym = is_symmetric(coeffs)
        expected = EXPECTED_POLYS.get(kid)
        matches = check_match(coeffs, expected) if expected else None
        
        # Report results
        status = "✅" if (is_sym and (matches or not expected)) else "⚠️"
        print(f"  {status} Method: {method}")
        print(f"     Coeffs: {coeffs}")
        print(f"     Symmetric: {is_sym}")
        if expected:
            print(f"     Matches expected: {matches}")
        
        if not is_sym or (expected and not matches):
            problematic_knots.append({
                'id': kid,
                'p': p,
                'q': q,
                'method': method,
                'coeffs': coeffs,
                'symmetric': is_sym,
                'matches': matches,
                'reason': 'Non-symmetric' if not is_sym else 'Does not match expected'
            })
        else:
            successful_knots.append(kid)
        
        # Extract data
        pairs = [(c.over, c.under) for c in found_knot.crossings]
        signs = [c.sign for c in found_knot.crossings]
        
        rational_config_str = str(pairs)
        signs_str = str(signs)
        
        line = f'    "{kid}": KnotInfo(rolfsen_id="{kid}", common_name="{info.common_name}", rational_config={rational_config_str}, signs={signs_str}, is_chiral={info.is_chiral}, is_alternating={info.is_alternating}, crossing_number={info.crossing_number}, description="{info.description}"),'
        lines.append(line)
    
    lines.append("}")
    
    # Write database file
    with open("rolfsen_database.py", "r") as f:
        original_content = f.read()
    
    parts = original_content.split("ROLFSEN_KNOTS: Dict[str, KnotInfo] = {")
    if len(parts) < 2:
        parts = original_content.split("ROLFSEN_KNOTS = {")
    
    header = parts[0]
    new_content = header + "ROLFSEN_KNOTS: Dict[str, KnotInfo] = {\n" + "\n".join(lines[1:])
    
    with open("rolfsen_database_updated.py", "w") as f:
        f.write(new_content)
    
    # Write problematic knots report
    with open("problematic_knots_report.txt", "w") as f:
        f.write("=" * 80 + "\n")
        f.write("PROBLEMATIC KNOTS REPORT\n")
        f.write("=" * 80 + "\n\n")
        f.write(f"Total knots processed: {len(all_keys)}\n")
        f.write(f"Successful: {len(successful_knots)}\n")
        f.write(f"Problematic: {len(problematic_knots)}\n\n")
        
        if problematic_knots:
            f.write("PROBLEMATIC KNOTS:\n")
            f.write("-" * 80 + "\n")
            for knot in problematic_knots:
                f.write(f"\nKnot: {knot['id']} (p={knot['p']}, q={knot['q']})\n")
                f.write(f"  Reason: {knot['reason']}\n")
                if 'method' in knot:
                    f.write(f"  Method tried: {knot['method']}\n")
                if 'coeffs' in knot:
                    f.write(f"  Coefficients: {knot['coeffs']}\n")
                    f.write(f"  Symmetric: {knot['symmetric']}\n")
                    if 'matches' in knot:
                        f.write(f"  Matches expected: {knot['matches']}\n")
        
        f.write("\n" + "=" * 80 + "\n")
        f.write("SUCCESSFUL KNOTS:\n")
        f.write("-" * 80 + "\n")
        for kid in successful_knots:
            f.write(f"  {kid}\n")
    
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Created: rolfsen_database_updated.py")
    print(f"Created: problematic_knots_report.txt")
    print(f"Successful: {len(successful_knots)}/{len([k for k in all_keys if k in CORRECTED_RATIONALS])}")
    print(f"Problematic: {len(problematic_knots)}")
    print("=" * 80)

if __name__ == "__main__":
    update_database()
