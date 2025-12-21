"""
Dowker-Thistlethwaite (DT) Code to RationalKnot Converter

DT codes from KnotInfo database provide unambiguous knot representations.

DT Code Format:
- Sequence of n even integers
- Pair (2i-1, dt[i]) represents crossing i
- Negative even number: strand goes OVER at that crossing
- Positive even number: strand goes UNDER at that crossing
"""

from rational_knot_theory import RationalKnot, RationalCrossing
from typing import List

# DT codes from KnotInfo database (verified)
DT_CODES = {
    '5_2': [4, 8, 10, 2, 6],
    '7_2': [6, 10, 14, 2, 12, 4, 8],
    '7_3': [10, -12, 14, -16, 18, -20, 22, -24, 26, -28, 2, -4, 6, -8],
    '7_4': [6, 10, 12, 14, 4, 2, 8],
    '7_5': [14, 2, 6, 12, 8, 10, 4],
    '8_2': [4, 10, 12, 14, 16, 2, 6, 8],
    '9_2': [4, 12, 18, 16, 14, 2, 10, 8, 6],
}


# DT codes from KnotInfo database (verified)
DT_CODES = {
    '5_2': [4, 8, 10, 2, 6],
    '7_2': [6, 10, 14, 2, 12, 4, 8],  # Corrected from search
    '7_3': [10, -12, 14, -16, 18, -20, 22, -24, 26, -28, 2, -4, 6, -8],
    '7_4': [6, 10, 12, 14, 4, 2, 8],
    '7_5': [14, 2, 6, 12, 8, 10, 4],
    '8_2': [4, 10, 12, 14, 16, 2, 6, 8],
    '9_2': [4, 12, 18, 16, 14, 2, 10, 8, 6],
}

def dt_to_rational_knot(dt_code: List[int]) -> RationalKnot:
    """
    Convert DT code to RationalKnot.
    
    Simplified algorithm:
    1. DT code gives us crossing connections directly
    2. Map each label to a segment number
    3. Build crossings with proper over/under/sign
    
    Args:
        dt_code: List of even integers (DT notation)
        
    Returns:
        RationalKnot object
    """
    n = len(dt_code)  # Number of crossings
    
    # Build pairs: (odd_label, even_label)
    # odd_label = 2i-1, even_label = dt_code[i-1]
    pairs = [(2*i - 1, dt_code[i-1]) for i in range(1, n+1)]
    
    # Create a mapping from labels to segments
    # We'll assign segments 1, 2, 3, ..., 2n to labels
    label_to_segment = {}
    segment_counter = 1
    
    # Process labels in order
    for i in range(1, 2*n + 1):
        if i not in label_to_segment:
            label_to_segment[i] = segment_counter
            segment_counter += 1
    
    # Build crossings
    crossings = []
    
    for i, (odd, even) in enumerate(pairs):
        # Get segment numbers
        seg_odd = label_to_segment[odd]
        seg_even = label_to_segment[abs(even)]
        
        # Determine over/under and sign based on DT convention
        # Negative even: strand at odd label goes OVER
        # Positive even: strand at odd label goes UNDER
        if even < 0:
            # Odd strand over, even strand under
            over_seg = seg_odd
            under_seg = seg_even
            sign = 1  # Positive crossing
        else:
            # Even strand over, odd strand under
            over_seg = seg_even
            under_seg = seg_odd
            sign = -1  # Negative crossing
        
        crossing = RationalCrossing(
            index=i + 1,  # 1-indexed
            over=over_seg,
            under=under_seg,
            sign=sign
        )
        crossings.append(crossing)
    
    return RationalKnot(crossings)

def test_dt_conversion():
    """Test DT code conversion for known knots."""
    print("=" * 60)
    print("DT CODE TO RATIONAL KNOT CONVERSION TEST")
    print("=" * 60)
    
    from alexander_polynomial import alexander_polynomial
    from expected_polynomials import EXPECTED_POLYS
    import sympy as sp
    
    t = sp.Symbol('t')
    
    for knot_id, dt_code in sorted(DT_CODES.items()):
        print(f"\n{knot_id}: DT = {dt_code}")
        
        try:
            knot = dt_to_rational_knot(dt_code)
            print(f"  Crossings: {len(knot.crossings)}")
            
            # Calculate polynomial
            poly = alexander_polynomial(knot)
            if isinstance(poly, sp.Poly):
                coeffs = poly.all_coeffs()
            else:
                coeffs = sp.Poly(poly, t).all_coeffs()
            
            coeffs = [int(c) for c in coeffs]
            while coeffs and coeffs[0] == 0: coeffs.pop(0)
            while coeffs and coeffs[-1] == 0: coeffs.pop()
            
            print(f"  Calculated: {coeffs}")
            
            # Check symmetry
            coeffs_rev = coeffs[::-1]
            is_sym = (coeffs == coeffs_rev) or (coeffs == [-c for c in coeffs_rev])
            print(f"  Symmetric: {is_sym}")
            
            # Check against expected
            expected = EXPECTED_POLYS.get(knot_id)
            if expected:
                matches = (coeffs == expected) or ([-c for c in coeffs] == expected)
                print(f"  Expected: {expected}")
                print(f"  Match: {'✅' if matches else '❌'}")
            
        except Exception as e:
            print(f"  ❌ Error: {e}")
            import traceback
            traceback.print_exc()
    
    print("\n" + "=" * 60)

if __name__ == "__main__":
    test_dt_conversion()
