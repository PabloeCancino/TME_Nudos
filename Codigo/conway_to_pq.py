"""
Conway Notation to p/q Converter for Rational Knots

Based on research from KnotInfo and mathematical literature.

Conway notation represents the continued fraction coefficients:
Conway "a b c" = [a, b, c] = a + 1/(b + 1/c)
"""

def conway_to_pq(conway_notation: str) -> tuple:
    """
    Convert Conway notation to p/q fraction.
    
    Args:
        conway_notation: String like "52" or "3 1 3" representing coefficients
        
    Returns:
        (p, q) tuple
        
    Example:
        "52" -> [5, 2] -> 5 + 1/2 = 11/2
        "313" -> [3, 1, 3] -> 3 + 1/(1 + 1/3) = 3 + 1/(4/3) = 3 + 3/4 = 15/4
    """
    # Parse notation - could be "52" or "5 2" or "5,2"
    if ' ' in conway_notation:
        coeffs = [int(x) for x in conway_notation.split()]
    elif ',' in conway_notation:
        coeffs = [int(x) for x in conway_notation.split(',')]
    else:
        # Each digit is a coefficient
        coeffs = [int(c) for c in conway_notation]
    
    # Evaluate continued fraction from right to left
    # [a, b, c] = a + 1/(b + 1/c)
    if not coeffs:
        return (0, 1)
    
    # Start from the rightmost term
    p, q = coeffs[-1], 1
    
    # Work backwards
    for i in range(len(coeffs) - 2, -1, -1):
        # Current fraction is p/q
        # Next level: coeffs[i] + 1/(p/q) = coeffs[i] + q/p = (coeffs[i]*p + q)/p
        p, q = coeffs[i] * p + q, p
    
    return (p, q)

# Known Conway notations from research
CONWAY_NOTATIONS = {
    # From web search results
    '7_2': '52',      # 5 + 1/2 = 11/2
    '7_3': '43',      # 4 + 1/3 = 13/3
    '7_4': '313',     # 3 + 1/(1 + 1/3) = 3 + 3/4 = 15/4
    '7_5': '322',     # 3 + 1/(2 + 1/2) = 3 + 1/(5/2) = 3 + 2/5 = 17/5
    '8_1': '62',      # 6 + 1/2 = 13/2
    '8_2': '512',     # 5 + 1/(1 + 1/2) = 5 + 1/(3/2) = 5 + 2/3 = 17/3
    
    # Additional knots (need to verify)
    '5_2': '32',      # 3 + 1/2 = 7/2  (three-twist knot)
    '9_2': '532',     # 5 + 1/(3 + 1/2) = 5 + 1/(7/2) = 5 + 2/7 = 37/7
}

# Special cases - NOT 2-bridge knots
NON_2BRIDGE_KNOTS = {
    '6_1': 'Pretzel(5, -1, -1)',  # Stevedore knot - NOT a 2-bridge knot
    '7_6': 'Unknown',
    '7_7': 'Unknown',
}

if __name__ == "__main__":
    print("Conway Notation to p/q Conversion")
    print("=" * 60)
    
    for knot_id, conway in sorted(CONWAY_NOTATIONS.items()):
        p, q = conway_to_pq(conway)
        print(f"{knot_id}: Conway '{conway}' -> p/q = {p}/{q}")
    
    print("\n" + "=" * 60)
    print("Non-2-Bridge Knots (cannot be represented as p/q):")
    print("=" * 60)
    for knot_id, desc in sorted(NON_2BRIDGE_KNOTS.items()):
        print(f"{knot_id}: {desc}")
    
    print("\n" + "=" * 60)
    print("Verification:")
    print("=" * 60)
    
    # Verify some known cases
    test_cases = [
        ("3_1", "3", 3, 1),      # Trefoil
        ("4_1", "212", 5, 3),    # Figure-8
        ("5_1", "5", 5, 1),      # Cinquefoil
    ]
    
    for knot_id, conway, expected_p, expected_q in test_cases:
        p, q = conway_to_pq(conway)
        status = "✅" if (p == expected_p and q == expected_q) else "❌"
        print(f"{status} {knot_id}: Conway '{conway}' -> {p}/{q} (expected {expected_p}/{expected_q})")
