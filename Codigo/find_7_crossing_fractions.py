"""
Script to find fractions p/q that generate 7-crossing knots.
Based on the property that crossing number of K(p/q) is sum(CF(p/q)).
"""

from rational_knot_theory import RationalKnot

def get_cf(p, q):
    cf = []
    while q != 0:
        a = p // q
        cf.append(a)
        p, q = q, p % q
    return cf

def find_7_crossing_knots():
    print("Searching for 2-bridge knots with crossing number 7...")
    
    found = []
    
    # Iterate p (always odd for knots)
    for p in range(3, 100, 2):
        for q in range(1, p):
            if q % 2 == 0: continue # q is usually odd? No, p is odd. q can be anything coprime.
            # Actually for Schubert form, p is odd.
            
            # Check gcd
            def gcd(a, b):
                while b: a, b = b, a % b
                return a
            
            if gcd(p, q) != 1: continue
            
            cf = get_cf(p, q)
            # Crossing number is sum of a_i
            cn = sum(cf)
            
            if cn == 7:
                # Found a candidate
                # Generate knot to verify
                try:
                    knot = RationalKnot.from_fraction(p, q)
                    if knot.n_crossings == 7:
                        found.append((p, q, cf, knot))
                        print(f"Found K({p}/{q}): CF={cf}, Config={[(c.over, c.under) for c in knot.crossings]}")
                except Exception as e:
                    pass
                    
    return found

if __name__ == "__main__":
    find_7_crossing_knots()
