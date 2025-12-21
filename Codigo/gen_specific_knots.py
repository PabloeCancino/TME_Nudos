from rational_knot_theory import RationalKnot

def print_config(p, q):
    try:
        knot = RationalKnot.from_fraction(p, q)
        print(f"K({p}/{q}): {[(c.over, c.under) for c in knot.crossings]}")
    except Exception as e:
        print(f"Error K({p}/{q}): {e}")

print_config(11, 2)
print_config(21, 8)
