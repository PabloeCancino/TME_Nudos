from rational_knot_theory import RationalKnot

def get_knot_data(p, q):
    try:
        knot = RationalKnot.from_fraction(p, q)
        config = [(c.over, c.under) for c in knot.crossings]
        signs = [c.sign for c in knot.crossings]
        return config, signs
    except:
        return None, None

knots = {
    "7_2": (11, 2),
    "7_3": (13, 9),
    "7_4": (17, 5),
    "7_5": (17, 7),
    "7_6": (19, 11),
    "7_7": (21, 8)
}

for name, (p, q) in knots.items():
    config, signs = get_knot_data(p, q)
    print(f"{name} (K({p}/{q})):")
    print(f"  Config: {config}")
    print(f"  Signs:  {signs}")
