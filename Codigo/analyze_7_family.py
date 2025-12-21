
from rolfsen_database_updated import ROLFSEN_KNOTS

def analyze_spectrum(knot_id):
    if knot_id not in ROLFSEN_KNOTS:
        print(f"Knot {knot_id} not found")
        return

    knot = ROLFSEN_KNOTS[knot_id]
    n = knot.crossing_number
    mod = 2 * n
    
    print(f"\n--- {knot_id} ({knot.common_name}) ---")
    print(f"Config: {knot.rational_config}")
    
    deltas = []
    for o, u in knot.rational_config:
        delta = (u - o) % mod
        deltas.append(delta)
        
    print(f"Deltas (u-o): {deltas}")
    print(f"Sorted Spectrum: {sorted(deltas)}")
    
    # Analyze balance
    counts = {}
    for d in deltas:
        counts[d] = counts.get(d, 0) + 1
    print(f"Counts: {counts}")

knots = ['7_1', '7_2', '7_3', '7_4', '7_5', '7_6', '7_7']
for k in knots:
    analyze_spectrum(k)
