
from rolfsen_database import ROLFSEN_KNOTS as ORIGINAL_DB
from rolfsen_database_updated import ROLFSEN_KNOTS as UPDATED_DB, KnotInfo
import inspect

# Valid 7-crossing knots generated previously
VALID_7_KNOTS = {
    "7_1": KnotInfo(rolfsen_id="7_1", common_name="Septafoil", rational_config=[(14, 7), (6, 13), (12, 5), (4, 11), (10, 3), (2, 9), (8, 1)], signs=[1, 1, 1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="Septafoil knot (torus knot T(2,7))"),
    "7_2": KnotInfo(rolfsen_id="7_2", common_name="7_2 Knot", rational_config=[(14, 9), (8, 13), (12, 7), (6, 11), (10, 5), (4, 1), (2, 3)], signs=[1, 1, 1, 1, 1, -1, -1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_2 knot (K(11/2))"),
    "7_3": KnotInfo(rolfsen_id="7_3", common_name="7_3 Knot", rational_config=[(14, 9), (8, 1), (2, 7), (6, 13), (12, 5), (4, 11), (10, 3)], signs=[1, -1, -1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_3 knot (K(13/9))"),
    "7_4": KnotInfo(rolfsen_id="7_4", common_name="7_4 Knot", rational_config=[(14, 9), (8, 13), (12, 7), (6, 1), (2, 5), (4, 11), (10, 3)], signs=[1, 1, 1, -1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_4 knot (K(17/5))"),
    "7_5": KnotInfo(rolfsen_id="7_5", common_name="7_5 Knot", rational_config=[(14, 7), (6, 13), (12, 1), (2, 11), (10, 5), (4, 9), (8, 3)], signs=[1, 1, -1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_5 knot (K(17/7))"),
    "7_6": KnotInfo(rolfsen_id="7_6", common_name="7_6 Knot", rational_config=[(14, 9), (8, 1), (2, 13), (12, 3), (4, 7), (6, 11), (10, 5)], signs=[1, -1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_6 knot (K(19/11))"),
    "7_7": KnotInfo(rolfsen_id="7_7", common_name="7_7 Knot", rational_config=[(14, 5), (6, 13), (12, 1), (2, 7), (8, 11), (10, 3), (4, 9)], signs=[1, 1, -1, 1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=7, description="7_7 knot (K(21/8))"),
}

def format_knot(key, knot):
    return f'    "{key}": KnotInfo(rolfsen_id="{knot.rolfsen_id}", common_name="{knot.common_name}", rational_config={knot.rational_config}, signs={knot.signs}, is_chiral={knot.is_chiral}, is_alternating={knot.is_alternating}, crossing_number={knot.crossing_number}, description="{knot.description}"),\n'

# Read the updated file
with open('rolfsen_database_updated.py', 'r') as f:
    lines = f.readlines()

# Find insertion point (after 4_1)
insert_idx = -1
for i, line in enumerate(lines):
    if '"4_1":' in line:
        # Find the end of this entry (it might be multi-line, but here it's one line)
        insert_idx = i + 1
        break

if insert_idx == -1:
    print("Error: Could not find 4_1 entry")
    exit(1)

# Construct missing entries
missing_lines = []

# 5_i and 6_i from ORIGINAL
knots_to_restore = ['5_1', '5_2', '6_1', '6_2', '6_3']
for k in knots_to_restore:
    if k in ORIGINAL_DB:
        missing_lines.append(format_knot(k, ORIGINAL_DB[k]))

# 7_i from VALID_7_KNOTS
for k in sorted(VALID_7_KNOTS.keys()):
    missing_lines.append(format_knot(k, VALID_7_KNOTS[k]))

# 8_1 to 8_14 from ORIGINAL
for i in range(1, 15):
    k = f"8_{i}"
    if k in ORIGINAL_DB:
        missing_lines.append(format_knot(k, ORIGINAL_DB[k]))

# Insert
new_lines = lines[:insert_idx] + missing_lines + lines[insert_idx:]

# Write back
with open('rolfsen_database_updated.py', 'w') as f:
    f.writelines(new_lines)

print("Database restored successfully!")
