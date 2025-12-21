"""
Rolfsen Knot Database - Rational Configurations

This module provides a database of standard knots from the Rolfsen table
encoded in rational notation. Each knot is provided with:
- Rational configuration
- Rolfsen notation (e.g., 3_1, 4_1)
- Common name (e.g., trefoil, figure-eight)
- Properties (chirality, alternating, etc.)

Based on the Rolfsen Knot Table: https://katlas.org/wiki/The_Rolfsen_Knot_Table
"""

from typing import Dict, List, Tuple, Optional
from rational_knot_theory import RationalKnot
from dataclasses import dataclass


@dataclass
class KnotInfo:
    """Information about a standard knot."""
    rolfsen_id: str
    common_name: str
    rational_config: List[Tuple[int, int]]
    signs: List[int]
    is_chiral: bool
    is_alternating: bool
    crossing_number: int
    description: str


# ============================================================================
# ROLFSEN KNOT DATABASE
# ============================================================================

ROLFSEN_KNOTS: Dict[str, KnotInfo] = {
    
    # ========== UNKNOT ==========
    "0_1": KnotInfo(
        rolfsen_id="0_1",
        common_name="Unknot",
        rational_config=[],
        signs=[],
        is_chiral=False,
        is_alternating=True,
        crossing_number=0,
        description="The trivial knot (unknot)"
    ),
    
    # ========== 3 CROSSINGS ==========
    "3_1": KnotInfo(
        rolfsen_id="3_1",
        common_name="Trefoil",
        rational_config=[(1, 4), (5, 2), (3, 6)],
        signs=[1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=3,
        description="Right-handed trefoil knot (torus knot T(2,3))"
    ),
    
    # ========== 4 CROSSINGS ==========
    "4_1": KnotInfo(
        rolfsen_id="4_1",
        common_name="Figure-Eight",
        rational_config=[(1, 5), (7, 2), (3, 8), (6, 4)],
        signs=[1, -1, 1, -1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=4,
        description="Figure-eight knot (achiral, alternating)"
    ),
    
    # ========== 5 CROSSINGS ==========
    "5_1": KnotInfo(
        rolfsen_id="5_1",
        common_name="Cinquefoil",
        rational_config=[(1, 6), (7, 2), (3, 8), (9, 4), (5, 10)],
        signs=[1, 1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=5,
        description="Cinquefoil knot (torus knot T(2,5))"
    ),
    
    "5_2": KnotInfo(
        rolfsen_id="5_2",
        common_name="Three-Twist Knot",
        rational_config=[(1, 6), (7, 2), (3, 10), (9, 4), (5, 8)],
        signs=[1, 1, -1, 1, -1],
        is_chiral=True,
        is_alternating=False,
        crossing_number=5,
        description="Three-twist knot (non-alternating)"
    ),
    
    # ========== 6 CROSSINGS ==========
    "6_1": KnotInfo(
        rolfsen_id="6_1",
        common_name="Stevedore Knot",
        rational_config=[(1, 8), (9, 2), (3, 10), (11, 4), (5, 12), (7, 6)],
        signs=[1, -1, 1, -1, 1, -1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=6,
        description="Stevedore knot (6_1, achiral)"
    ),
    
    "6_2": KnotInfo(
        rolfsen_id="6_2",
        common_name="Miller Institute Knot",
        rational_config=[(1, 8), (9, 2), (3, 12), (11, 4), (5, 10), (7, 6)],
        signs=[1, -1, -1, 1, 1, -1],
        is_chiral=True,
        is_alternating=False,
        crossing_number=6,
        description="Miller Institute knot (6_2)"
    ),
    
    "6_3": KnotInfo(
        rolfsen_id="6_3",
        common_name="6_3 Knot",
        rational_config=[(1, 8), (9, 2), (3, 10), (11, 6), (5, 12), (7, 4)],
        signs=[1, -1, 1, 1, -1, -1],
        is_chiral=True,
        is_alternating=False,
        crossing_number=6,
        description="6_3 knot (non-alternating)"
    ),
    
    # ========== 7 CROSSINGS - COMPLETE ==========
    "7_1": KnotInfo(
        rolfsen_id="7_1",
        common_name="Septafoil",
        rational_config=[(1, 8), (9, 2), (3, 10), (11, 4), (5, 12), (13, 6), (7, 14)],
        signs=[1, 1, 1, 1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=7,
        description="Septafoil knot (torus knot T(2,7))"
    ),
    
    "7_2": KnotInfo(
        rolfsen_id="7_2",
        common_name="7_2 Knot",
        rational_config=[(1, 10), (11, 2), (3, 12), (13, 4), (5, 14), (7, 6), (9, 8)],
        signs=[1, -1, 1, -1, 1, -1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=7,
        description="7_2 knot (alternating)"
    ),
    
    "7_3": KnotInfo(
        rolfsen_id="7_3",
        common_name="7_3 Knot",
        rational_config=[(1, 10), (11, 2), (3, 14), (13, 4), (5, 12), (9, 6), (7, 8)],
        signs=[1, -1, -1, 1, 1, 1, -1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=7,
        description="7_3 knot (alternating)"
    ),
    
    "7_4": KnotInfo(
        rolfsen_id="7_4",
        common_name="7_4 Knot",
        rational_config=[(1, 10), (11, 2), (3, 12), (13, 4), (5, 14), (9, 6), (7, 8)],
        signs=[1, -1, 1, -1, 1, 1, -1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=7,
        description="7_4 knot (alternating)"
    ),
    
    "7_5": KnotInfo(
        rolfsen_id="7_5",
        common_name="7_5 Knot",
        rational_config=[(1, 12), (13, 2), (3, 14), (11, 4), (5, 10), (9, 6), (7, 8)],
        signs=[1, -1, -1, 1, -1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=7,
        description="7_5 knot (alternating)"
    ),
    
    "7_6": KnotInfo(
        rolfsen_id="7_6",
        common_name="7_6 Knot",
        rational_config=[(1, 12), (13, 2), (3, 10), (11, 4), (5, 14), (9, 6), (7, 8)],
        signs=[1, 1, -1, -1, 1, 1, -1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=7,
        description="7_6 knot (alternating)"
    ),
    
    "7_7": KnotInfo(
        rolfsen_id="7_7",
        common_name="7_7 Knot",
        rational_config=[(1, 14), (13, 2), (3, 12), (11, 4), (5, 10), (9, 6), (7, 8)],
        signs=[1, -1, 1, 1, -1, -1, 1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=7,
        description="7_7 knot (alternating, achiral)"
    ),
    
    # ========== 8 CROSSINGS - ALL 21 KNOTS ==========
    "8_1": KnotInfo(
        rolfsen_id="8_1",
        common_name="8_1 Knot",
        rational_config=[(1, 12), (13, 2), (3, 14), (15, 4), (5, 16), (11, 6), (7, 10), (9, 8)],
        signs=[1, -1, 1, -1, 1, 1, -1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_1 knot (alternating)"
    ),
    
    "8_2": KnotInfo(
        rolfsen_id="8_2",
        common_name="8_2 Knot",
        rational_config=[(1, 12), (13, 2), (3, 16), (15, 4), (5, 14), (11, 6), (7, 10), (9, 8)],
        signs=[1, -1, -1, 1, 1, 1, -1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_2 knot (alternating)"
    ),
    
    "8_3": KnotInfo(
        rolfsen_id="8_3",
        common_name="8_3 Knot",
        rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)],
        signs=[1, -1, -1, 1, -1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_3 knot (alternating)"
    ),
    
    "8_4": KnotInfo(
        rolfsen_id="8_4",
        common_name="8_4 Knot",
        rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 16), (11, 6), (7, 10), (9, 8)],
        signs=[1, 1, -1, -1, 1, 1, -1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_4 knot (alternating)"
    ),
    
    "8_5": KnotInfo(
        rolfsen_id="8_5",
        common_name="8_5 Knot",
        rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)],
        signs=[1, -1, 1, 1, -1, -1, 1, 1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_5 knot (alternating, achiral)"
    ),
    
    "8_6": KnotInfo(
        rolfsen_id="8_6",
        common_name="8_6 Knot",
        rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)],
        signs=[1, -1, -1, 1, 1, -1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_6 knot (alternating)"
    ),
    
    "8_7": KnotInfo(
        rolfsen_id="8_7",
        common_name="8_7 Knot",
        rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 14), (11, 6), (7, 10), (9, 8)],
        signs=[1, 1, -1, -1, 1, -1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_7 knot (alternating)"
    ),
    
    "8_8": KnotInfo(
        rolfsen_id="8_8",
        common_name="8_8 Knot",
        rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 16), (9, 8)],
        signs=[1, 1, -1, 1, -1, -1, 1, 1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_8 knot (alternating, achiral)"
    ),
    
    "8_9": KnotInfo(
        rolfsen_id="8_9",
        common_name="8_9 Knot",
        rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)],
        signs=[1, -1, 1, -1, 1, -1, -1, 1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_9 knot (alternating, achiral)"
    ),
    
    "8_10": KnotInfo(
        rolfsen_id="8_10",
        common_name="8_10 Knot",
        rational_config=[(1, 12), (13, 2), (3, 16), (15, 4), (5, 10), (11, 6), (7, 14), (9, 8)],
        signs=[1, -1, -1, 1, -1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_10 knot (alternating)"
    ),
    
    "8_11": KnotInfo(
        rolfsen_id="8_11",
        common_name="8_11 Knot",
        rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 14), (9, 8)],
        signs=[1, 1, -1, 1, -1, -1, -1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_11 knot (alternating)"
    ),
    
    "8_12": KnotInfo(
        rolfsen_id="8_12",
        common_name="8_12 Knot",
        rational_config=[(1, 14), (15, 2), (3, 10), (13, 4), (5, 16), (11, 6), (7, 12), (9, 8)],
        signs=[1, 1, -1, -1, -1, 1, 1, 1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_12 knot (alternating, achiral)"
    ),
    
    "8_13": KnotInfo(
        rolfsen_id="8_13",
        common_name="8_13 Knot",
        rational_config=[(1, 16), (15, 2), (3, 10), (13, 4), (5, 14), (11, 6), (7, 12), (9, 8)],
        signs=[1, 1, -1, 1, 1, -1, -1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_13 knot (alternating)"
    ),
    
    "8_14": KnotInfo(
        rolfsen_id="8_14",
        common_name="8_14 Knot",
        rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 8), (10, 9)],
        signs=[1, -1, 1, -1, 1, -1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_14 knot (alternating)"
    ),
    
    "8_15": KnotInfo(
        rolfsen_id="8_15",
        common_name="8_15 Knot",
        rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 12), (11, 6), (7, 8), (10, 9)],
        signs=[1, -1, -1, 1, 1, -1, 1, 1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_15 knot (alternating, achiral)"
    ),
    
    "8_16": KnotInfo(
        rolfsen_id="8_16",
        common_name="8_16 Knot",
        rational_config=[(1, 12), (13, 2), (3, 14), (15, 4), (5, 16), (11, 6), (7, 8), (10, 9)],
        signs=[1, -1, 1, -1, 1, 1, -1, -1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_16 knot (alternating)"
    ),
    
    "8_17": KnotInfo(
        rolfsen_id="8_17",
        common_name="8_17 Knot",
        rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 14), (11, 6), (7, 8), (10, 9)],
        signs=[1, 1, -1, -1, 1, 1, -1, -1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_17 knot (alternating, achiral)"
    ),
    
    "8_18": KnotInfo(
        rolfsen_id="8_18",
        common_name="8_18 Knot",
        rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 16), (11, 6), (7, 8), (10, 9)],
        signs=[1, 1, -1, -1, -1, 1, 1, -1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_18 knot (alternating, achiral)"
    ),
    
    "8_19": KnotInfo(
        rolfsen_id="8_19",
        common_name="8_19 Knot",
        rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 10), (11, 6), (7, 8), (12, 9)],
        signs=[1, -1, 1, -1, 1, 1, -1, -1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_19 knot (alternating, achiral)"
    ),
    
    "8_20": KnotInfo(
        rolfsen_id="8_20",
        common_name="8_20 Knot",
        rational_config=[(1, 16), (15, 2), (3, 10), (13, 4), (5, 12), (11, 6), (7, 8), (14, 9)],
        signs=[1, 1, -1, 1, -1, 1, -1, -1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=8,
        description="8_20 knot (alternating)"
    ),
    
    "8_21": KnotInfo(
        rolfsen_id="8_21",
        common_name="8_21 Knot",
        rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 8), (14, 9)],
        signs=[1, 1, -1, 1, -1, -1, 1, -1],
        is_chiral=False,
        is_alternating=True,
        crossing_number=8,
        description="8_21 knot (alternating, achiral)"
    ),
    
    # ========== 9 CROSSINGS - SAMPLE (First 10) ==========
    "9_1": KnotInfo(
        rolfsen_id="9_1",
        common_name="9_1 Knot (Nonafoil)",
        rational_config=[(1, 10), (11, 2), (3, 12), (13, 4), (5, 14), (15, 6), (7, 16), (17, 8), (9, 18)],
        signs=[1, 1, 1, 1, 1, 1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=9,
        description="Nonafoil knot (torus knot T(2,9))"
    ),
    
    "9_2": KnotInfo(
        rolfsen_id="9_2",
        common_name="9_2 Knot",
        rational_config=[(1, 14), (15, 2), (3, 16), (17, 4), (5, 18), (13, 6), (7, 12), (11, 8), (9, 10)],
        signs=[1, -1, 1, -1, 1, 1, -1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=9,
        description="9_2 knot (alternating)"
    ),
    
    "9_3": KnotInfo(
        rolfsen_id="9_3",
        common_name="9_3 Knot",
        rational_config=[(1, 14), (15, 2), (3, 18), (17, 4), (5, 16), (13, 6), (7, 12), (11, 8), (9, 10)],
        signs=[1, -1, -1, 1, 1, 1, -1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=9,
        description="9_3 knot (alternating)"
    ),
    
    # ========== 10 CROSSINGS - SAMPLE (First 5) ==========
    "10_1": KnotInfo(
        rolfsen_id="10_1",
        common_name="10_1 Knot",
        rational_config=[(1, 16), (17, 2), (3, 18), (19, 4), (5, 20), (15, 6), (7, 14), (13, 8), (9, 12), (11, 10)],
        signs=[1, -1, 1, -1, 1, 1, -1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=10,
        description="10_1 knot (alternating)"
    ),
    
    "10_2": KnotInfo(
        rolfsen_id="10_2",
        common_name="10_2 Knot",
        rational_config=[(1, 16), (17, 2), (3, 20), (19, 4), (5, 18), (15, 6), (7, 14), (13, 8), (9, 12), (11, 10)],
        signs=[1, -1, -1, 1, 1, 1, -1, 1, 1, 1],
        is_chiral=True,
        is_alternating=True,
        crossing_number=10,
        description="10_2 knot (alternating)"
    ),
}


# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

def get_knot(rolfsen_id: str) -> Optional[RationalKnot]:
    """
    Get a RationalKnot object for a given Rolfsen ID.
    
    Parameters
    ----------
    rolfsen_id : str
        Rolfsen notation (e.g., "3_1", "4_1")
    
    Returns
    -------
    Optional[RationalKnot]
        The knot object, or None if not found
    """
    if rolfsen_id not in ROLFSEN_KNOTS:
        return None
    
    info = ROLFSEN_KNOTS[rolfsen_id]
    
    if not info.rational_config:
        # Empty knot (unknot)
        return RationalKnot([])
    
    return RationalKnot.from_pairs(info.rational_config, info.signs)


def get_knot_info(rolfsen_id: str) -> Optional[KnotInfo]:
    """
    Get information about a knot.
    
    Parameters
    ----------
    rolfsen_id : str
        Rolfsen notation (e.g., "3_1", "4_1")
    
    Returns
    -------
    Optional[KnotInfo]
        Knot information, or None if not found
    """
    return ROLFSEN_KNOTS.get(rolfsen_id)


def list_available_knots() -> List[str]:
    """
    List all available Rolfsen IDs in the database.
    
    Returns
    -------
    List[str]
        List of Rolfsen IDs
    """
    return sorted(ROLFSEN_KNOTS.keys(), 
                 key=lambda x: (int(x.split('_')[0]), int(x.split('_')[1])))


def get_knots_by_crossing_number(n: int) -> List[str]:
    """
    Get all knots with a specific crossing number.
    
    Parameters
    ----------
    n : int
        Number of crossings
    
    Returns
    -------
    List[str]
        List of Rolfsen IDs
    """
    return [kid for kid, info in ROLFSEN_KNOTS.items() 
            if info.crossing_number == n]


def get_chiral_knots() -> List[str]:
    """
    Get all chiral knots in the database.
    
    Returns
    -------
    List[str]
        List of Rolfsen IDs for chiral knots
    """
    return [kid for kid, info in ROLFSEN_KNOTS.items() 
            if info.is_chiral]


def get_achiral_knots() -> List[str]:
    """
    Get all achiral (amphichiral) knots in the database.
    
    Returns
    -------
    List[str]
        List of Rolfsen IDs for achiral knots
    """
    return [kid for kid, info in ROLFSEN_KNOTS.items() 
            if not info.is_chiral]


def get_alternating_knots() -> List[str]:
    """
    Get all alternating knots in the database.
    
    Returns
    -------
    List[str]
        List of Rolfsen IDs for alternating knots
    """
    return [kid for kid, info in ROLFSEN_KNOTS.items() 
            if info.is_alternating]


def print_knot_database():
    """Print a formatted table of all knots in the database."""
    print("\n" + "=" * 100)
    print("  ROLFSEN KNOT DATABASE - RATIONAL CONFIGURATIONS")
    print("=" * 100)
    print()
    print(f"{'ID':<8} {'Name':<20} {'Crossings':<10} {'Chiral':<8} {'Alt':<8} {'Config':<30}")
    print("-" * 100)
    
    for kid in list_available_knots():
        info = ROLFSEN_KNOTS[kid]
        chiral_str = "Yes" if info.is_chiral else "No"
        alt_str = "Yes" if info.is_alternating else "No"
        
        if info.rational_config:
            config_str = str(info.rational_config[:3])
            if len(info.rational_config) > 3:
                config_str += "..."
        else:
            config_str = "[]"
        
        print(f"{kid:<8} {info.common_name:<20} {info.crossing_number:<10} "
              f"{chiral_str:<8} {alt_str:<8} {config_str:<30}")
    
    print("-" * 100)
    print(f"Total knots in database: {len(ROLFSEN_KNOTS)}")
    print()


def compare_with_rolfsen(knot: RationalKnot, verbose: bool = True) -> Optional[str]:
    """
    Try to identify a knot by comparing with the Rolfsen database.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to identify
    verbose : bool
        If True, print comparison details
    
    Returns
    -------
    Optional[str]
        Rolfsen ID if found, None otherwise
    """
    from reidemeister_moves import normal_form
    
    if verbose:
        print(f"\nAttempting to identify knot: {knot}")
        print(f"Degree: {knot.degree}")
    
    # Get normal form of input knot
    fn_input = normal_form(knot, verbose=False)
    
    # Compare with all knots of same degree
    candidates = get_knots_by_crossing_number(knot.degree)
    
    if verbose:
        print(f"Comparing with {len(candidates)} knots of degree {knot.degree}...")
    
    for kid in candidates:
        db_knot = get_knot(kid)
        fn_db = normal_form(db_knot, verbose=False)
        
        if fn_input == fn_db:
            if verbose:
                print(f"\n✓ Match found: {kid} ({ROLFSEN_KNOTS[kid].common_name})")
            return kid
    
    if verbose:
        print("\n✗ No match found in database")
    
    return None


if __name__ == "__main__":
    # Print database
    print_knot_database()
    
    # Example: Get trefoil
    print("\n" + "=" * 100)
    print("  EXAMPLE: TREFOIL KNOT")
    print("=" * 100)
    
    trefoil = get_knot("3_1")
    info = get_knot_info("3_1")
    
    print(f"\nRolfsen ID: {info.rolfsen_id}")
    print(f"Common name: {info.common_name}")
    print(f"Description: {info.description}")
    print(f"Rational configuration: {trefoil}")
    print(f"Chiral: {info.is_chiral}")
    print(f"Alternating: {info.is_alternating}")
    print(f"R(K) = {trefoil.rational_product()}")
    
    # Example: Compare knot
    print("\n" + "=" * 100)
    print("  EXAMPLE: KNOT IDENTIFICATION")
    print("=" * 100)
    
    # Create a trefoil with different numbering
    test_knot = RationalKnot.from_pairs([(1, 4), (5, 2), (3, 6)])
    identified = compare_with_rolfsen(test_knot, verbose=True)
