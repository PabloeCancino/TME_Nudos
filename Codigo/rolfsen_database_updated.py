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
    "0_1": KnotInfo(rolfsen_id="0_1", common_name="Unknot", rational_config=[], signs=[], is_chiral=False, is_alternating=True, crossing_number=0, description="The trivial knot (unknot)"),
    "10_1": KnotInfo(rolfsen_id="10_1", common_name="10_1 Knot", rational_config=[(1, 16), (17, 2), (3, 18), (19, 4), (5, 20), (15, 6), (7, 14), (13, 8), (9, 12), (11, 10)], signs=[1, -1, 1, -1, 1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=10, description="10_1 knot (alternating)"),
    "10_2": KnotInfo(rolfsen_id="10_2", common_name="10_2 Knot", rational_config=[(1, 16), (17, 2), (3, 20), (19, 4), (5, 18), (15, 6), (7, 14), (13, 8), (9, 12), (11, 10)], signs=[1, -1, -1, 1, 1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=10, description="10_2 knot (alternating)"),
    "3_1": KnotInfo(rolfsen_id="3_1", common_name="Trefoil", rational_config=[(1, 4), (5, 2), (3, 6)], signs=[1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=3, description="Right-handed trefoil knot (torus knot T(2,3))"),
    "4_1": KnotInfo(rolfsen_id="4_1", common_name="Figure-Eight", rational_config=[(1, 4), (7, 2), (5, 8), (3, 6)], signs=[1, -1, 1, -1], is_chiral=False, is_alternating=True, crossing_number=4, description="Figure-eight knot (achiral, alternating)"),
    "5_1": KnotInfo(rolfsen_id="5_1", common_name="Cinquefoil", rational_config=[(1, 6), (7, 2), (3, 8), (9, 4), (5, 10)], signs=[1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=5, description="Cinquefoil knot (torus knot T(2,5))"),
    "5_2": KnotInfo(rolfsen_id="5_2", common_name="Three-Twist Knot", rational_config=[(1, 6), (7, 2), (3, 10), (9, 4), (5, 8)], signs=[1, 1, -1, 1, -1], is_chiral=True, is_alternating=False, crossing_number=5, description="Three-twist knot (non-alternating)"),
    "6_1": KnotInfo(rolfsen_id="6_1", common_name="Stevedore Knot", rational_config=[(1, 8), (9, 2), (3, 10), (11, 4), (5, 12), (7, 6)], signs=[1, -1, 1, -1, 1, -1], is_chiral=False, is_alternating=True, crossing_number=6, description="Stevedore knot (6_1, achiral)"),
    "6_2": KnotInfo(rolfsen_id="6_2", common_name="Miller Institute Knot", rational_config=[(1, 8), (9, 2), (3, 12), (11, 4), (5, 10), (7, 6)], signs=[1, -1, -1, 1, 1, -1], is_chiral=True, is_alternating=False, crossing_number=6, description="Miller Institute knot (6_2)"),
    "6_3": KnotInfo(rolfsen_id="6_3", common_name="6_3 Knot", rational_config=[(1, 8), (9, 2), (3, 10), (11, 6), (5, 12), (7, 4)], signs=[1, -1, 1, 1, -1, -1], is_chiral=True, is_alternating=False, crossing_number=6, description="6_3 knot (non-alternating)"),
    "7_1": KnotInfo(rolfsen_id="7_1", common_name="Septafoil", rational_config=[(14, 7), (6, 13), (12, 5), (4, 11), (10, 3), (2, 9), (8, 1)], signs=[1, 1, 1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="Septafoil knot (torus knot T(2,7))"),
    "7_2": KnotInfo(rolfsen_id="7_2", common_name="7_2 Knot", rational_config=[(14, 9), (8, 13), (12, 7), (6, 11), (10, 5), (4, 1), (2, 3)], signs=[1, 1, 1, 1, 1, -1, -1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_2 knot (K(11/2))"),
    "7_3": KnotInfo(rolfsen_id="7_3", common_name="7_3 Knot", rational_config=[(14, 9), (8, 1), (2, 7), (6, 13), (12, 5), (4, 11), (10, 3)], signs=[1, -1, -1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_3 knot (K(13/9))"),
    "7_4": KnotInfo(rolfsen_id="7_4", common_name="7_4 Knot", rational_config=[(14, 9), (8, 13), (12, 7), (6, 1), (2, 5), (4, 11), (10, 3)], signs=[1, 1, 1, -1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_4 knot (K(17/5))"),
    "7_5": KnotInfo(rolfsen_id="7_5", common_name="7_5 Knot", rational_config=[(14, 7), (6, 13), (12, 1), (2, 11), (10, 5), (4, 9), (8, 3)], signs=[1, 1, -1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_5 knot (K(17/7))"),
    "7_6": KnotInfo(rolfsen_id="7_6", common_name="7_6 Knot", rational_config=[(14, 9), (8, 1), (2, 13), (12, 3), (4, 7), (6, 11), (10, 5)], signs=[1, -1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_6 knot (K(19/11))"),
    "7_7": KnotInfo(rolfsen_id="7_7", common_name="7_7 Knot", rational_config=[(14, 5), (6, 13), (12, 1), (2, 7), (8, 11), (10, 3), (4, 9)], signs=[1, 1, -1, 1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=7, description="7_7 knot (K(21/8))"),
    "8_1": KnotInfo(rolfsen_id="8_1", common_name="8_1 Knot", rational_config=[(1, 12), (13, 2), (3, 14), (15, 4), (5, 16), (11, 6), (7, 10), (9, 8)], signs=[1, -1, 1, -1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_1 knot (alternating)"),
    "8_2": KnotInfo(rolfsen_id="8_2", common_name="8_2 Knot", rational_config=[(1, 12), (13, 2), (3, 16), (15, 4), (5, 14), (11, 6), (7, 10), (9, 8)], signs=[1, -1, -1, 1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_2 knot (alternating)"),
    "8_3": KnotInfo(rolfsen_id="8_3", common_name="8_3 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)], signs=[1, -1, -1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_3 knot (alternating)"),
    "8_4": KnotInfo(rolfsen_id="8_4", common_name="8_4 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 16), (11, 6), (7, 10), (9, 8)], signs=[1, 1, -1, -1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_4 knot (alternating)"),
    "8_5": KnotInfo(rolfsen_id="8_5", common_name="8_5 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)], signs=[1, -1, 1, 1, -1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_5 knot (alternating, achiral)"),
    "8_6": KnotInfo(rolfsen_id="8_6", common_name="8_6 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)], signs=[1, -1, -1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_6 knot (alternating)"),
    "8_7": KnotInfo(rolfsen_id="8_7", common_name="8_7 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 14), (11, 6), (7, 10), (9, 8)], signs=[1, 1, -1, -1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_7 knot (alternating)"),
    "8_8": KnotInfo(rolfsen_id="8_8", common_name="8_8 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 16), (9, 8)], signs=[1, 1, -1, 1, -1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_8 knot (alternating, achiral)"),
    "8_9": KnotInfo(rolfsen_id="8_9", common_name="8_9 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)], signs=[1, -1, 1, -1, 1, -1, -1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_9 knot (alternating, achiral)"),
    "8_10": KnotInfo(rolfsen_id="8_10", common_name="8_10 Knot", rational_config=[(1, 12), (13, 2), (3, 16), (15, 4), (5, 10), (11, 6), (7, 14), (9, 8)], signs=[1, -1, -1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_10 knot (alternating)"),
    "8_11": KnotInfo(rolfsen_id="8_11", common_name="8_11 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 14), (9, 8)], signs=[1, 1, -1, 1, -1, -1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_11 knot (alternating)"),
    "8_12": KnotInfo(rolfsen_id="8_12", common_name="8_12 Knot", rational_config=[(1, 14), (15, 2), (3, 10), (13, 4), (5, 16), (11, 6), (7, 12), (9, 8)], signs=[1, 1, -1, -1, -1, 1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_12 knot (alternating, achiral)"),
    "8_13": KnotInfo(rolfsen_id="8_13", common_name="8_13 Knot", rational_config=[(1, 16), (15, 2), (3, 10), (13, 4), (5, 14), (11, 6), (7, 12), (9, 8)], signs=[1, 1, -1, 1, 1, -1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_13 knot (alternating)"),
    "8_14": KnotInfo(rolfsen_id="8_14", common_name="8_14 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 8), (10, 9)], signs=[1, -1, 1, -1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_14 knot (alternating)"),
    "5_1": KnotInfo(rolfsen_id="5_1", common_name="Cinquefoil", rational_config=[(1, 6), (7, 2), (3, 8), (9, 4), (5, 10)], signs=[1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=5, description="Cinquefoil knot (torus knot T(2,5))"),
    "5_2": KnotInfo(rolfsen_id="5_2", common_name="Three-Twist Knot", rational_config=[(1, 6), (7, 2), (3, 10), (9, 4), (5, 8)], signs=[1, 1, -1, 1, -1], is_chiral=True, is_alternating=False, crossing_number=5, description="Three-twist knot (non-alternating)"),
    "6_1": KnotInfo(rolfsen_id="6_1", common_name="Stevedore Knot", rational_config=[(1, 8), (9, 2), (3, 10), (11, 4), (5, 12), (7, 6)], signs=[1, -1, 1, -1, 1, -1], is_chiral=False, is_alternating=True, crossing_number=6, description="Stevedore knot (6_1, achiral)"),
    "6_2": KnotInfo(rolfsen_id="6_2", common_name="Miller Institute Knot", rational_config=[(1, 8), (9, 2), (3, 12), (11, 4), (5, 10), (7, 6)], signs=[1, -1, -1, 1, 1, -1], is_chiral=True, is_alternating=False, crossing_number=6, description="Miller Institute knot (6_2)"),
    "6_3": KnotInfo(rolfsen_id="6_3", common_name="6_3 Knot", rational_config=[(1, 8), (9, 2), (3, 10), (11, 6), (5, 12), (7, 4)], signs=[1, -1, 1, 1, -1, -1], is_chiral=True, is_alternating=False, crossing_number=6, description="6_3 knot (non-alternating)"),
    "7_1": KnotInfo(rolfsen_id="7_1", common_name="Septafoil", rational_config=[(14, 7), (6, 13), (12, 5), (4, 11), (10, 3), (2, 9), (8, 1)], signs=[1, 1, 1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="Septafoil knot (torus knot T(2,7))"),
    "7_2": KnotInfo(rolfsen_id="7_2", common_name="7_2 Knot", rational_config=[(14, 9), (8, 13), (12, 7), (6, 11), (10, 5), (4, 1), (2, 3)], signs=[1, 1, 1, 1, 1, -1, -1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_2 knot (K(11/2))"),
    "7_3": KnotInfo(rolfsen_id="7_3", common_name="7_3 Knot", rational_config=[(14, 9), (8, 1), (2, 7), (6, 13), (12, 5), (4, 11), (10, 3)], signs=[1, -1, -1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_3 knot (K(13/9))"),
    "7_4": KnotInfo(rolfsen_id="7_4", common_name="7_4 Knot", rational_config=[(14, 9), (8, 13), (12, 7), (6, 1), (2, 5), (4, 11), (10, 3)], signs=[1, 1, 1, -1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_4 knot (K(17/5))"),
    "7_5": KnotInfo(rolfsen_id="7_5", common_name="7_5 Knot", rational_config=[(14, 7), (6, 13), (12, 1), (2, 11), (10, 5), (4, 9), (8, 3)], signs=[1, 1, -1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_5 knot (K(17/7))"),
    "7_6": KnotInfo(rolfsen_id="7_6", common_name="7_6 Knot", rational_config=[(14, 9), (8, 1), (2, 13), (12, 3), (4, 7), (6, 11), (10, 5)], signs=[1, -1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=7, description="7_6 knot (K(19/11))"),
    "7_7": KnotInfo(rolfsen_id="7_7", common_name="7_7 Knot", rational_config=[(14, 5), (6, 13), (12, 1), (2, 7), (8, 11), (10, 3), (4, 9)], signs=[1, 1, -1, 1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=7, description="7_7 knot (K(21/8))"),
    "8_1": KnotInfo(rolfsen_id="8_1", common_name="8_1 Knot", rational_config=[(1, 12), (13, 2), (3, 14), (15, 4), (5, 16), (11, 6), (7, 10), (9, 8)], signs=[1, -1, 1, -1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_1 knot (alternating)"),
    "8_2": KnotInfo(rolfsen_id="8_2", common_name="8_2 Knot", rational_config=[(1, 12), (13, 2), (3, 16), (15, 4), (5, 14), (11, 6), (7, 10), (9, 8)], signs=[1, -1, -1, 1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_2 knot (alternating)"),
    "8_3": KnotInfo(rolfsen_id="8_3", common_name="8_3 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)], signs=[1, -1, -1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_3 knot (alternating)"),
    "8_4": KnotInfo(rolfsen_id="8_4", common_name="8_4 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 16), (11, 6), (7, 10), (9, 8)], signs=[1, 1, -1, -1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_4 knot (alternating)"),
    "8_5": KnotInfo(rolfsen_id="8_5", common_name="8_5 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)], signs=[1, -1, 1, 1, -1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_5 knot (alternating, achiral)"),
    "8_6": KnotInfo(rolfsen_id="8_6", common_name="8_6 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)], signs=[1, -1, -1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_6 knot (alternating)"),
    "8_7": KnotInfo(rolfsen_id="8_7", common_name="8_7 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 14), (11, 6), (7, 10), (9, 8)], signs=[1, 1, -1, -1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_7 knot (alternating)"),
    "8_8": KnotInfo(rolfsen_id="8_8", common_name="8_8 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 16), (9, 8)], signs=[1, 1, -1, 1, -1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_8 knot (alternating, achiral)"),
    "8_9": KnotInfo(rolfsen_id="8_9", common_name="8_9 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)], signs=[1, -1, 1, -1, 1, -1, -1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_9 knot (alternating, achiral)"),
    "8_10": KnotInfo(rolfsen_id="8_10", common_name="8_10 Knot", rational_config=[(1, 12), (13, 2), (3, 16), (15, 4), (5, 10), (11, 6), (7, 14), (9, 8)], signs=[1, -1, -1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_10 knot (alternating)"),
    "8_11": KnotInfo(rolfsen_id="8_11", common_name="8_11 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 14), (9, 8)], signs=[1, 1, -1, 1, -1, -1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_11 knot (alternating)"),
    "8_12": KnotInfo(rolfsen_id="8_12", common_name="8_12 Knot", rational_config=[(1, 14), (15, 2), (3, 10), (13, 4), (5, 16), (11, 6), (7, 12), (9, 8)], signs=[1, 1, -1, -1, -1, 1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_12 knot (alternating, achiral)"),
    "8_13": KnotInfo(rolfsen_id="8_13", common_name="8_13 Knot", rational_config=[(1, 16), (15, 2), (3, 10), (13, 4), (5, 14), (11, 6), (7, 12), (9, 8)], signs=[1, 1, -1, 1, 1, -1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_13 knot (alternating)"),
    "8_14": KnotInfo(rolfsen_id="8_14", common_name="8_14 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 8), (10, 9)], signs=[1, -1, 1, -1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_14 knot (alternating)"),
    "8_15": KnotInfo(rolfsen_id="8_15", common_name="8_15 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 12), (11, 6), (7, 8), (10, 9)], signs=[1, -1, -1, 1, 1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_15 knot (alternating, achiral)"),
    "8_16": KnotInfo(rolfsen_id="8_16", common_name="8_16 Knot", rational_config=[(1, 12), (13, 2), (3, 14), (15, 4), (5, 16), (11, 6), (7, 8), (10, 9)], signs=[1, -1, 1, -1, 1, 1, -1, -1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_16 knot (alternating)"),
    "8_17": KnotInfo(rolfsen_id="8_17", common_name="8_17 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 14), (11, 6), (7, 8), (10, 9)], signs=[1, 1, -1, -1, 1, 1, -1, -1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_17 knot (alternating, achiral)"),
    "8_18": KnotInfo(rolfsen_id="8_18", common_name="8_18 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 16), (11, 6), (7, 8), (10, 9)], signs=[1, 1, -1, -1, -1, 1, 1, -1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_18 knot (alternating, achiral)"),
    "8_19": KnotInfo(rolfsen_id="8_19", common_name="8_19 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 10), (11, 6), (7, 8), (12, 9)], signs=[1, -1, 1, -1, 1, 1, -1, -1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_19 knot (alternating, achiral)"),
    "8_2": KnotInfo(rolfsen_id="8_2", common_name="8_2 Knot", rational_config=[(1, 10), (11, 2), (3, 12), (13, 4), (5, 14), (7, 6), (15, 8), (9, 16)], signs=[1, 1, 1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_2 knot (alternating)"),
    "8_20": KnotInfo(rolfsen_id="8_20", common_name="8_20 Knot", rational_config=[(1, 16), (15, 2), (3, 10), (13, 4), (5, 12), (11, 6), (7, 8), (14, 9)], signs=[1, 1, -1, 1, -1, 1, -1, -1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_20 knot (alternating)"),
    "8_21": KnotInfo(rolfsen_id="8_21", common_name="8_21 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 8), (14, 9)], signs=[1, 1, -1, 1, -1, -1, 1, -1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_21 knot (alternating, achiral)"),
    "8_3": KnotInfo(rolfsen_id="8_3", common_name="8_3 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)], signs=[1, -1, -1, 1, -1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_3 knot (alternating)"),
    "8_4": KnotInfo(rolfsen_id="8_4", common_name="8_4 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 16), (11, 6), (7, 10), (9, 8)], signs=[1, 1, -1, -1, 1, 1, -1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_4 knot (alternating)"),
    "8_5": KnotInfo(rolfsen_id="8_5", common_name="8_5 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 12), (11, 6), (7, 10), (9, 8)], signs=[1, -1, 1, 1, -1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_5 knot (alternating, achiral)"),
    "8_6": KnotInfo(rolfsen_id="8_6", common_name="8_6 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)], signs=[1, -1, -1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_6 knot (alternating)"),
    "8_7": KnotInfo(rolfsen_id="8_7", common_name="8_7 Knot", rational_config=[(1, 16), (15, 2), (3, 12), (13, 4), (5, 14), (11, 6), (7, 10), (9, 8)], signs=[1, 1, -1, -1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=8, description="8_7 knot (alternating)"),
    "8_8": KnotInfo(rolfsen_id="8_8", common_name="8_8 Knot", rational_config=[(1, 14), (15, 2), (3, 12), (13, 4), (5, 10), (11, 6), (7, 16), (9, 8)], signs=[1, 1, -1, 1, -1, -1, 1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_8 knot (alternating, achiral)"),
    "8_9": KnotInfo(rolfsen_id="8_9", common_name="8_9 Knot", rational_config=[(1, 16), (15, 2), (3, 14), (13, 4), (5, 10), (11, 6), (7, 12), (9, 8)], signs=[1, -1, 1, -1, 1, -1, -1, 1], is_chiral=False, is_alternating=True, crossing_number=8, description="8_9 knot (alternating, achiral)"),
    "9_1": KnotInfo(rolfsen_id="9_1", common_name="9_1 Knot (Nonafoil)", rational_config=[(1, 10), (11, 2), (3, 12), (13, 4), (5, 14), (15, 6), (7, 16), (17, 8), (9, 18)], signs=[1, 1, 1, 1, 1, 1, 1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=9, description="Nonafoil knot (torus knot T(2,9))"),
    "9_2": KnotInfo(rolfsen_id="9_2", common_name="9_2 Knot", rational_config=[(1, 14), (15, 2), (3, 16), (17, 4), (5, 18), (9, 6), (7, 10), (11, 8), (19, 12), (13, 20)], signs=[1, 1, 1, 1, 1, -1, -1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=9, description="9_2 knot (alternating)"),
    "9_3": KnotInfo(rolfsen_id="9_3", common_name="9_3 Knot", rational_config=[(1, 14), (15, 2), (3, 18), (17, 4), (5, 16), (13, 6), (7, 12), (11, 8), (9, 10)], signs=[1, -1, -1, 1, 1, 1, -1, 1, 1], is_chiral=True, is_alternating=True, crossing_number=9, description="9_3 knot (alternating)"),
}