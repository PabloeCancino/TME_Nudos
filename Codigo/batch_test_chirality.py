"""
Batch Testing of Chiral Knots - Rational Invariant R(K) Validation

This script systematically tests the rational invariant R(K*) = R(K)^(-1) on:
1. Problematic chiral knots (where classical invariants fail)
2. Complete Rolfsen database
3. Known amphichiral knots (verification)

Goal: Demonstrate that R(K) successfully detects chirality across all test cases.
"""

import json
from typing import Dict, List, Tuple, Optional
from fractions import Fraction
from knot_notation_converter import gauss_to_rational
from rational_knot_theory import RationalKnot
import rolfsen_database as rdb


# Problematic chiral knots with Gauss codes from KnotAtlas
PROBLEMATIC_CHIRAL_KNOTS = {
    "9_42": {
        "gauss_code": [1, -2, 3, -4, 2, -1, 5, -6, 4, -3, 7, -8, 6, -5, 9, -7, 8, -9],
        "description": "Chiral knot with symmetric Jones polynomial",
        "classical_fail": True
    },
    "10_71": {
        "gauss_code": [-1, 10, -2, 1, -4, 5, -10, 2, -6, 9, -3, 4, -5, 3, -7, 8, -9, 6, -8, 7],
        "description": "Chiral knot, classical invariants cannot detect",
        "classical_fail": True
    }
}


def test_single_knot(knot_id: str, gauss_code: List[int], description: str) -> Dict:
    """Test a single knot for chirality detection."""
    
    print(f"\n{'='*80}")
    print(f"  Testing: {knot_id}")
    print(f"  {description}")
    print(f"{'='*80}")
    
    result = {
        "knot_id": knot_id,
        "description": description,
        "success": False,
        "error": None
    }
    
    try:
        # Convert to rational
        K = gauss_to_rational(gauss_code)
        print(f"✓ Converted to rational representation ({K.n_crossings} crossings)")
        
        # Calculate R(K)
        R_K = K.rational_product()
        print(f"  R(K) = {R_K} ≈ {float(R_K):.6f}")
        
        # Get mirror
        K_mirror = K.mirror()
        R_K_mirror = K_mirror.rational_product()
        print(f"  R(K*) = {R_K_mirror} ≈ {float(R_K_mirror):.6f}")
        
        # Verify mirror property
        R_K_inverse = Fraction(1) / R_K
        mirror_property_verified = (R_K_mirror == R_K_inverse)
        print(f"  R(K*) = R(K)⁻¹? {mirror_property_verified}")
        
        # Detect chirality
        is_chiral = (R_K != R_K_mirror)
        print(f"  Chirality detected? {is_chiral}")
        
        result.update({
            "n_crossings": K.n_crossings,
            "R_K": str(R_K),
            "R_K_decimal": float(R_K),
            "R_K_mirror": str(R_K_mirror),
            "R_K_mirror_decimal": float(R_K_mirror),
            "mirror_property_verified": mirror_property_verified,
            "chirality_detected": is_chiral,
            "success": True
        })
        
        if is_chiral and mirror_property_verified:
            print(f"  ✅ SUCCESS: Chirality detected correctly!")
        elif not is_chiral:
            print(f"  ⚠️  WARNING: No chirality detected (amphichiral?)")
        
    except Exception as e:
        print(f"  ❌ ERROR: {e}")
        result["error"] = str(e)
    
    return result


def test_rolfsen_database() -> Dict:
    """Test all knots in the Rolfsen database."""
    
    print(f"\n{'='*80}")
    print(f"  TESTING ROLFSEN DATABASE")
    print(f"{'='*80}")
    
    all_knots = rdb.list_available_knots()
    print(f"\nTotal knots in database: {len(all_knots)}")
    
    results = {
        "total": len(all_knots),
        "tested": 0,
        "chiral_detected": 0,
        "amphichiral_detected": 0,
        "errors": 0,
        "knots": {}
    }
    
    for knot_id in all_knots:
        try:
            knot_info = rdb.get_knot_info(knot_id)
            if not knot_info:
                continue
                
            K = rdb.get_knot(knot_id)
            if not K:
                continue
            
            # Calculate R(K) and R(K*)
            R_K = K.rational_product()
            K_mirror = K.mirror()
            R_K_mirror = K_mirror.rational_product()
            
            # Check chirality
            is_chiral_detected = (R_K != R_K_mirror)
            expected_chiral = knot_info.is_chiral
            
            # Verify mirror property
            R_K_inverse = Fraction(1) / R_K
            mirror_property_ok = (R_K_mirror == R_K_inverse)
            
            results["tested"] += 1
            
            if is_chiral_detected:
                results["chiral_detected"] += 1
            else:
                results["amphichiral_detected"] += 1
            
            # Check if detection matches expected
            detection_correct = (is_chiral_detected == expected_chiral)
            
            results["knots"][knot_id] = {
                "expected_chiral": expected_chiral,
                "detected_chiral": is_chiral_detected,
                "correct": detection_correct,
                "mirror_property_ok": mirror_property_ok,
                "R_K": str(R_K),
                "R_K_mirror": str(R_K_mirror)
            }
            
            status = "✓" if detection_correct else "✗"
            chiral_str = "chiral" if is_chiral_detected else "amphichiral"
            print(f"  {status} {knot_id:8s} - {chiral_str:12s} (expected: {expected_chiral})")
            
        except Exception as e:
            results["errors"] += 1
            print(f"  ✗ {knot_id:8s} - ERROR: {e}")
    
    return results


def generate_report(problematic_results: List[Dict], rolfsen_results: Dict):
    """Generate comprehensive test report."""
    
    print(f"\n{'='*80}")
    print(f"  COMPREHENSIVE TEST REPORT")
    print(f"{'='*80}")
    
    # Problematic knots summary
    print(f"\n--- Problematic Chiral Knots ---")
    print(f"Total tested: {len(problematic_results)}")
    successful = sum(1 for r in problematic_results if r.get("success") and r.get("chirality_detected"))
    print(f"Successfully detected: {successful}/{len(problematic_results)}")
    
    for result in problematic_results:
        if result.get("success"):
            status = "✅" if result.get("chirality_detected") else "⚠️"
            print(f"  {status} {result['knot_id']}: {result['description']}")
    
    # Rolfsen database summary
    print(f"\n--- Rolfsen Database ---")
    print(f"Total knots: {rolfsen_results['total']}")
    print(f"Successfully tested: {rolfsen_results['tested']}")
    print(f"Chiral detected: {rolfsen_results['chiral_detected']}")
    print(f"Amphichiral detected: {rolfsen_results['amphichiral_detected']}")
    print(f"Errors: {rolfsen_results['errors']}")
    
    # Calculate accuracy
    correct = sum(1 for k in rolfsen_results['knots'].values() if k['correct'])
    accuracy = (correct / rolfsen_results['tested'] * 100) if rolfsen_results['tested'] > 0 else 0
    print(f"\nAccuracy: {correct}/{rolfsen_results['tested']} = {accuracy:.1f}%")
    
    # Check mirror property
    mirror_ok = sum(1 for k in rolfsen_results['knots'].values() if k['mirror_property_ok'])
    print(f"Mirror property R(K*) = R(K)⁻¹: {mirror_ok}/{rolfsen_results['tested']} = {mirror_ok/rolfsen_results['tested']*100:.1f}%")
    
    # Mismatches
    mismatches = [kid for kid, v in rolfsen_results['knots'].items() if not v['correct']]
    if mismatches:
        print(f"\n⚠️  Mismatches found: {mismatches}")
    else:
        print(f"\n✅ All detections match expected chirality!")
    
    return {
        "problematic_knots": problematic_results,
        "rolfsen_database": rolfsen_results,
        "summary": {
            "problematic_success_rate": successful / len(problematic_results) if problematic_results else 0,
            "rolfsen_accuracy": accuracy / 100,
            "mirror_property_success": mirror_ok / rolfsen_results['tested'] if rolfsen_results['tested'] > 0 else 0
        }
    }


def main():
    """Main testing routine."""
    
    print("="*80)
    print("  BATCH TESTING: RATIONAL INVARIANT R(K) FOR CHIRALITY DETECTION")
    print("="*80)
    
    # Test problematic chiral knots
    print(f"\n{'='*80}")
    print(f"  PHASE 1: PROBLEMATIC CHIRAL KNOTS")
    print(f"{'='*80}")
    
    problematic_results = []
    for knot_id, data in PROBLEMATIC_CHIRAL_KNOTS.items():
        result = test_single_knot(
            knot_id,
            data["gauss_code"],
            data["description"]
        )
        problematic_results.append(result)
    
    # Test Rolfsen database
    print(f"\n{'='*80}")
    print(f"  PHASE 2: ROLFSEN DATABASE")
    print(f"{'='*80}")
    
    rolfsen_results = test_rolfsen_database()
    
    # Generate report
    full_report = generate_report(problematic_results, rolfsen_results)
    
    # Save results
    with open("batch_chirality_test_results.json", "w") as f:
        json.dump(full_report, f, indent=2)
    
    print(f"\n{'='*80}")
    print(f"  Results saved to: batch_chirality_test_results.json")
    print(f"{'='*80}")
    
    return full_report


if __name__ == "__main__":
    main()
