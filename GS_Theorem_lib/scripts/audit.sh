#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0/bin:$PATH"

cd "$ROOT"

echo "=== [1/3] Checking zero sorry / admit / axiom / native_decide in code ==="
BAD=$(grep -rn -E '^[[:space:]]*(sorry|admit|axiom |theorem .*:=\s*by\s*native_decide|native_decide)' GSTheoremLib.lean GSTheoremLib/ || true)
if [ -n "$BAD" ]; then
  echo "FAILED: forbidden keyword found:"
  echo "$BAD"
  exit 1
fi
echo "CLEAN: zero sorry / admit / axiom / native_decide."

echo "=== [2/3] Running full lake build ==="
lake build

echo "=== [3/3] Running #print axioms audit across all 4 theorem suites ==="
lake env lean --stdin <<'EOF'
import GSTheoremLib

-- Core
#print axioms GSTheoremLib.Core.qpEq_iff
#print axioms GSTheoremLib.Core.qpLe_iff
#print axioms GSTheoremLib.Core.nagumoScaled_eq_unit
#print axioms GSTheoremLib.Core.pi_machin_enclosure
#print axioms GSTheoremLib.Core.expGridList_encloses

-- PlanarCrossover
#print axioms PlanarNonmonotoneCrossover.dual_rail_not_impossible_in_planar_disk
#print axioms PlanarNonmonotoneCrossover.dual_rail_not_impossible_single_port_planar_disk
#print axioms PlanarNonmonotoneCrossover.xorGadget_is_strictly_planar
#print axioms PlanarNonmonotoneCrossover.swapGadget_is_strictly_planar
#print axioms PlanarNonmonotoneCrossover.inhibitToNandGadget_is_strictly_planar

-- M-23
#print axioms M23Supersolution.m23_all_time_supersolution_comparison
#print axioms M23Supersolution.m23_all_time_subthreshold_pinning
#print axioms M23Supersolution.m23_h2_exact_center_slopes
#print axioms M23Supersolution.m23_coupled_stencil_inheritance

-- M-27
#print axioms M27SymmetryContraction.secantSlope_bounds
#print axioms M27SymmetryContraction.m27_critical_width_phys_enclosure
#print axioms M27SymmetryContraction.m27_critical_width_cells_enclosure
#print axioms M27SymmetryContraction.m27_continuum_gamma_pos_le39
#print axioms M27SymmetryContraction.m27_continuum_gamma_neg_40
#print axioms M27SymmetryContraction.m27_discrete_all_time_spatial_contraction
#print axioms M27SymmetryContraction.antisym_entrance_normSq_le
#print axioms M27SymmetryContraction.antisym_linf_sq_le_two_normSq
#print axioms M27SymmetryContraction.m27_h0_w25_5pt_cert
#print axioms M27SymmetryContraction.m27_h0_w25_9pt_cert
#print axioms M27SymmetryContraction.m27_h2_w50_5pt_cert
#print axioms M27SymmetryContraction.m27_h2_w50_9pt_cert

-- M-41
#print axioms M41ScalarReset.SymGraphNagumo.energy_step_descent
#print axioms M41ScalarReset.m41_negative_energy_reset_obstruction
#print axioms M41ScalarReset.m41_four_grid_exact_constants
#print axioms M41ScalarReset.m41_uniform_fuel_depletion_from_threshold_witness

-- M-44 (including all 2,269 frozen JSON segments + end-to-end Rat bridge)
#print axioms M44ContinuumPinning.pi_machin_enclosure
#print axioms M44ContinuumPinning.checkFullRawCert_sound
#print axioms M44ContinuumPinning.m44_w15_end_to_end
#print axioms M44ContinuumPinning.m44_w16_end_to_end
#print axioms M44ContinuumPinning.m44_w17_end_to_end
#print axioms M44ContinuumPinning.m44_w18_end_to_end
EOF
echo "=== AUDIT COMPLETE ==="
