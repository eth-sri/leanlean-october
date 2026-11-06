/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Analytic.RealChargeBudget
import DOZZ.GMC.SharpMoments.SeibergDecomp

/-! Fixed separated insertion geometry for the local analytic construction. -/

open Filter Topology Set
namespace DOZZ.Proofs

/-- Distinct finitely many insertions admit one positive disk separation, bounded by `1/8`. -/
theorem separated_geometry {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖ := DOZZ.Proofs.exists_root_separation z hz

end DOZZ.Proofs
