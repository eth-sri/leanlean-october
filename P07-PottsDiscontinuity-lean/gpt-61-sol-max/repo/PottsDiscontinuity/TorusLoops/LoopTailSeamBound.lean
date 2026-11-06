module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.RectangleCrossingCount
public import PottsDiscontinuity.TorusLoops.RectangleFK

/-!
# Finite-energy reduction of winding-loop tails to rectangle crossings

The deterministic corrected crossing count and the seam-stability of the
cut-graph event give the first probability inequality in the proof of (3.17).
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N M : ℕ}

/-- Configurations with at least `m` homologically winding loops. -/
def windingLoopTailEvent (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (m : ℕ)  :=
  {A | m ≤ windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A}

/-- The source finite-energy reduction, with the factor-two-corrected number
of distinct horizontal cut-rectangle crossing components. -/
theorem torusRCProbability_windingTail_le_seamClosedCrossings
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) :
    (1 - (rcCriticalParameter q).val) ^
        (rectangleSeamIndices (N := N) (M := M)).card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      phi_T_probability hN hM q
        (hasAtLeastRectangleCrossings hN hM ((m - 3 * N + 1) / 2) ∩
          {A | ∀ v ∈ rectangleSeamIndices (N := N) (M := M), A v = false}) := by
  
  let S := rectangleSeamIndices (N := N) (M := M)
  let k := (m - 3 * N + 1) / 2
  let C := hasAtLeastRectangleCrossings hN hM k
  
  
  
  
  
  have hclosed' :
      (1 - (rcCriticalParameter q).val) ^ S.card *
          phi_T_probability hN hM q C ≤
        phi_T_probability hN hM q (C ∩ {A | ∀ v ∈ S, A v = false}) := (torusRCProbability_close_finite_set hN hM q S C (by
                                                                                                                                                                            exact fun v hv A => hasAtLeastRectangleCrossings_toggleEdge_seam hN hM k A v (Finset.mem_filter.mp hv).right))
  calc
    (1 - (rcCriticalParameter q).val) ^ S.card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      (1 - (rcCriticalParameter q).val) ^ S.card *
        phi_T_probability hN hM q C := mul_le_mul_of_nonneg_left (torusRCProbability_mono hN hM q (windingLoopCount_ge_implies_rectangleCrossings hN hM hNp hMp m)) (pow_nonneg (sub_nonneg.mpr (criticalParameter_lt_one q).le) _)
    _ ≤ phi_T_probability hN hM q (C ∩ {A | ∀ v ∈ S, A v = false}) := by
      simpa [S, C] using hclosed'
    _ = phi_T_probability hN hM q
        (hasAtLeastRectangleCrossings hN hM k ∩
          {A | ∀ v ∈ rectangleSeamIndices (N := N) (M := M), A v = false}) := rfl

end PottsDiscontinuity.TorusLoops
