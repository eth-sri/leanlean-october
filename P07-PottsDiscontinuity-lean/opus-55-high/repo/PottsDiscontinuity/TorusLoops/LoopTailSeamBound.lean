module

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

section
variable (hN : Even N) (hM : Even M)
include hN hM
/-- Configurations with at least `m` homologically winding loops. -/
def windingLoopTailEvent (hNp : 0 < N) (hMp : 0 < M)
    (m : ℕ) : Set (RCConfig N M) :=
  {A | m ≤ windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A}

/-- The source finite-energy reduction, with the factor-two-corrected number
of distinct horizontal cut-rectangle crossing components. -/
theorem torusRCProbability_windingTail_le_seamClosedCrossings
    (hNp : 0 < N) (hMp : 0 < M)
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
  have hsub : windingLoopTailEvent hN hM hNp hMp m ⊆ C := by
    intro A hA
    have hcross := windingLoopCount_ge_implies_rectangleCrossings
      hN hM hNp hMp m A hA
    tauto
  have hstable : ∀ v ∈ S, ∀ A,
      A ∈ C ↔ toggleEdge A v ∈ C := by
    intro v hv A
    have hseam :=
      (Finset.mem_filter.mp hv).2
    exact hasAtLeastRectangleCrossings_toggleEdge_seam hN hM k A v hseam
  have hclosed := torusRCProbability_close_finite_set hN hM q S C hstable
  have hclosed' :
      (1 - (rcCriticalParameter q).val) ^ S.card *
          phi_T_probability hN hM q C ≤
        phi_T_probability hN hM q (C ∩ {A | ∀ v ∈ S, A v = false}) := by
    tauto
  calc
    (1 - (rcCriticalParameter q).val) ^ S.card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      (1 - (rcCriticalParameter q).val) ^ S.card *
        phi_T_probability hN hM q C := mul_le_mul_of_nonneg_left (torusRCProbability_mono hN hM q hsub) (pow_nonneg (sub_nonneg.mpr (criticalParameter_lt_one q).le) _)
    _ ≤ phi_T_probability hN hM q (C ∩ {A | ∀ v ∈ S, A v = false}) := by
      omega
    _ = phi_T_probability hN hM q
        (hasAtLeastRectangleCrossings hN hM k ∩
          {A | ∀ v ∈ rectangleSeamIndices, A v = false}) := by
      rfl
end

end PottsDiscontinuity.TorusLoops
