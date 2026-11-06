module

public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordMoleculeContourCount
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

noncomputable def contourBudget (a : I) (k : ℕ) : ENNReal :=
  (molecularContourConstant : ENNReal) * (1-(toNNReal a : ENNReal)^2)^k

theorem measure_molecule_contours_size_le {L N w k b : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (hb : 0 < b) (a : I) :
    staticReactionMeasure N a {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s b,
      contourDetoursFailed hL C (fun r ω => ω r) ω} ≤ (contourBudget a k)^b := by
  let E := wordMoleculeContourEnvelope L N s b
  have hcount : (E.card : ENNReal) ≤ (molecularContourConstant : ENNReal)^b :=
    by exact_mod_cast wordMoleculeContourEnvelope_card L N s b hb
  rw [show {ω : Reaction N → Prop | ∃ C ∈ E, contourDetoursFailed hL C (fun r ω => ω r) ω} =
    ⋃ C ∈ E, {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} by ext; simp]
  calc
    _ ≤ ∑ C ∈ E, staticReactionMeasure N a {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} :=
      measure_biUnion_finset_le E _
    _ ≤ ∑ _C ∈ E, ((1-(toNNReal a : ENNReal)^2)^k)^b := Finset.sum_le_sum fun C hC => by
      obtain ⟨_, _, he⟩ := Finset.mem_biUnion.mp hC
      simpa only [(Finset.mem_filter.mp he).2.1] using staticReaction_contour_failure hL hk C a
    _ ≤ (contourBudget a k)^b := by rw [Finset.sum_const, nsmul_eq_mul, contourBudget, mul_pow]; gcongr

/-- A per-molecule envelope of all positive-size disabled contours. Its
probability bounds actual smaller-side membership by the compiled anchor theorem. -/
def moleculeContourBad {L N w : ℕ} (hL : 2*w ≤ L) (s : List Bool)
    (ω : Reaction N → Prop) : Prop :=
  ∃ j : ℕ, ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
    contourDetoursFailed hL C (fun r ω => ω r) ω

theorem wordBond_smaller_side_bad {L N w : ℕ} (hL : 2*w ≤ L)
    (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (hn : (wordGraphCut f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) (ω : Reaction N → Prop)
    (hfailed : contourDetoursFailed hL (wordGraphCut f) (fun r ω => ω r) ω) :
    moleculeContourBad hL s ω :=
  ⟨(wordGraphCut f).card - 1, wordGraphCut f, by
    rw [Nat.sub_add_cancel (Finset.card_pos.mpr hn)]
    exact wordBond_mem_molecule_envelope f hmin hn c hminor s hs, hfailed⟩

/-- Uniform bad-side marginal; no independence between contours is required. -/
theorem measure_moleculeContourBad_le {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (a : I) :
    staticReactionMeasure N a {ω | moleculeContourBad hL s ω} ≤
      contourBudget a k / (1-contourBudget a k) := by
  rw [show {ω | moleculeContourBad hL s ω} = ⋃ j : ℕ, {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
    contourDetoursFailed hL C (fun r ω => ω r) ω} by ext; simp [moleculeContourBad],
    div_eq_mul_inv, ← ENNReal.tsum_geometric_add_one]
  exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => measure_molecule_contours_size_le hL hk s (by omega) a)

end HordijkSteelThreshold
