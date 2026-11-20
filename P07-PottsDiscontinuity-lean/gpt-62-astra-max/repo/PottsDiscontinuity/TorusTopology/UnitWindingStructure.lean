module

public import PottsDiscontinuity.TorusTopology.PositiveLoops
public import PottsDiscontinuity.TorusTopology.VerticalSupport

/-! The exact vertical support when U=1. Horizontal winding is unrestricted. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}

/-- The corrected vertical-loop structure used in Corollary 3.13(ii): precisely two loops,
with opposite unit vertical
windings. There is no horizontal-winding conclusion. -/
theorem U_one_vertical_loop_structure
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
    (hU : rcVerticalWinding hN hM j A = 1) :
    ∃ q₁ q₂ : Loop hN hM (rcSmoothing A), q₁ ≠ q₂ ∧
      (∀ q, (loopVertical j q ≠ 0 ↔
          q = q₁ ∨ q = q₂)) ∧
      loopVertical j q₁ = 1 ∧
      loopVertical j q₂ = -1 := by
  let f := loopVertical
    (h := (checkerArrows_compatible hN hM (rcSmoothing A))) j
  let S := verticalWindingLoops hN hM j A
  have hmem (q) : q ∈ S ↔ f q ≠ 0 := by simp [S,verticalWindingLoops,f]
  have hcard := verticalWindingLoops_card_le_two_of_U_eq_one hN hM j A hU
  have hmass : ∑ q ∈ S, (f q).natAbs = 2 := by
    have he := two_mul_verticalWindingCount hN
      (checkerArrows_compatible hN hM (rcSmoothing A)) j
    change 2 * rcVerticalWinding hN hM j A = _ at he
    have hf : ∑ q ∈ S, (f q).natAbs = verticalMass
        (checkerArrows_compatible hN hM (rcSmoothing A)) j := by
      simp only [S,verticalWindingLoops,Finset.sum_filter,verticalMass]
      grind
    omega
  have hsum : ∑ q ∈ S, f q = 0 := by
    rw [show S = univ.filter (fun q => f q ≠ 0) from rfl,Finset.sum_filter_ne_zero]
    exact sum_vertical_winding_zero hN hM j A
  obtain ⟨q,hq⟩ : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    grind
  obtain ⟨r,hr,hqr⟩ : ∃ r ∈ S, q ≠ r := by
    by_contra h
    have he : S = {q} := by
      grind
    grind
  have he : S = {q,r} := by
    have hsub : ({q,r} : Finset _) ⊆ S := by grind
    exact (Finset.eq_of_subset_of_card_le hsub (by grind)).symm
  grind

end PottsDiscontinuity.TorusTopology
