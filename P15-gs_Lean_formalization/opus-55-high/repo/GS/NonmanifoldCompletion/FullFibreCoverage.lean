module

public import GS.NonmanifoldCompletion.FactorSpace
public import GS.NonmanifoldCompletion.OriginalCoordinates
public import GS.Continuation.CompactCoverageTools

@[expose] public section


/-!
# Coverage of an actual GS neighbourhood by the original compact parametrization

The proof normalizes EACH representative of the full compact fibre, using fixed
local diagonal gauges, local rotation angles, and genuine small logarithms.
It then applies compactness. No normalization or full-fibre coverage assumption
is exposed in the final theorem. The original scalarShuffle, localFamily,
originalF, and originalK definitions are retained.

This theorem supplies `OriginalLocalCoverageGoal` to the final nonmanifold
proof. 
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.Nonmanifold
namespace GS.NonmanifoldCompletion
attribute [local instance] Matrix.normedAddCommGroup

/-- Every full-fibre representative has a parameter neighbourhood whose image
is contained in originalF(K_eta). Gauges are chosen locally, not globally. -/
theorem factor_neighbourhood_in_original_image {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0)
    (η : ℝ) (hη : 0<η) (p : SmallBlockParameters ℝ q) (hp : p∈smallFactorSet ℝ q)
    (he : smallFactorMap p=basePoint Q₀) :
    ∃ N : Set (SmallBlockParameters ℝ q), IsOpen N ∧ p∈N ∧
      ∀ p'∈N, p'∈smallFactorSet ℝ q → smallFactorMap p' ∈ originalF Q₀ '' originalK q η := by
  rcases p with ⟨U,A,B,V⟩
  rcases hp with ⟨hU,hA,hB,hV⟩
  obtain ⟨S,D,E,hS,hD,hE,hleft,hright,hAg,hBg⟩ := normalize_scalar_base_fibre hq
    Q₀ A B hentries U V hU hV (smallFactorMap_eq_base_blocks Q₀ _ he)
  obtain ⟨L,hL,hQL,hlog⟩ := exists_open_frob_small_skew_log Q₀ hQ₀ η hη
  let N : Set (SmallBlockParameters ℝ q) := {p' |
    (∀ i, p'.1 i*D i*S ∈ rotationChartDomain (η/4)) ∧
    (∀ j, Sᵀ*E j*p'.2.2.2 j ∈ rotationChartDomain (η/4)) ∧
    gaugeMiddle D E 0 p'.2.1 ∈ L ∧ gaugeMiddle D E 1 p'.2.2.1 ∈ L}
  have hN : IsOpen N := by
    refine .and ?_ (.and ?_ (.and ?_ ?_))
    any_goals simp only [Set.setOf_forall]; exact isOpen_iInter_of_finite fun i => (isOpen_rotationChartDomain (η/4)).preimage (by fun_prop)
    all_goals exact hL.preimage (by unfold gaugeMiddle; fun_prop)
  have hI : (1 : Mat 2) ∈ rotationChartDomain (η/4) := one_mem_rotationChartDomain (by positivity)
  have hpN : (U,A,B,V)∈N := by
    grind
  refine ⟨N,hN,hpN,?_⟩
  rintro ⟨U',A',B',V'⟩ ⟨hUl,hVr,hAL,hBL⟩ ⟨hU',hA',hB',hV'⟩
  obtain ⟨p',hp',he'⟩ := original_coordinates_of_gauged_near hq Q₀ η hη L hlog
    S D E hS hD hE U' V' A' B' hU' hV' hA' hB' hUl hVr hAL hBL
  tauto

/-- FULL open-neighbourhood coverage for the unchanged original parametrization.
The determinant-one condition is unnecessary for this statement. -/
theorem exists_open_original_local_coverage {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0)
    (η : ℝ) (hη : 0<η) :
    ∃ W : Set (Mat (q*2)), IsOpen W ∧ basePoint Q₀∈W ∧
      ∀ M∈localFamily q, M∈W → ∃ p∈originalK q η, originalF Q₀ p=M := by
  obtain ⟨W,hW,hx,hcover⟩ := compact_full_fibre_neighbourhood (@smallFactorMap ℝ _ q) (continuous_smallFactorMap q) _
    (isCompact_smallFactorSet q) (⋃ N ∈ {N | IsOpen N ∧ ∀ k∈N, k∈smallFactorSet ℝ q → smallFactorMap k ∈ originalF Q₀ '' originalK q η}, N)
    (isOpen_biUnion fun N h => h.1) (basePoint Q₀) fun k hk he => by
      obtain ⟨N,hN,hkN,hmap⟩ := factor_neighbourhood_in_original_image hq Q₀ hQ₀ hentries η hη k hk he
      exact Set.mem_biUnion ⟨hN, hmap⟩ hkN
  refine ⟨W,hW,hx,fun M hM hMW => ?_⟩
  obtain ⟨k,⟨hks,hkO⟩,rfl⟩ := hcover M hMW (by rw [image_smallFactorMap]; aesop)
  simp only [Set.mem_iUnion] at hkO
  obtain ⟨N,⟨-,hN⟩,hkN⟩ := hkO
  simpa using hN k hkN hks

end GS.NonmanifoldCompletion
