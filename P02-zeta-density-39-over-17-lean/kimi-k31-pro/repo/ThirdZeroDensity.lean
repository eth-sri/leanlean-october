module
public import ThirdLargeValues
public import ThirdWindowParameters
public import HalfLossTypeIISlab
public import GeneralDetectorCover
public import TwoTermZeroDensity

@[expose] public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

/-- Actual Type-I detection with every powered length covered. -/
theorem third_typeI_separated_count {σ a p α ε : ℝ}
    (hw : ThirdWindow σ a p α) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (t₀ : ℝ) (R : Finset ℂ),
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(p+ε) := by
  apply typeI_separated_count_of_large_values hw.a_low hw.a_high (by linarith [hw.sigma_low]) hε
  intro δ hδ hδ'
  exact third_full_window_large_values hw hδ hδ'

/-- The Type-I branch count on actual zeta zero representatives. -/
theorem third_typeI_zero_slab_count {σ a p α ε : ℝ}
    (hw : ThirdWindow σ a p α) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ R : Finset ℂ,
      R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(p+ε) := by
  obtain ⟨C,hC,hcount⟩ := third_typeI_separated_count hw hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with H hh
  intro R hR hcard hsep hlarge
  apply hh H R hcard hsep
  intro ρ hρ
  obtain ⟨hz,hβ,hγ,hγ'⟩ := mem_zetaZeroFinset.mp (hR hρ)
  exact ⟨hβ,hz.2.2.le,⟨hγ,by linarith⟩,hlarge ρ hρ⟩

/-- Actual slabs: the weak Type-II moment is already proved and its exponent
is checked against p. Multiplicity and ordinate collisions are restored. -/
theorem third_slab_density {σ a p α ε : ℝ}
    (hw : ThirdWindow σ a p α) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(p+ε) := by
  have hη : 0 < ε/2 := by positivity
  obtain ⟨CI,hCI,hI⟩ := third_typeI_zero_slab_count hw hη
  obtain ⟨CII,hCII,hII⟩ := half_loss_typeII_zero_slab_count hη
  obtain ⟨C₀,hC₀,hrestore⟩ := short_slab_count_of_separated_branch_bounds
  let D : ℝ := Real.log 2+1/(ε/2)
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hη)
  refine ⟨C₀*(CI+CII)*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hI,hII,hrestore] with H hH hi hii hr
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hb := hr σ (CI*H^(p+ε/2)) (CII*H^(p+ε/2)) hw.sigma_low
    (fun R hR hc hs hl => hi R hR hc hs hl) (by
      intro R hR hc hs hl
      exact (hii σ R hw.sigma_low hR hc hs hl).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith [hw.typeII])) hCII.le))
  have hlog : Real.log (2*H) ≤ D*H^(ε/2) := classical_log_budget hH1 hη
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^(p+ε/2)+CII*H^(p+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^(p+ε/2)+CII*H^(p+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^(p+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring

/-- End-to-end theorem for actual riemannZeta zeros. ThirdWindow contains
only explicit algebraic inequalities; no analytic conclusion is assumed. -/
theorem third_density {σ a p α ε : ℝ}
    (hw : ThirdWindow σ a p α) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) := by
  obtain ⟨C,hC,hslab⟩ := third_slab_density hw hε
  have hp : 0 < p+ε := by linarith [hw.p_low]
  exact zetaDensity_bound_of_eventual_slabs hp hC hslab

/-- Complete third orange branch on the literal zeta zero count, with
both endpoints closed and no unproved analytic premise. -/
theorem third_density_segment {σ ε : ℝ}
    (hσ : 113/153 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(255*(1-σ)/(153*σ+7)+ε) :=
  third_density (third_window_parameters σ hσ hσ') hε

end Montgomery.RationalMoment
