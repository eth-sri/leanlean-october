module
public import AdjacentLargeValues
public import AdjacentWindowParameters
public import HalfLossTypeIISlab
public import TwoTermDetectorCover
public import ThirdZeroDensity
import WeylPort.Analytic.RealLaplace

public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped Topology
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

section
variable {σ a p α ε : ℝ} (hw : AdjacentWindow σ a p α) (hε : 0 < ε)
include σ a p α ε hw hε
/-- Actual Type-I detection with every powered length covered. -/
theorem adjacent_typeI_separated_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (t₀ : ℝ) (R : Finset ℂ),
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(p+ε) := by
  classical
  let η : ℝ := min (ε/1000) (1/100)
  pm_251 hη η
  pm_7855
  pm_7776
  pm_114 C hC hLV adjacent_full_window_large_values hw hη hηsmall
  have hloglim := (isLittleO_log_rpow_rpow_atTop (2:ℝ) hη).tendsto_div_nhds_zero
  norm_num at hloglim
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ), two_term_powered_cover hη,
    shortPoweredDetectorFamily_coefficients hη,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^99),
    (tendsto_rpow_atTop (show (0:ℝ)<7/10 by norm_num)).eventually_ge_atTop 2,
    hloglim.eventually (gt_mem_nhds (show (0:ℝ)<1/600000 by norm_num))]
    with H hH hfamily hcoeff hconst hlength hlog
  intro t₀ R hcard hsep hR
  pm_34 hHpos H hHa
  let J := (shortPoweredDetectorIndices H).filter (fun q =>
    H^(a) ≤ (shortPoweredDetectorScale q:ℝ) ∧
    (shortPoweredDetectorScale q:ℝ) ≤ (2:ℝ)^99*H^(3*a/2) ∧
    2*(shortPoweredDetectorScale q:ℝ) ≤ H^2)
  let W := R.image Complex.im
  let Wj := fun q => W.filter (fun t =>
    (shortPoweredDetectorScale q:ℝ)^σ*H^(-2*η) ≤
      ‖detectingPolynomial (shortPoweredDetectorScale q) (shortPoweredDetectorFamilyCoeff η H q) t‖)
  have hWj : ∀ q ∈ J, ((Wj q).card:ℝ) ≤ C*H^(p+18*η) := by
    intro q hp
    obtain ⟨hp,hlow,hhigh,hsupport⟩ := Finset.mem_filter.mp hp
    have hN : 2 ≤ (shortPoweredDetectorScale q:ℝ) :=
      hlength.trans ((Real.rpow_le_rpow_of_exponent_le hHa hw.a_low).trans hlow)
    have hupper : (shortPoweredDetectorScale q:ℝ) ≤ H^(3*a/2+η) := by
      calc
        _ ≤ (2:ℝ)^99*H^(3*a/2) := hhigh
        _ ≤ H^η*H^(3*a/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = _ := by rw [← Real.rpow_add hHpos]; congr 1; ring
    have hc : ∀ n ∈ sourceRatioIndices (shortPoweredDetectorScale q:ℝ),
        ‖shortPoweredDetectorFamilyCoeff η H q n‖ ≤ 1 := by
      intro n hn
      apply hcoeff q hp hsupport n
      simpa only [sourceRatioIndices, show 2*(shortPoweredDetectorScale q:ℝ) =
        ((2*shortPoweredDetectorScale q:ℕ):ℝ) by push_cast; rfl, Nat.floor_natCast] using hn
    apply hLV H (shortPoweredDetectorScale q:ℝ) t₀
      (shortPoweredDetectorFamilyCoeff η H q) (Wj q) hH hN hlow hupper hc
    · intro t ht
      obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
      exact (hR ρ hρ).2.2.1
    · intro t ht s hs hne
      exact hsep t (Finset.mem_filter.mp ht).1 s (Finset.mem_filter.mp hs).1 hne
    · intro t ht
      simpa only [← detectingPolynomial_eq_boundedPolynomial] using (Finset.mem_filter.mp ht).2
  have hcover : W ⊆ J.biUnion Wj := by
    pm_67 t ht ρ hρ Finset.mem_image.mp
    pm_205 hβ hβ' _hloc hd hR ρ hρ
    obtain ⟨q,hp,hlo,hhi,hsupport,hlarge⟩ := hfamily.2 (a) σ ρ
      hw.a_low hw.a_high (by linarith [hw.sigma_low]) hβ hβ' hd
    apply Finset.mem_biUnion.mpr
    refine ⟨q,Finset.mem_filter.mpr ⟨hp,hlo,hhi,hsupport⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ρ,hρ,rfl⟩,hlarge⟩
  have hJ : (J.card:ℝ) ≤ H^η := by
    have hsmall : 600000*(Real.log H)^2 ≤ H^η := by
      have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hHpos η)).mp hlog
      linarith
    exact (show (J.card:ℝ) ≤ (shortPoweredDetectorIndices H).card by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans (hfamily.1.trans hsmall)
  have hsum : (W.card:ℝ) ≤ (J.card:ℝ)*(C*H^(p+18*η)) := by
    calc
      _ ≤ ∑ q ∈ J, ((Wj q).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ J, C*H^(p+18*η) := Finset.sum_le_sum hWj
      _ = _ := by simp
  have hpow : H^(p+19*η) ≤ H^(p+ε) :=
    Real.rpow_le_rpow_of_exponent_le hHa (by linarith)
  calc
    _ = (W.card:ℝ) := by rw [hcard]
    _ ≤ (J.card:ℝ)*(C*H^(p+18*η)) := hsum
    _ ≤ H^η*(C*H^(p+18*η)) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = C*H^(p+19*η) := by
      rw [← mul_left_comm, ← Real.rpow_add hHpos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC.le



/-- The Type-I branch count on actual zeta zero representatives. -/
theorem adjacent_typeI_zero_slab_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ R : Finset ℂ,
      R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(p+ε) := by pm_2707 adjacent_typeI_separated_count

/-- Actual slabs: the weak Type-II moment is already proved and its exponent
is checked against p. Multiplicity and ordinate collisions are restored. -/
theorem adjacent_slab_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(p+ε) := by pm_2708 adjacent_typeI_zero_slab_count half_loss_typeII_zero_slab_count

/-- End-to-end theorem for actual riemannZeta zeros. AdjacentWindow contains
only explicit algebraic inequalities; no analytic conclusion is assumed. -/
theorem adjacent_density :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) := by
  pm_69 C hC hslab adjacent_slab_density hw hε
  pm_2709
end

/-- Complete second pictured branch, retaining both closed endpoints. -/
theorem adjacent_density_second {σ ε : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 113/153) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(12*(1-σ)/(9*σ-1)+ε) :=
  adjacent_density (adjacent_window_second σ hσ hσ') hε

end Montgomery.RationalMoment
