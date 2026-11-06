module
public import GuthMaynard.Improvement.UpperCurveDensity
public import GuthMaynard.Improvement.CombinedDensityCurve
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped Topology
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
noncomputable section
namespace Montgomery.Refined

/-- New bounds for the moving powered window on the upper interval. -/
theorem refined_scale_bounds {σ : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) :
    8/11 ≤ shortDensityA σ ∧ shortDensityA σ ≤ 4/5 ∧
    0 ≤ shortDensityB σ ∧ shortDensityB σ ≤ 6/5 ∧
    0 < shortDensityExponent σ ∧
    2-2*σ+1/25 ≤ shortDensityExponent σ := by
  pm_1115
  have ha : 8/11 ≤ shortDensityA σ := by
    unfold shortDensityA
    apply (le_div_iff₀ hd).mpr
    linarith
  pm_4534
  · have hg : 2-2*σ+1/22 ≤ shortDensityExponent σ := by
      unfold shortDensityExponent
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg_of_nonpos_of_nonpos
        (show 4*σ-3 ≤ 0 by linarith) (show 77*σ-87 ≤ 0 by linarith)]
    linarith

def refinedSplit (σ : ℝ) : ℝ := (25*σ-15)/((7*σ+3)*(2*σ-1))

theorem refined_split_budgets {σ : ℝ} (hσ : 5/7 ≤ σ) (_hσ' : σ ≤ 3/4) :
    refinedSplit σ*(18/5-4*σ) ≤ shortDensityExponent σ ∧
    1+refinedSplit σ*(1-2*σ) = shortDensityExponent σ := by
  have hd : 0 < (7*σ+3)*(2*σ-1) := mul_pos (by linarith) (by linarith)
  have hne : 7*σ+3 ≠ 0 := by linarith
  have hne' : 2*σ-1 ≠ 0 := by linarith
  constructor
  · have hid : shortDensityExponent σ-refinedSplit σ*(18/5-4*σ) =
        4*(4*σ-3)^2/((7*σ+3)*(2*σ-1)) := by
      unfold shortDensityExponent refinedSplit
      pm_3944
      ring_nf
      pm_3944
      ring
    have hh : 0 ≤ shortDensityExponent σ-refinedSplit σ*(18/5-4*σ) := by
      rw [hid]
      positivity
    linarith
  · unfold shortDensityExponent refinedSplit
    pm_3944
    ring_nf
    pm_3944
    ring

theorem refined_length_budgets {σ H N δ : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100) (hhi : N ≤ H^(shortDensityB σ+δ)) :
    N^δ ≤ H^(2*δ) ∧
    N^(2-2*σ) ≤ H^(shortDensityExponent σ+2*δ) := by
  pm_8222 hB refined_scale_bounds
  have hid := (short_density_scale_identities (show 9/13 ≤ σ by linarith)).1
  constructor
  · calc
      _ ≤ (H^(shortDensityB σ+δ))^δ := Real.rpow_le_rpow hN hhi hδ
      _ = H^((shortDensityB σ+δ)*δ) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH
        (mul_le_mul_of_nonneg_right (by linarith : shortDensityB σ+δ ≤ 2) hδ)
  · calc
      _ ≤ (H^(shortDensityB σ+δ))^(2-2*σ) := Real.rpow_le_rpow hN hhi (by linarith)
      _ = H^((shortDensityB σ+δ)*(2-2*σ)) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (by
        nlinarith [mul_nonneg hδ (show 0 ≤ σ by linarith)])

section
variable {σ H N : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H)
include σ H N hσ hσ' hH
theorem refined_padded_time (hN : 2 ≤ N)
    (hlo : H^(shortDensityA σ) ≤ N) (hhi : N ≤ H^(refinedSplit σ)) :
    ∃ S : ℝ, N^(6/5:ℝ) ≤ S ∧ S ≤ N^(5/3:ℝ) ∧ H ≤ S ∧
      N^(18/7-4*σ)*S^(6/7:ℝ) ≤ H^(shortDensityExponent σ) := by
  pm_4583
  have ha := (refined_scale_bounds hσ hσ').1
  have hid := (short_density_scale_identities (show 9/13 ≤ σ by linarith)).2
  pm_7256
  · refine ⟨H,?_,?_,le_rfl,?_⟩
    · calc
        _ ≤ (H^(5/6:ℝ))^(6/5:ℝ) := Real.rpow_le_rpow hN0.le hm (by norm_num)
        _ = H := by rw [← Real.rpow_mul hH0.le]; norm_num
    · calc
        H = H^(1:ℝ) := (Real.rpow_one H).symm
        _ ≤ H^(shortDensityA σ*(5/3:ℝ)) := Real.rpow_le_rpow_of_exponent_le hH (by linarith)
        _ = (H^(shortDensityA σ))^(5/3:ℝ) := Real.rpow_mul hH0.le _ _
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hlo (by norm_num)
    · calc
        _ ≤ (H^(shortDensityA σ))^(18/7-4*σ)*H^(6/7:ℝ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
            (by positivity) hlo (by linarith)) (by positivity)
        _ = H^(shortDensityA σ*(18/7-4*σ)+6/7) := by
          rw [← Real.rpow_mul hH0.le,← Real.rpow_add hH0]
        _ = _ := by rw [hid]
  · refine ⟨N^(6/5:ℝ),le_rfl,?_,?_,?_⟩
    pm_4582
    · calc
        _ = N^(18/5-4*σ) := by
          pm_694
        _ ≤ (H^(refinedSplit σ))^(18/5-4*σ) :=
          Real.rpow_le_rpow hN0.le hhi (by linarith)
        _ = H^(refinedSplit σ*(18/5-4*σ)) := by rw [← Real.rpow_mul hH0.le]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (refined_split_budgets hσ hσ').1

theorem refined_mean_budget
    (hlo : H^(refinedSplit σ) ≤ N) :
    H*N^(1-2*σ) ≤ H^(shortDensityExponent σ) := by
  have hH0 : 0 < H := by linarith
  calc
    _ ≤ H*(H^(refinedSplit σ))^(1-2*σ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)) hH0.le
    _ = H^(1+refinedSplit σ*(1-2*σ)) := by
      pm_4535
      rw [← Real.rpow_add hH0]
    _ = _ := by rw [(refined_split_budgets hσ hσ').2]
end
set_option hygiene false in
macro "pf_75" x1:term:max x2:term:max : tactic => `(tactic| (
  have hl := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (show (0:ℝ)<1/$x1:term by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    (tendsto_rpow_atTop (show (0:ℝ)<4/5 by norm_num)).eventually_ge_atTop ((2:ℝ)^100)]
    with T hT hlog hconst
  intro a ha ha'
  have ht : 0 < T := by linarith
  constructor
  · have hb : (Real.log T)^4 ≤ T^(1/$x1:term :ℝ) :=
      ((div_lt_one (by positivity)).mp hlog).le
    calc
      _ ≤ T*T^(1/$x1:term :ℝ) := mul_le_mul_of_nonneg_left hb ht.le
      _ = T^($x2:term/$x1:term :ℝ) := by
        nth_rw 1 [← Real.rpow_one T]
        rw [← Real.rpow_add ht]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  · calc
      _ ≤ T^(4/5:ℝ)*T^(3*a/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = T^((4/5:ℝ)+3*a/2) := by rw [← Real.rpow_add ht]
      _ ≤ T^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T^2 := Real.rpow_two T))
/-- Uniform logarithmic buffer for the entire compact target exponent range. -/
theorem refined_power_buffer_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 8/11 ≤ a → a ≤ 4/5 →
      T*(Real.log T)^4 ≤ T^(3*a/2) ∧
      (2:ℝ)^100*T^(3*a/2) ≤ T^2 := by pf_75 11 12

/-- Actual short detection yields a bounded-coefficient powered family in the
full target window, without moving the ordinate. No counting estimate is assumed. -/
theorem refined_powered_cover {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      ((shortPoweredDetectorIndices T).card:ℝ) ≤ 600000*(Real.log T)^2 ∧
      ∀ (a σ : ℝ) (ρ : ℂ), 8/11 ≤ a → a ≤ 4/5 →
        0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 → 1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ shortPoweredDetectorIndices T,
          T^a ≤ (shortPoweredDetectorScale p:ℝ) ∧
          (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*T^(3*a/2) ∧
          2*(shortPoweredDetectorScale p:ℝ) ≤ T^2 ∧
          (shortPoweredDetectorScale p:ℝ)^σ*T^(-2*η) ≤
            ‖detectingPolynomial (shortPoweredDetectorScale p)
              (shortPoweredDetectorFamilyCoeff η T p) ρ.im‖ := by pm_2714 refined_power_buffer_eventually

/-- Actual large values for sigma in [5/7,3/4]. The intermediate lengths
pad the observation time to N^(6/5), preserving the original threshold and
finite set. The middle theorem is invoked only within its proved range. -/
theorem refined_large_values {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ H N t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      5/7 ≤ σ → σ ≤ 3/4 → 2 ≤ H → 2 ≤ N →
      H^(shortDensityA σ) ≤ N → N ≤ H^(shortDensityB σ+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*H^(shortDensityExponent σ+10*δ) := by
  pm_4528
  obtain ⟨hsmall,hpos⟩ := refined_length_budgets hσ hσ' hH1 hN0.le hδ.le hδ' hhi
  pm_97 hdiv2 _hdiv4 hdivM short_density_height_budgets hH0 hN0 σ δ
  pm_6287
  by_cases hm : N ≤ H^(refinedSplit σ)
  · obtain ⟨S,htlo,hthi,hHS,hquartic⟩ := refined_padded_time hσ hσ' hH1 hN hlo hm
    have hS0 : 0 < S := hH0.trans_le hHS
    have hlocS : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+S := by
      intro t ht
      exact ⟨(hloc t ht).1,by linarith [(hloc t ht).2]⟩
    have hc := hmid N S (N^σ*H^(-2*δ)) t₀ a W hN htlo hthi hV ha hlocS hsep hlarge
    rw [hdiv2,upper_window_padded_denominator hH0 hN0 S σ δ] at hc
    pm_4529
    have hb4 : (N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) ≤
        H^(shortDensityExponent σ+8*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ)*H^(8*δ) :=
          mul_le_mul_of_nonneg_right hquartic (by positivity)
        _ = _ := (Real.rpow_add hH0 _ _).symm
    have hsum : N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) ≤
        2*H^(shortDensityExponent σ+8*δ) := by linarith
    have hbudget : C*N^δ*(N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ)) ≤
        (2*C)*H^(shortDensityExponent σ+10*δ) := by
      pm_4530
    pm_4531
  · have hmean := separated_second_moment hN hH0.le a ha W hloc hsep
    pm_4527
    have hmean1 := refined_mean_budget hσ hσ' hH1 (le_of_not_ge hm)
    pm_4526

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
/-- Actual Type-I detection of an ordinate-injective separated finite family.
The constant and height threshold precede sigma, translation and the family. -/
theorem refined_typeI_separated_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ t₀ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by pf_13 refined_large_values refined_powered_cover 8 11 refined_scale_bounds

/-- The Type-I branch count on actual zero-slab representatives. -/
theorem refined_typeI_zero_slab_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by pm_4571 refined_typeI_separated_count

/-- Uniform actual slab density, using the proved weaker moment.
Both separated branch estimates, contour detection and analytic multiplicity
restoration are proved dependencies. -/
theorem refined_slab_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      5/7 ≤ σ → σ ≤ 3/4 →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^((shortDensityExponent σ)+ε) := by
  pm_6200 refined_typeI_zero_slab_count
  pm_4605
  have hσ₀ : 9/13 ≤ σ := by linarith
  have hIIexp := (refined_scale_bounds hσ hσ').2.2.2.2.2
  pm_178 hH1 H hH0
  have hb := hr σ (CI*H^((shortDensityExponent σ)+ε/2))
    (CII*H^((shortDensityExponent σ)+ε/2)) hσ₀ (fun R hR hc hs hl => hi σ R hσ hσ' hR hc hs hl) (by
      intro R hR hc hs hl
      exact (hii σ R hσ₀ hR hc hs hl).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1
          (by linarith)) hCII.le))
  pm_1427
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^((shortDensityExponent σ)+ε/2)+CII*H^((shortDensityExponent σ)+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^((shortDensityExponent σ)+ε/2)+CII*H^((shortDensityExponent σ)+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^((shortDensityExponent σ)+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
end

/-- All actual zeros with analytic multiplicity and both signs. The audited
fixed-sigma dyadic summation is reused, so this constant may depend on sigma. -/
theorem refined_density
    {σ ε : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(shortDensityExponent σ+ε) := by
  obtain ⟨C,hC,hslab⟩ := refined_slab_density hε
  have hp : 0 < (shortDensityExponent σ)+ε := by
    have he := (refined_scale_bounds hσ hσ').2.2.2.2.1
    linarith
  pm_6733

theorem refined_density_middle {σ ε : ℝ}
    (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(18*(1-σ)/(7*σ+3)+ε) := by
  by_cases hs : σ ≤ 5/7
  · exact short_density hσ hs hε
  · exact refined_density (by linarith) hσ' hε

end Montgomery.Refined
