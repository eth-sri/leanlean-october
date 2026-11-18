module
public import GuthMaynard.Improvement.GlobalDensityConditional
public import GuthMaynard.Improvement.ShortDetectorContour
public import GuthMaynard.Improvement.ShortDetectorGamma
public import GuthMaynard.Improvement.ShortDetectorLocalMass
public import GuthMaynard.Improvement.ShortDetectorFamilyScales
public import GuthMaynard.Improvement.ShortFixedDetectorFamily
public import GuthMaynard.Improvement.SeparatedSecondMoment
public import GuthMaynard.Improvement.ShortDensityHeight
public import GuthMaynard.Improvement.ShortTypeIIPacking
public import MathCollab.Density.LocalZeroCount
public import MathCollab.Density.Stronger.GenericTaylorFamily
public import MathCollab.Density.Stronger.FiniteConvolution
public import MathCollab.Density.Stronger.Fourth.FourthMoment
public import MathCollab.Density.Packing
public import MathCollab.Density.DensityDyadicSummation
public import MathCollab.Density.MollifierBound
public import MathCollab.Density.DetectorError

@[expose] public section

open Real Complex MeasureTheory Set Filter
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Contour
open MathCollab.Density.ZetaGrowth
open scoped BigOperators Topology ComplexConjugate Interval

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace GuthMaynard.Improvement

/-! ### 1. Local zero count and separated representatives down to `σ = 1/2` -/

private theorem half_unit_bin_sum_le_jensen (σ T : ℝ) (z : ℤ)
    (hσLower : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        zetaMultiplicity ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7/4 : ℝ) / (13/8 : ℝ)) := by
  let S := (zetaZeroFinset σ T (2*T)).filter (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1)
  have hLogDen : 0 < Real.log ((7/4 : ℝ) / (13/8 : ℝ)) := Real.log_pos (by norm_num)
  have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : 1 ≤ T ^ (2 : ℕ) := by nlinarith
    nlinarith
  by_cases hSEmpty : S = ∅
  · change ((∑ ρ ∈ S, zetaMultiplicity ρ : ℕ) : ℝ) ≤ _
    rw [hSEmpty]; simp only [Finset.sum_empty, Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg ((le_div_iff₀ (by norm_num)).mpr (by linarith))) hLogDen.le
  · obtain ⟨ρ₀, hρ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    have hρ₀Data := Finset.mem_filter.mp hρ₀
    obtain ⟨hz₀, hs₀, hlo₀, hhi₀⟩ := mem_zetaZeroFinset.mp hρ₀Data.1
    have hzRange : (z : ℝ) ∈ Set.Icc (T - 1) (2 * T) := ⟨by linarith, by linarith⟩
    let c : ℂ := 2 + I * (((z : ℝ) + 1/2 : ℝ) : ℂ)
    let U : Set ℂ := Metric.closedBall c (7/4 : ℝ)
    have hUAnalytic : AnalyticOnNhd ℂ riemannZeta U := by
      apply analyticOn_riemannZeta.mono
      intro w hw hwOne
      have hwNorm : ‖w - c‖ ≤ 7/4 := by simpa [U, Metric.mem_closedBall, dist_eq_norm] using hw
      have hwImDiff : |w.im - ((z : ℝ) + 1/2)| ≤ 7/4 :=
        (by simp [c] : |w.im - ((z : ℝ) + 1/2)| = |(w - c).im|).trans_le ((abs_im_le_norm _).trans hwNorm)
      have hwIm : 1 < w.im := by linarith [(abs_le.mp hwImDiff).1, hzRange.1]
      subst w; norm_num at hwIm
    have hcLower : (0.6 : ℝ) ≤ ‖riemannZeta c‖ := by simpa [c] using euler_product_lower_bound_2 (z : ℝ)
    have hcNe : riemannZeta c ≠ 0 := fun hcZero => by rw [hcZero, norm_zero] at hcLower; norm_num at hcLower
    have hcOrder : analyticOrderAt riemannZeta c ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hcNe)]; exact ENat.natCast_ne_top 0
    let V : Set ℂ := Metric.closedBall c (13/8 : ℝ)
    have hSV : ∀ ρ ∈ S, ρ ∈ V := by
      intro ρ hρ
      have hρData := Finset.mem_filter.mp hρ
      obtain ⟨hz, hs, _, _⟩ := mem_zetaZeroFinset.mp hρData.1
      rw [Metric.mem_closedBall, dist_eq_norm, mul_self_le_mul_self_iff (norm_nonneg _) (by norm_num),
        Complex.norm_mul_self_eq_normSq, normSq_apply]
      have hre1 : -(3/2 : ℝ) ≤ (ρ - c).re := by simp [c]; linarith [hz.2.2]
      have hre2 : (ρ - c).re ≤ 0 := by simp [c]; linarith [hz.2.2]
      have him1 : -(1/2 : ℝ) ≤ (ρ - c).im := by simp [c]; linarith [hρData.2.1]
      have him2 : (ρ - c).im ≤ 1/2 := by simp [c]; linarith [hρData.2.2]
      nlinarith [sq_nonneg ((ρ - c).re + 3/2), sq_nonneg ((ρ - c).im + 1/2), sq_nonneg ((ρ - c).im - 1/2)]
    have hVAnalytic : AnalyticOnNhd ℂ riemannZeta V :=
      hUAnalytic.mono (Metric.closedBall_subset_closedBall (by norm_num))
    have hBridge := finset_analyticOrderNatAt_le_finsum_divisor hVAnalytic (isCompact_closedBall c _)
      (convex_closedBall c _).isPreconnected (by simp [V, Metric.mem_closedBall]; norm_num) hcOrder S hSV
    have hUAnalyticAbs : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c |(7/4 : ℝ)|) := by
      simpa [U, abs_of_pos (by norm_num : (0 : ℝ) < 7/4)] using hUAnalytic
    have hJensen := hUAnalyticAbs.sum_divisor_le (r := (13/8 : ℝ)) (R := (7/4 : ℝ))
      (M := 100 * T ^ (3 : ℝ)) (by norm_num) (by norm_num) hM hcNe fun w hw =>
      zeta_jensen_sphere_bound T (z : ℝ) hT hzRange w (by simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7/4)] using hw)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 13/8)] at hJensen
    change ((∑ ρ ∈ S, zetaMultiplicity ρ : ℕ) : ℝ) ≤ _
    refine hBridge.trans ((le_trans (by simpa [c, V] using hJensen) ?_))
    apply div_le_div_of_nonneg_right _ hLogDen.le
    have hMPos : 0 < 100 * T ^ (3 : ℕ) := by positivity
    have hcNormPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcNe
    have hRatioLe : (100 * T ^ (3 : ℕ)) / ‖riemannZeta c‖ ≤ (100 * T ^ (3 : ℕ)) / (0.6 : ℝ) :=
      div_le_div_of_nonneg_left hMPos.le (by norm_num) hcLower
    exact Real.log_le_log (div_pos hMPos (by simpa [c] using hcNormPos)) (by simpa [c] using hRatioLe)

private theorem half_local_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → 2 ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ C*Real.log (2*T) := by
  classical
  let D : ℝ := Real.log ((7/4 : ℝ)/(13/8 : ℝ))
  let K : ℝ := 100/D
  let T₀ : ℝ := max (Real.exp 2) 8
  have hD : 0 < D := Real.log_pos (by norm_num)
  have hK : 0 < K := div_pos (by norm_num) hD
  let Q : ℝ := zetaDensityCount (1/2) (2*T₀)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨K+Q/Real.log 4+1, by positivity, fun σ T hσ hT k => ?_⟩
  have hTpos : 0 < T := by linarith
  have hloglow : Real.log 4 ≤ Real.log (2*T) := Real.log_le_log (by norm_num) (by linarith)
  have hlognonneg : 0 ≤ Real.log (2*T) := hlog4.le.trans hloglow
  by_cases hlargeT : T₀ ≤ T
  · have hT8 : 8 ≤ T := (le_max_right _ _).trans hlargeT
    have hTexp : Real.exp 2 ≤ T := (le_max_left _ _).trans hlargeT
    have hlog : 2 ≤ Real.log T := by simpa using Real.log_le_log (Real.exp_pos 2) hTexp
    have hnum : Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) ≤ 100*Real.log T := by
      have hconst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500/3 by norm_num)
      rw [show (100*T^(3 : ℝ))/(0.6 : ℝ) = (500/3 : ℝ)*T^(3 : ℝ) by ring,
        Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTpos 3).ne', Real.log_rpow hTpos]
      nlinarith
    have hcast : (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ))/D := by
      simpa only [D, Nat.cast_sum, ordinateBin_eq_iff] using (half_unit_bin_sum_le_jensen σ T k hσ hT8)
    calc
      _ ≤ (100*Real.log T)/D := hcast.trans (div_le_div_of_nonneg_right hnum hD.le)
      _ = K*Real.log T := by dsimp [K]; ring
      _ ≤ K*Real.log (2*T) := mul_le_mul_of_nonneg_left (Real.log_le_log hTpos (by linarith)) hK.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by have := div_nonneg hQ hlog4.le; linarith) hlognonneg
  · have hTupper : T ≤ T₀ := (not_le.mp hlargeT).le
    have hsum : (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ Q := by
      dsimp [Q]
      exact_mod_cast (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
        (zetaSlabCount_mono hσ (by linarith) (by linarith))
    calc
      _ ≤ (Q/Real.log 4)*Real.log 4 := hsum.trans_eq (div_mul_cancel₀ Q hlog4.ne').symm
      _ ≤ (Q/Real.log 4)*Real.log (2*T) := mul_le_mul_of_nonneg_left hloglow (div_nonneg hQ hlog4.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlognonneg

private theorem half_separated_representatives :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → 2 ≤ T →
      ∃ R : Finset ℂ, R ⊆ zetaZeroFinset σ T (2*T) ∧
        (R.image Complex.im).card = R.card ∧ oneSeparated (R.image Complex.im) ∧
        (zetaSlabCount σ T (2*T) : ℝ) ≤ C*Real.log (2*T)*(R.card : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := half_local_multiplicity_bound
  refine ⟨2*C, by positivity, fun σ T hσ hT => ?_⟩
  obtain ⟨R, hR, hcard, hsep, hcount⟩ := zetaSlab_separated_representatives σ T (2*T)
    (mul_nonneg hC.le (Real.log_nonneg (by linarith))) (hlocal σ T hσ hT)
  exact ⟨R, hR, hcard, hsep, hcount.trans_eq (by ring)⟩

/-! ### 2. Endpoint `σ = 1/2` directly from separated `1`-packing -/

private theorem ingham_at_half {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount (1/2) T : ℝ) ≤ C * T ^ (3 * (1 - (1/2 : ℝ)) / (2 - (1/2 : ℝ)) + ε) := by
  obtain ⟨C₀, hC₀, hrep⟩ := half_separated_representatives
  let D : ℝ := Real.log 2 + 1 / ε
  have hD : 0 < D := add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hε)
  have hslab : ∀ᶠ H : ℝ in atTop, (zetaSlabCount (1/2) H (2*H) : ℝ) ≤ (2*C₀*D)*H^(1+ε) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with H hH
    obtain ⟨R, hR, hcard, hsep, hcount⟩ := hrep (1/2) H le_rfl hH
    let W := R.image Complex.im
    have hWsub : ∀ t ∈ W, t ∈ Icc H (2*H) := by
      intro t ht
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨_, _, hlo, hhi⟩ := mem_zetaZeroFinset.mp (hR hρ)
      exact ⟨hlo, hhi⟩
    have hWcard : (W.card : ℝ) ≤ 2 * H := by
      have hinj : Set.InjOn Int.floor (W : Set ℝ) := by
        intro x hx y hy heq
        by_contra hne
        have h1 : 1 ≤ |x - y| := hsep x hx y hy hne
        have hx0 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
        have hx1 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
        have hy0 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
        have hy1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
        rw [heq] at hx0 hx1
        rcases abs_cases (x - y) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> linarith
      have hmaps : ∀ t ∈ W, ⌊t⌋ ∈ Finset.Icc ⌊H⌋ ⌊2*H⌋ := fun t ht =>
        Finset.mem_Icc.mpr ⟨Int.floor_mono (hWsub t ht).1, Int.floor_mono (hWsub t ht).2⟩
      have hle : W.card ≤ (Finset.Icc ⌊H⌋ ⌊2*H⌋).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
      have hicc : ((Finset.Icc ⌊H⌋ ⌊2*H⌋).card : ℝ) ≤ 2 * H := by
        rw [Int.card_Icc]
        have h1 := Int.floor_le (2 * H)
        have h2 := Int.lt_floor_add_one H
        have : ((⌊2*H⌋ + 1 - ⌊H⌋).toNat : ℝ) = ((⌊2*H⌋ + 1 - ⌊H⌋ : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by have := Int.floor_mono (show H ≤ 2*H by linarith); omega)
        rw [this]; push_cast; linarith
      exact (Nat.cast_le.mpr hle).trans hicc
    have hlog : Real.log (2*H) ≤ D * H ^ ε := classical_log_budget (by linarith) hε
    have hH0 : 0 < H := by linarith
    rw [← hcard] at hcount
    calc
      (zetaSlabCount (1/2) H (2*H) : ℝ) ≤ C₀ * Real.log (2*H) * (W.card : ℝ) := hcount
      _ ≤ C₀ * (D * H ^ ε) * (2 * H) := by gcongr
      _ = (2 * C₀ * D) * (H ^ (1 : ℝ) * H ^ ε) := by rw [Real.rpow_one]; ring
      _ = (2 * C₀ * D) * H ^ (1 + ε) := by rw [← Real.rpow_add hH0]
  have heq : 3 * (1 - (1/2 : ℝ)) / (2 - (1/2 : ℝ)) + ε = 1 + ε := by norm_num
  rw [heq]
  exact zetaDensity_bound_of_eventual_slabs (by linarith) (by positivity) hslab

/-! ### 3. Interior `1/2 < σ ≤ 9/13` via `X = 2 * H^(1/M)` detector + 2nd & 4th moments -/

private def inghamX (M : ℕ) (H : ℝ) : ℝ := 2 * H ^ ((M : ℝ)⁻¹)

private def inghamCoeff (M : ℕ) (T : ℝ) (n : ℕ) : ℂ :=
  if ⌊inghamX M T⌋₊ < n ∧ n < shortDetectorCutoff T then
    (mollifierCoefficient (inghamX M T) n : ℂ) * (Real.exp (-(n : ℝ) / (T ^ (1/2 : ℝ))) : ℂ)
  else 0

private def inghamFiniteDetector (M : ℕ) (ρ : ℂ) (T : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (shortDetectorCutoff T), inghamCoeff M T n * (n : ℂ) ^ (-ρ)

private def inghamTwistedNorm (M : ℕ) (H t : ℝ) : ℝ :=
  ‖riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) * zetaMollifier (inghamX M H) ((1/2 : ℂ) + (t : ℂ) * I)‖

private theorem ingham_mellin_rightContour {σ₀ : ℝ} (hσ₀ : 1/2 < σ₀) {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : σ₀ ≤ ρ.re) :
    smoothedDetector ρ X (1/Y) =
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        detectorKernel ρ X Y (((1/2 : ℝ) : ℂ) + (u : ℂ) * I)) ∧
      Integrable (fun u : ℝ => detectorKernel ρ X Y (((1/2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
  let p₀ : ℝ := 1 + (σ₀ - 1/2) / 2
  have hp₀ : 1 < p₀ := by dsimp [p₀]; linarith
  have hsumP : Summable (fun n : ℕ => (n : ℝ) ^ (-p₀)) := Real.summable_nat_rpow.mpr (by linarith)
  let Pval : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-p₀)
  have hLbound : ∀ z : ℂ, p₀ ≤ z.re → ‖LSeries (mollifierDirichletCoeff X) z‖ ≤ (⌊X⌋₊ : ℝ) * Pval := by
    intro z hz
    have hNorm := summable_norm_iff.mpr (mollifierDirichletCoeff_LSeriesSummable X (hp₀.trans_le hz))
    have hTerm (n : ℕ) : ‖LSeries.term (mollifierDirichletCoeff X) z n‖ ≤ (⌊X⌋₊ : ℝ) * (n : ℝ) ^ (-p₀) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp; positivity
      · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        rw [LSeries.norm_term_eq, ite_eq_right hn, Real.rpow_neg hnPos.le]
        exact (div_le_div_of_nonneg_right (norm_mollifierDirichletCoeff_le_cutoff X n) (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) (Real.rpow_le_rpow_of_exponent_le hnOne hz))
    exact (norm_tsum_le_tsum_norm hNorm).trans ((hNorm.tsum_le_tsum hTerm (hsumP.mul_left _)).trans_eq (tsum_mul_left))
  let line : ℝ → ℂ := fun u => ((1/2 : ℝ) : ℂ) + (u : ℂ) * I
  let g : ℝ → ℂ := fun u => Complex.Gamma (line u) * (riemannZeta (ρ + line u) * zetaMollifier X (ρ + line u))
  have hgCont : Continuous g := by
    refine (continuous_iff_continuousAt.2 fun u => ?_).mul
      ((continuous_iff_continuousAt.2 fun u => ?_).mul (continuous_iff_continuousAt.2 fun u => ?_))
    · exact ContinuousAt.comp' (Complex.differentiableAt_Gamma _ fun m hm => by
        have := congrArg Complex.re hm; simp [line] at this; linarith [Nat.cast_nonneg (α := ℝ) m]).continuousAt
        (by dsimp [line]; fun_prop)
    · exact ContinuousAt.comp' (differentiableAt_riemannZeta fun hz => by
        have := congrArg Complex.re hz; simp [line] at this; linarith).continuousAt (by dsimp [line]; fun_prop)
    · exact ContinuousAt.comp' (differentiableAt_zetaMollifier X _).continuousAt (by dsimp [line]; fun_prop)
  have hGammaInt : Integrable (fun u : ℝ => Complex.Gamma (line u)) := by
    simpa [line, VerticalIntegrable] using GammaMellin.verticalIntegrable_Gamma (sigma := 1/2) (by norm_num)
  have hgInt : Integrable g := by
    refine (hGammaInt.norm.const_mul ((⌊X⌋₊ : ℝ) * Pval)).mono' hgCont.aestronglyMeasurable ?_
    filter_upwards with u
    have hzRe : p₀ ≤ (ρ + line u).re := by simp [line, p₀]; linarith
    dsimp [g]; rw [norm_mul, riemannZeta_mul_zetaMollifier_eq_LSeries X (hp₀.trans_le hzRe)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hLbound _ hzRe) (norm_nonneg _)
  have hVert : VerticalIntegrable (mellin (smoothedDetector ρ X)) (1/2 : ℝ) := by
    refine hgInt.congr ?_; filter_upwards with u
    have hAbs : 1 < (ρ + line u).re := by simp [line]; linarith
    rw [mellin_smoothedDetector_eq (X := X) (by linarith) (by simp [line]) hAbs]
    dsimp [g]
    rw [riemannZeta_mul_zetaMollifier_eq_LSeries X hAbs]
  have hConv : MellinConvergent (smoothedDetector ρ X) ((1/2 : ℝ) : ℂ) := by
    let f := mollifierDirichletCoeff X
    let s : ℂ := ((1/2 : ℝ) : ℂ)
    let term : ℕ → ℝ → ℂ := fun n t => LSeries.term f ρ n * ((t : ℂ) ^ (s - 1) * Real.exp (-(n : ℝ) * t))
    have hs : 0 < s.re := by simp [s]
    have hSumNorm : Summable (fun n => ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re) :=
      (summable_norm_iff.mpr (mollifierDirichletCoeff_LSeriesSummable X (show 1 < (ρ + s).re by simp [s]; linarith))).congr fun n => (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm
    have hTermInt (n : ℕ) : IntegrableOn (term n) (Ioi 0) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [term, LSeries.term]
      · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hGamma := Complex.GammaIntegral_convergent hs
        rw [← mul_zero (n : ℝ), ← integrableOn_Ioi_comp_mul_left_iff _ _ hnPos] at hGamma
        refine (MeasureTheory.IntegrableOn.congr_fun (hGamma.const_mul (1 / (((n : ℝ) : ℂ) ^ (s - 1)))) ?_ measurableSet_Ioi).const_mul _
        intro t ht
        change 1 / (((n : ℝ) : ℂ) ^ (s - 1)) * ((Real.exp (-((n : ℝ) * t)) : ℂ) * ((((n : ℝ) * t : ℝ) : ℂ) ^ (s - 1))) =
          (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)
        rw [mul_comm (Real.exp _ : ℂ), ← mul_assoc, neg_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hnPos.le ht.le, ← mul_assoc, one_div,
          inv_mul_cancel₀ (by rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl (by exact_mod_cast hnPos.ne')), one_mul]
    have hTermSum : Summable (fun n => ∫ t in Ioi 0, ‖term n t‖) := by
      apply Summable.of_norm
      convert! hSumNorm.mul_left (Real.Gamma s.re) using 2 with n
      simp_rw [term, norm_mul (LSeries.term f ρ n), integral_const_mul]
      rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc, norm_mul ‖LSeries.term f ρ n‖, norm_norm]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      congr 1
      have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hReal := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hnPos
      simp_rw [← neg_mul (n : ℝ), one_div, Real.inv_rpow hnPos.le, ← div_eq_inv_mul] at hReal
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hReal]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
          norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
    rw [MellinConvergent]
    refine MeasureTheory.IntegrableOn.congr_fun (integrable_tsum_of_summable_integral_norm hTermInt hTermSum) (fun t ht => ?_) measurableSet_Ioi
    calc
      ∑' n, term n t = ∑' n, (t : ℂ) ^ (s - 1) * (LSeries.term (mollifierDirichletCoeff X) ρ n * Complex.exp (-((n : ℝ) * t))) :=
        tsum_congr fun n => by dsimp [term, f]; rw [Complex.ofReal_exp]; push_cast; ring_nf
      _ = (t : ℂ) ^ (s - 1) * smoothedDetector ρ X t := by simpa [Complex.ofReal_exp] using ((hasSum_smoothedDetector (ρ := ρ) (X := X) ht (by linarith)).mul_left ((t : ℂ) ^ (s - 1))).tsum_eq
  constructor
  · have hInv := mellinInv_mellin_eq (1/2 : ℝ) (smoothedDetector ρ X) (one_div_pos.mpr hY)
      hConv hVert (continuousAt_smoothedDetector (one_div_pos.mpr hY) (by linarith))
    rw [← hInv]; simp only [mellinInv, Complex.real_smul]; congr 1
    apply integral_congr_ae
    filter_upwards with u
    have hAbs : 1 < (ρ + line u).re := by simp [line]; linarith
    have hPow : ((1/Y : ℝ) : ℂ) ^ (-line u) = (Y : ℂ) ^ (line u) := by
      simpa using GammaMellin.cpow_neg_div_eq_reverse_cpow (x := 1) (by norm_num) hY (line u)
    rw [mellin_smoothedDetector_eq (by linarith) (by simp [line]) hAbs]
    change ((1/Y : ℝ) : ℂ) ^ (-line u) * (Complex.Gamma (line u) * LSeries (mollifierDirichletCoeff X) (ρ + line u)) = _
    rw [hPow, ← riemannZeta_mul_zetaMollifier_eq_LSeries X hAbs]; unfold detectorKernel; ring
  · have hp : Continuous (fun u : ℝ => (Y : ℂ) ^ (line u)) :=
      Continuous.cpow continuous_const (by dsimp [line]; fun_prop) fun _ => Or.inl (by simpa using hY)
    refine (hgInt.bdd_mul (c := Y ^ (1/2 : ℝ)) hp.aestronglyMeasurable (Eventually.of_forall fun u => ?_)).congr (Eventually.of_forall fun u => ?_)
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]; simp [line]
    · unfold detectorKernel; dsimp [g]; ring

private theorem ingham_left_integrable {σ₀ : ℝ} (hσ₀ : 1/2 < σ₀) {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hβ : σ₀ ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let a : ℝ := 1/2 - ρ.re
  let line := fun t : ℝ => (a : ℂ) + (t : ℂ) * I
  let Kg : ℝ := 12 / (σ₀ - 1/2)
  have hKg : 0 < Kg := div_pos (by norm_num) (by linarith)
  have hgmaj : Integrable (fun t => (Kg / 48) * detectorGammaMajorant t) :=
    integrable_detectorGammaMajorant.const_mul _
  have hgInt : Integrable (fun t : ℝ => (1 + |t|) * ‖Complex.Gamma (line t)‖) := by
    have hgCont0 : Continuous (fun t : ℝ => (1 + |t|) * ‖Complex.Gamma (line t)‖) :=
      (continuous_const.add continuous_abs).mul
        (short_continuous_Gamma_detector_strip (by dsimp [a]; linarith) (by dsimp [a]; linarith)).norm
    refine hgmaj.mono' hgCont0.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ha : 0 < ρ.re - 1/2 := by linarith
    have h := short_detector_gamma_bound ha (by linarith) t
    rw [show -(ρ.re - 1/2) = a by dsimp [a]; ring] at h
    have hc : 12 / (ρ.re - 1/2) ≤ Kg := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have hh := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))) (by positivity : 0 ≤ 1 + |t|)
    dsimp [detectorGammaMajorant]
    nlinarith [hh, mul_nonneg (abs_nonneg t) (show 0 ≤ Kg * (1 + |t|) * Real.exp (-|t|) by positivity)]
  have he (t : ℝ) : ρ + line t = (1/2 : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I := by apply Complex.ext <;> simp [line, a]
  have hc : Continuous (fun t : ℝ => detectorKernel ρ X Y (line t)) := by
    unfold detectorKernel
    refine (((Continuous.cpow continuous_const (by dsimp [line]; fun_prop) fun _ => Or.inl (by simpa using hY)).mul
      (short_continuous_Gamma_detector_strip (by dsimp [a]; linarith) (by dsimp [a]; linarith))).mul
      (continuous_iff_continuousAt.mpr fun t => ContinuousAt.comp' (differentiableAt_zetaMollifier X _).continuousAt (by dsimp [line]; fun_prop))).mul
      (continuous_iff_continuousAt.mpr fun t => ContinuousAt.comp' (differentiableAt_riemannZeta fun h => by
        rw [he] at h; have := congrArg Complex.re h; norm_num at this).continuousAt (by dsimp [line]; fun_prop))
  let C : ℝ := Y ^ a * (⌊X⌋₊ : ℝ) * 4 * (1 + |ρ.im|)
  refine (hgInt.const_mul C).mono' hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hm := norm_zetaMollifier_le_cutoff X (s := ρ + line t) (by rw [he]; norm_num)
  have hz := norm_riemannZeta_critical_le_linear (ρ.im + t)
  rw [← he] at hz
  have hzt : ‖riemannZeta (ρ + line t)‖ ≤ 4 * (1 + |ρ.im|) * (1 + |t|) := by
    nlinarith [abs_add_le ρ.im t, mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
  dsimp [detectorKernel, line]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have hre : (((a : ℂ) + (t : ℂ) * I)).re = a := by simp
  rw [hre]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hzt (norm_nonneg _) (by positivity)).trans_eq (by dsimp [C]; ring)

private theorem ingham_contour_identity {σ₀ : ℝ} (hσ₀ : 1/2 < σ₀) {ρ : ℂ} {X Y : ℝ}
    (hY : 1 ≤ Y) (hβ : σ₀ ≤ ρ.re) (hβ' : ρ.re < 1) (hZero : riemannZeta ρ = 0) :
    smoothedDetector ρ X (1/Y) = detectorResidue ρ X Y + detectorIntegral ρ X Y := by
  let a : ℝ := 1/2 - ρ.re
  let F := detectorKernel ρ X Y
  let Jl : ℂ := ∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * I)
  let Jr : ℂ := ∫ t : ℝ, F (((1/2 : ℝ) : ℂ) + (t : ℂ) * I)
  let c : ℂ := 1 / (2 * Real.pi * I)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  obtain ⟨hRightEq, hRightInt⟩ := ingham_mellin_rightContour hσ₀ (X := X) hYpos hβ
  have hl := intervalIntegral_tendsto_integral (ingham_left_integrable hσ₀ (X := X) hYpos hβ hβ'.le)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hr := intervalIntegral_tendsto_integral hRightInt
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hhoriz (ε : ℝ) (hε : |ε| = 1) : Tendsto (fun R : ℝ => ∫ u in a..(1/2 : ℝ),
      F ((u : ℂ) + ((ε * R : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    let Ch : ℝ := 60 * Y ^ (1/2 : ℝ) * (⌊X⌋₊ : ℝ) * (2 + |ρ.im|)
    apply squeeze_zero_norm' _ (tendsto_detector_horizontal_majorant Ch)
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with R hR
    have hRpos : 0 < R := by linarith [abs_nonneg ρ.im]
    have he : |ε * R| = R := by rw [abs_mul, hε, one_mul, abs_of_pos hRpos]
    have hlen : |(1/2 : ℝ) - a| ≤ 1 := by
      dsimp [a]; rw [show (1/2 : ℝ) - (1/2 - ρ.re) = ρ.re by ring, abs_of_nonneg (by linarith)]; exact hβ'.le
    have hpt : ∀ u ∈ Set.uIoc a (1/2 : ℝ), ‖F ((u : ℂ) + ((ε * R : ℝ) : ℂ) * I)‖ ≤ Ch * (1 + R) ^ 3 * Real.exp (-R) := by
      intro u hu
      rw [Set.uIoc_of_le (by dsimp [a]; linarith)] at hu
      have h := norm_detectorKernel_horizontal (ρ := ρ) (X := X) (Y := Y) (u := u) (t := ε * R) hY hβ'.le hu.1.le hu.2 (by rw [he]; exact hR)
      rwa [he] at h
    exact (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans
      (by simpa using mul_le_mul_of_nonneg_left hlen (by dsimp [Ch]; positivity))
  have hlim : Tendsto (fun R : ℝ => RectangleIntegral' F ((a : ℂ) - (R : ℂ) * I) (((1/2 : ℝ) : ℂ) + (R : ℂ) * I))
      atTop (𝓝 (c * (I * Jr - I * Jl))) := by
    have h := ((((hhoriz (-1) (by norm_num)).sub (hhoriz 1 (by norm_num))).add (hr.const_smul I)).sub (hl.const_smul I)).const_smul c
    simpa [RectangleIntegral', Contour.RectangleIntegral, Contour.HIntegral, Contour.VIntegral, F, a, Jl, Jr, c, smul_eq_mul] using h
  have heq : ∀ᶠ R : ℝ in atTop, RectangleIntegral' F ((a : ℂ) - (R : ℂ) * I) (((1/2 : ℝ) : ℂ) + (R : ℂ) * I) = detectorResidue ρ X Y := by
    filter_upwards [eventually_gt_atTop |ρ.im|] with R hR
    exact short_detector_finite_rectangle_kernel hYpos (hσ₀.trans_le hβ) hβ' hR hZero
  have he : c * (I * Jr - I * Jl) = detectorResidue ρ X Y :=
    tendsto_nhds_unique hlim ((tendsto_congr' heq).mpr tendsto_const_nhds)
  rw [hRightEq]
  change (((1/(2*Real.pi) : ℝ) : ℂ) * Jr) = detectorResidue ρ X Y + (((1/(2*Real.pi) : ℝ) : ℂ) * Jl)
  rw [← he]; dsimp [c]; push_cast; field_simp; ring

private theorem ingham_alternative {σ₀ : ℝ} (hσ₀ : 1/2 < σ₀) {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ H : ℝ in atTop, ∀ ρ : ℂ,
      σ₀ ≤ ρ.re → ρ.re < 1 → H ≤ |ρ.im| → |ρ.im| ≤ 2 * H → riemannZeta ρ = 0 →
      (1/3 : ℝ) ≤ ‖inghamFiniteDetector M ρ H‖ ∨
      (1/3 : ℝ) ≤ ‖detectorIntegral ρ (inghamX M H) (H ^ (1/2 : ℝ))‖ := by
  let Cg : ℝ := 12 / (σ₀ - 1/2)
  have hCg : 0 < Cg := div_pos (by norm_num) (by linarith)
  have hresLim : Tendsto (fun H : ℝ => (6 * Cg) * (H ^ 3 * Real.exp (-H))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul (6 * Cg)
  have htailLim : Tendsto (fun H : ℝ => 4 * H ^ (-2 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul 4
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 1/2 by norm_num)).eventually_ge_atTop 4,
    Real.tendsto_log_atTop.eventually_ge_atTop 4,
    hresLim.eventually (gt_mem_nhds (show (0 : ℝ) < 1/24 by norm_num)),
    htailLim.eventually (gt_mem_nhds (show (0 : ℝ) < 1/24 by norm_num))]
    with H hH hY4 hlog hres htail ρ hβ hβ' hγ hγ' hzero
  have hHpos : 0 < H := by linarith
  have hYpos : 0 < H ^ (1/2 : ℝ) := by linarith
  have hX1 : 1 ≤ inghamX M H := by
    unfold inghamX; linarith [Real.one_le_rpow hH (show (0 : ℝ) ≤ (M : ℝ)⁻¹ by positivity)]
  have hXle : inghamX M H ≤ 2 * H := by
    unfold inghamX
    have hMinv : (M : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hM)
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH hMinv) (by norm_num : (0 : ℝ) ≤ 2)
  have hK : 1 < shortDetectorCutoff H := by
    have hk : H ^ (1/2 : ℝ) * (Real.log H) ^ 2 ≤ shortDetectorCutoff H := Nat.le_ceil _
    have : (1 : ℝ) < shortDetectorCutoff H := by nlinarith
    exact_mod_cast this
  have hsplit (n : ℕ) (hn : n < shortDetectorCutoff H) :
      detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) n =
        (if n = 1 then (Real.exp (-1 / (H ^ (1/2 : ℝ))) : ℂ) else 0) + inghamCoeff M H n * (n : ℂ) ^ (-ρ) := by
    by_cases hlow : n ≤ ⌊inghamX M H⌋₊
    · have hc : inghamCoeff M H n = 0 := by simp [inghamCoeff, not_lt.mpr hlow]
      rw [hc, zero_mul, add_zero]
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [detectorTerm, mollifierCoefficient]
      rcases eq_or_ne n 1 with rfl | hn1
      · simp [detectorTerm, mollifierCoefficient_one hX1]
      · have hnX : (n : ℝ) ≤ inghamX M H := (Nat.cast_le.mpr hlow).trans (Nat.floor_le (by linarith))
        simp [detectorTerm, mollifierCoefficient_vanishes (by omega) hnX, hn1]
    · have hn1 : n ≠ 1 := fun he => by subst n; exact hlow (Nat.le_floor (by simpa using hX1))
      simp only [hn1, ite_false, zero_add]
      rw [inghamCoeff, ite_eq_left ⟨by omega, hn⟩]; dsimp [detectorTerm]; ring
  have hdecomp : (Real.exp (-1 / (H ^ (1/2 : ℝ))) : ℂ) + inghamFiniteDetector M ρ H +
      (∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) (n + shortDetectorCutoff H)) =
      smoothedDetector ρ (inghamX M H) (1 / (H ^ (1/2 : ℝ))) := by
    have hs := (summable_zeta_detector_series (inghamX M H) hYpos (by linarith)).sum_add_tsum_nat_add (shortDetectorCutoff H)
    have hsum : ∑ n ∈ Finset.range (shortDetectorCutoff H), detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) n =
        (Real.exp (-1 / (H ^ (1/2 : ℝ))) : ℂ) + inghamFiniteDetector M ρ H := by
      simp_rw [Finset.sum_congr rfl fun n hn => hsplit n (Finset.mem_range.mp hn), Finset.sum_add_distrib]
      simp [inghamFiniteDetector, hK]
    have hfull : (∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) n) =
        smoothedDetector ρ (inghamX M H) (1 / (H ^ (1/2 : ℝ))) :=
      tsum_congr fun n => (smoothedDetector_term_eq ρ (inghamX M H) (H ^ (1/2 : ℝ)) n).symm
    change (∑ n ∈ Finset.range (shortDetectorCutoff H), detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) n) +
      (∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) (n + shortDetectorCutoff H)) =
      (∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) n) at hs
    rwa [hsum, hfull] at hs
  have htailB : ‖∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) (n + shortDetectorCutoff H)‖ < 1/24 := by
    refine (norm_detector_tail_le _ _ hYpos (by linarith)).trans_lt (lt_of_le_of_lt ?_ htail)
    have hk : H ^ (1/2 : ℝ) * (Real.log H) ^ 2 ≤ shortDetectorCutoff H := Nat.le_ceil _
    have hexp : Real.exp (-(shortDetectorCutoff H : ℝ) / (H ^ (1/2 : ℝ))) ≤ H ^ (-4 : ℝ) := by
      rw [Real.rpow_def_of_pos hHpos (-4)]; apply Real.exp_le_exp.mpr
      have hq : (Real.log H) ^ 2 ≤ (shortDetectorCutoff H : ℝ) / (H ^ (1/2 : ℝ)) := (le_div_iff₀ hYpos).2 (by nlinarith)
      rw [neg_div]; nlinarith [mul_nonneg (show 0 ≤ Real.log H by linarith) (show 0 ≤ Real.log H - 4 by linarith)]
    have hgeo : (1 - Real.exp (-1 / (H ^ (1/2 : ℝ))))⁻¹ ≤ 2 * H :=
      (detector_geometric_factor_le (by linarith)).trans
        (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hH (by norm_num : (1/2 : ℝ) ≤ 1)) (by norm_num))
    exact (mul_le_mul (mul_le_mul ((Nat.floor_le (by linarith)).trans hXle) hexp (by positivity) (by positivity))
          hgeo (inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) hYpos.le)))) (by positivity)).trans_eq (by
        have he : H ^ (-4 : ℝ) * H ^ 2 = H ^ (-2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_add hHpos]; norm_num
        nlinarith [he])
  have hresB : ‖detectorResidue ρ (inghamX M H) (H ^ (1/2 : ℝ))‖ < 1/24 := by
    refine lt_of_le_of_lt ?_ hres
    have hg : ‖Complex.Gamma (1 - ρ)‖ ≤ Cg * (1 + |ρ.im|) * Real.exp (-|ρ.im|) := by
      have he : 1 - ρ = ((1 - ρ.re : ℝ) : ℂ) + ((-ρ.im : ℝ) : ℂ) * I := by apply Complex.ext <;> simp
      have h0 : ‖Complex.Gamma (1 - ρ)‖ ≤ 12 * (1 + |ρ.im|) * Real.exp (-|ρ.im|) := by
        rw [he]
        simpa [GammaBounds.stripPoint] using GammaBounds.norm_Gamma_compactStrip_le_exp
          (a := 1 - ρ.re) (t := -ρ.im) (by linarith) (by linarith) (by simpa using hH.trans hγ)
      have hCg12 : (12 : ℝ) ≤ Cg := by dsimp [Cg]; rw [le_div_iff₀ (by linarith)]; nlinarith
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCg12 (by positivity)) (by positivity))
    have hp : (H ^ (1/2 : ℝ)) ^ (1 - ρ.re) ≤ H := by
      rw [← Real.rpow_mul hHpos.le]; simpa using Real.rpow_le_rpow_of_exponent_le hH (by linarith : (1/2 : ℝ) * (1 - ρ.re) ≤ 1)
    have hexp : Real.exp (-|ρ.im|) ≤ Real.exp (-H) := Real.exp_le_exp.mpr (by linarith)
    dsimp [detectorResidue]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.sub_re, Complex.one_re]
    calc
      _ ≤ H * (Cg * (3 * H) * Real.exp (-H)) * (2 * H) := by
        refine mul_le_mul (mul_le_mul hp ?_ (norm_nonneg _) (by positivity)) ((norm_zetaMollifier_le_cutoff (inghamX M H) (s := 1) (by norm_num)).trans ((Nat.floor_le (by linarith)).trans hXle)) (norm_nonneg _) (by positivity)
        exact hg.trans (by gcongr; linarith)
      _ = _ := by ring
  have hfirst : (3/4 : ℝ) ≤ Real.exp (-1 / (H ^ (1/2 : ℝ))) := by
    have he := Real.add_one_le_exp (-1 / (H ^ (1/2 : ℝ)))
    have hq : 1 / (H ^ (1/2 : ℝ)) ≤ 1/4 := (div_le_iff₀ hYpos).2 (by linarith)
    rw [neg_div] at he ⊢; linarith
  have hnorm : Real.exp (-1 / (H ^ (1/2 : ℝ))) ≤ ‖detectorResidue ρ (inghamX M H) (H ^ (1/2 : ℝ))‖ +
      ‖detectorIntegral ρ (inghamX M H) (H ^ (1/2 : ℝ))‖ + ‖inghamFiniteDetector M ρ H‖ +
      ‖∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) (n + shortDetectorCutoff H)‖ := by
    have he : (Real.exp (-1 / (H ^ (1/2 : ℝ))) : ℂ) =
        (detectorResidue ρ (inghamX M H) (H ^ (1/2 : ℝ)) + detectorIntegral ρ (inghamX M H) (H ^ (1/2 : ℝ))) -
        inghamFiniteDetector M ρ H - (∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) (n + shortDetectorCutoff H)) := by
      rw [← (ingham_contour_identity hσ₀ (X := inghamX M H) (show 1 ≤ H ^ (1/2 : ℝ) by linarith) hβ hβ' hzero), ← hdecomp]; ring
    have hn : ‖(Real.exp (-1 / (H ^ (1/2 : ℝ))) : ℂ)‖ ≤
        ‖detectorResidue ρ (inghamX M H) (H ^ (1/2 : ℝ))‖ + ‖detectorIntegral ρ (inghamX M H) (H ^ (1/2 : ℝ))‖ +
        ‖inghamFiniteDetector M ρ H‖ + ‖∑' n : ℕ, detectorTerm ρ (inghamX M H) (H ^ (1/2 : ℝ)) (n + shortDetectorCutoff H)‖ := by
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  by_contra hn; push Not at hn; linarith [hn.1, hn.2]

private theorem ingham_typeII_slab_count {σ : ℝ} (hσ : 1/2 < σ) (hσ' : σ ≤ 9/13)
    {M : ℕ} (hM : 1 ≤ M) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ R : Finset ℂ,
      R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3 : ℝ) ≤ ‖detectorIntegral ρ (inghamX M H) (H ^ (1/2 : ℝ))‖) →
      (R.card : ℝ) ≤ C * H ^ (2 - 2 * σ + 2 / (M : ℝ) + η) := by
  classical
  let Cg : ℝ := 12 / (σ - 1/2)
  have hCg : 0 < Cg := div_pos (by norm_num) (by linarith)
  let G : ℝ := (∫ t : ℝ, (Cg / 48) * detectorGammaMajorant t) + 1
  have hG : 0 < G := add_pos_of_nonneg_of_pos (integral_nonneg fun t => by unfold detectorGammaMajorant; positivity) zero_lt_one
  let Kdec : ℝ := 6 * Cg * Real.exp 1
  have hKdec : 0 < Kdec := by dsimp [Kdec]; positivity
  let Jmaj : ℝ := ∫ t : ℝ, detectorGammaMajorant (t / 2)
  have hJmaj : 0 ≤ Jmaj := integral_nonneg fun t => by unfold detectorGammaMajorant; positivity
  let Ctail : ℝ := 4 * Cg * (Jmaj + 1)
  have htailLim : Tendsto (fun H : ℝ => (6 * Ctail) * (H ^ 2 * Real.exp (-(H / 4)))) atTop (𝓝 0) := by
    have hd : Tendsto (fun H : ℝ => H / 4) atTop atTop := Tendsto.atTop_div_const (by norm_num) tendsto_id
    convert ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hd).const_mul (96 * Ctail) using 1
    · funext H; dsimp [Function.comp_def]; ring
    · simp
  obtain ⟨Bf, Hb, hBf, hbf⟩ := Fourth.zeta_fourth_dyadic η hη
  let A : ℝ := 6 ^ 4 * G ^ 3
  let Bpack : ℝ := Kdec * separationMass + 1
  have hBpack : 0 < Bpack := by have := separationMass_nonneg; dsimp [Bpack]; positivity
  let Cm : ℝ := 192 * (Bf + 1) * 2 ^ (1 + η)
  refine ⟨A * Bpack * Cm, by dsimp [A, Cm]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (2 * Hb)),
    htailLim.eventually (gt_mem_nhds (show (0 : ℝ) < 1/6 by norm_num))] with H hH htailSmall R hR hcard hsep hlarge
  have hH2 : 2 ≤ H := (le_max_left _ _).trans hH
  have hHb : 2 * Hb ≤ H := (le_max_right _ _).trans hH
  have hHpos : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hYpos : 0 < H ^ (1/2 : ℝ) := by positivity
  have hXle : (⌊inghamX M H⌋₊ : ℝ) ≤ 2 * H := by
    refine (Nat.floor_le (by unfold inghamX; positivity)).trans ?_
    unfold inghamX
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (inv_le_one_of_one_le₀ (by exact_mod_cast hM))) (by norm_num : (0 : ℝ) ≤ 2)
  have hFcont : Continuous (inghamTwistedNorm M H) := by
    unfold inghamTwistedNorm
    refine Continuous.norm ((continuous_iff_continuousAt.mpr fun t => ?_).mul
      (continuous_iff_continuousAt.mpr fun t => ContinuousAt.comp' (differentiableAt_zetaMollifier _ _).continuousAt (by fun_prop)))
    exact ContinuousAt.comp' (differentiableAt_riemannZeta fun hh => by have := congrArg Complex.re hh; norm_num at this).continuousAt (by fun_prop)
  have hknorm (ρ : ℂ) (t : ℝ) : ‖detectorKernel ρ (inghamX M H) (H ^ (1/2 : ℝ)) (((1/2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖ =
      (H ^ (1/2 : ℝ)) ^ (1/2 - ρ.re) * ‖Complex.Gamma (((1/2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖ * inghamTwistedNorm M H (ρ.im + t) := by
    have he : ρ + (((1/2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I) = (1/2 : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I := by apply Complex.ext <;> simp
    unfold detectorKernel inghamTwistedNorm
    rw [he, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    ring
  have hgbound (β t : ℝ) (hβ : σ ≤ β) (hβ' : β ≤ 1) :
      ‖Complex.Gamma (((1/2 - β : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Cg * (1 + |t|) * Real.exp (-|t|) := by
    have ha : 0 < β - 1/2 := by linarith
    have h := short_detector_gamma_bound ha (by linarith) t
    rw [show -(β - 1/2) = 1/2 - β by ring] at h
    have hc : 12 / (β - 1/2) ≤ Cg := div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < σ - 1/2) (by linarith)
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))
  let W := R.image Complex.im
  have hex : ∀ u : ℝ, ∃ ρ : ℂ, u ∈ W → ρ ∈ R ∧ ρ.im = u := fun u =>
    if hu : u ∈ W then let ⟨ρ, hρ, he⟩ := Finset.mem_image.mp hu; ⟨ρ, fun _ => ⟨hρ, he⟩⟩ else ⟨0, fun hh => (hu hh).elim⟩
  choose ρf hρf using hex
  let J := fun u : ℝ => ∫ v in Icc (-(H/2)) (H/2),
    ‖Complex.Gamma (((1/2 - (ρf u).re : ℝ) : ℂ) + (v : ℂ) * I)‖ * (inghamTwistedNorm M H (u + v)) ^ 4
  have hone (u : ℝ) (hu : u ∈ W) : 1 ≤ A * H ^ (1 - 2 * σ) * J u := by
    obtain ⟨hr, him⟩ := hρf u hu
    obtain ⟨hz, hβ, hlo, hhi⟩ := mem_zetaZeroFinset.mp (hR hr)
    have hβ1 : (ρf u).re ≤ 1 := hz.2.2.le
    let ρ := ρf u
    let K := fun t : ℝ => detectorKernel ρ (inghamX M H) (H ^ (1/2 : ℝ)) (((1/2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)
    have hiK : Integrable K := ingham_left_integrable hσ hYpos hβ hβ1
    have hcpi : ‖((1/(2*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
    have hnormI : (1/3 : ℝ) ≤ ∫ t, ‖K t‖ := (hlarge ρ hr).trans (by
      unfold detectorIntegral; rw [norm_mul]
      exact (mul_le_mul hcpi (norm_integral_le_integral_norm K) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
    let S := Icc (-(H/2)) (H/2)
    have hcomp : Sᶜ = {t : ℝ | H/2 < |t|} := by
      ext t; simp only [S, mem_compl_iff, mem_Icc, ← abs_le, not_le]; rfl
    have hsplit := integral_add_compl (measurableSet_Icc : MeasurableSet S) hiK.norm
    have hsmall : (∫ t in Sᶜ, ‖K t‖) < 1/6 := by
      rw [hcomp]
      let B0 := 4 * Cg * (⌊inghamX M H⌋₊ : ℝ) * (1 + |ρ.im|)
      have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
      have hm := (short_scaled_majorant_integrable.const_mul (B0 * Real.exp (-(H/2)/2)))
      have hcoarse : ∀ t ∈ {t : ℝ | H/2 < |t|}, ‖K t‖ ≤ (B0 * Real.exp (-(H/2)/2)) * detectorGammaMajorant (t / 2) := by
        intro t ht
        dsimp [K]; rw [hknorm]
        have hy1 : (H ^ (1/2 : ℝ)) ^ (1/2 - ρ.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_rpow hH1 (by norm_num)) (by linarith)
        have htw : inghamTwistedNorm M H (ρ.im + t) ≤ 4 * (⌊inghamX M H⌋₊ : ℝ) * (1 + |ρ.im|) * (1 + |t|) := by
          unfold inghamTwistedNorm; rw [norm_mul]
          have hz0 := norm_riemannZeta_critical_le_linear (ρ.im + t)
          have hm0 := norm_zetaMollifier_le_cutoff (inghamX M H) (s := (1/2 : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) (by norm_num)
          have hmul := mul_le_mul hz0 hm0 (norm_nonneg _) (by positivity)
          refine hmul.trans ?_
          have hh : 1 + |ρ.im + t| ≤ (1 + |ρ.im|) * (1 + |t|) := by nlinarith [abs_add_le ρ.im t, mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
          nlinarith [show 0 ≤ (⌊inghamX M H⌋₊ : ℝ) by positivity]
        have h1 := mul_le_mul (mul_le_mul hy1 (hgbound ρ.re t hβ hβ1) (norm_nonneg _) (by norm_num)) htw (norm_nonneg _) (by positivity)
        have h2 := mul_le_mul_of_nonneg_left (short_exponential_tail_domination (show H/2 ≤ |t| from ht.le)) hB0
        refine h1.trans ?_; convert h2 using 1 <;> (dsimp [B0]; ring)
      have hint1 := (setIntegral_mono_on hiK.norm.integrableOn hm.integrableOn (measurableSet_lt measurable_const continuous_abs.measurable) hcoarse).trans
        (setIntegral_le_integral hm (Eventually.of_forall fun t => by unfold detectorGammaMajorant; positivity))
      rw [integral_const_mul] at hint1
      have habs : |ρ.im| ≤ 2 * H := abs_le.mpr ⟨by linarith, hhi⟩
      refine (hint1.trans ?_).trans_lt htailSmall
      have : B0 * Real.exp (-(H/2)/2) * Jmaj ≤ Ctail * (2 * H) * (3 * H) * Real.exp (-(H/4)) := by
        rw [show -(H/2)/2 = -(H/4) by ring]
        have h3H : 1 + |ρ.im| ≤ 3 * H := by linarith
        have hb0le : B0 ≤ 4 * Cg * (2 * H) * (3 * H) := by
          dsimp [B0]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hXle (by positivity)) h3H (by positivity) (by positivity)
        have hbmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb0le (Real.exp_pos (-(H/4))).le) hJmaj
        have hnn : 0 ≤ (2 * H) * (3 * H) * Real.exp (-(H/4)) := by positivity
        dsimp [Ctail]; nlinarith [hbmul, mul_nonneg hCg.le hnn]
      linarith
    have hnear : (1/6 : ℝ) ≤ ∫ t in S, ‖K t‖ := by dsimp [S] at hsmall ⊢; linarith [hnormI, hsplit]
    let g := fun t : ℝ => ‖Complex.Gamma (((1/2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖
    have hgCont : Continuous g := (short_continuous_Gamma_detector_strip (by linarith) (by linarith)).norm
    have heqS : (∫ t in S, ‖K t‖) = (H ^ (1/2 : ℝ)) ^ (1/2 - ρ.re) * ∫ t in S, g t * inghamTwistedNorm M H (u + t) := by
      rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp [K, g]; rw [hknorm, him]; ring
    rw [heqS] at hnear
    have hgmajInt : Integrable (fun t => (Cg / 48) * detectorGammaMajorant t) := integrable_detectorGammaMajorant.const_mul _
    have hgInt : Integrable g := hgmajInt.mono' hgCont.aestronglyMeasurable (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h := hgbound ρ.re t hβ hβ1
      dsimp [detectorGammaMajorant]
      nlinarith [h, mul_nonneg (abs_nonneg t) (show 0 ≤ Cg * (1 + |t|) * Real.exp (-|t|) by positivity)])
    have hgMass : (∫ t in S, g t) ≤ G :=
      (setIntegral_le_integral hgInt (Eventually.of_forall fun _ => norm_nonneg _)).trans
        ((integral_mono hgInt hgmajInt fun t => by
          have h := hgbound ρ.re t hβ hβ1
          dsimp [detectorGammaMajorant]
          nlinarith [h, mul_nonneg (abs_nonneg t) (show 0 ≤ Cg * (1 + |t|) * Real.exp (-|t|) by positivity)]).trans (by dsimp [G]; linarith))
    have hhold := (short_window_fourth_holder (F := fun t => inghamTwistedNorm M H (u + t)) (fun _ => norm_nonneg _) hgCont (hFcont.comp (continuous_const.add continuous_id)) (-(H/2)) (H/2)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) hgMass 3)
        (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (pow_nonneg (by unfold inghamTwistedNorm; positivity) 4)))
    have hpow4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/6) hnear 4
    rw [mul_pow] at hpow4
    have hYpow : ((H ^ (1/2 : ℝ)) ^ (1/2 - ρ.re)) ^ 4 ≤ H ^ (1 - 2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le, ← Real.rpow_mul hHpos.le]
      exact Real.rpow_le_rpow_of_exponent_le hH1 (by nlinarith)
    have hJ0 : 0 ≤ J u := integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg (by unfold inghamTwistedNorm; positivity) 4)
    have hm1 := mul_le_mul_of_nonneg_left hhold (by positivity : 0 ≤ ((H ^ (1/2 : ℝ)) ^ (1/2 - ρ.re)) ^ 4)
    have hm2 := mul_le_mul_of_nonneg_right hYpow (mul_nonneg (by positivity : 0 ≤ G ^ 3) hJ0)
    dsimp [A, J, S, g] at *; nlinarith
  have hsW : (W.card : ℝ) ≤ A * H ^ (1 - 2 * σ) * ∑ u ∈ W, J u := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] using Finset.sum_le_sum hone
  -- Packing bound
  let F4 := fun t => (inghamTwistedNorm M H t) ^ 4
  let q := fun u t : ℝ => Kdec / (1 + |t - u|) ^ 2
  have hf4 : Continuous F4 := hFcont.pow 4
  have hqCont (u : ℝ) : Continuous (q u) := by
    dsimp [q]
    exact continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 2) fun _ => by positivity
  have hiq (u : ℝ) : IntegrableOn (fun t => q u t * F4 t) (Icc (H/2) (3*H)) :=
    ((hqCont u).mul hf4).integrableOn_Icc
  have hpack : (∑ u ∈ W, J u) ≤ Bpack * ∫ t in Icc (H/2) (3*H), F4 t := by
    have honeP (u : ℝ) (hu : u ∈ W) : J u ≤ ∫ t in Icc (H/2) (3*H), q u t * F4 t := by
      obtain ⟨hr, him⟩ := hρf u hu
      obtain ⟨hz, hβ, hlo, hhi⟩ := mem_zetaZeroFinset.mp (hR hr)
      let g := fun v : ℝ => ‖Complex.Gamma (((1/2 - (ρf u).re : ℝ) : ℂ) + (v : ℂ) * I)‖
      have hg : Continuous g := (short_continuous_Gamma_detector_strip (by linarith [hz.2.2]) (by linarith)).norm
      have he : J u = ∫ t in Icc (u - H/2) (u + H/2), g (t - u) * F4 t := by
        simpa only [J, F4, add_sub_cancel_left] using short_setIntegral_comp_add_Icc (fun t => g (t - u) * F4 t) u (H/2)
      rw [he]
      refine (setIntegral_mono_on (((hg.comp (continuous_id.sub continuous_const)).mul hf4).integrableOn_Icc)
        (((hqCont u).mul hf4).integrableOn_Icc)
        measurableSet_Icc fun t _ => mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by unfold inghamTwistedNorm; positivity) 4)).trans
        (setIntegral_mono_set (hiq u) (Eventually.of_forall fun _ => mul_nonneg (by dsimp [q]; positivity) (pow_nonneg (by unfold inghamTwistedNorm; positivity) 4))
          (Eventually.of_forall fun t ht => ⟨by linarith [ht.1, him], by linarith [ht.2, him]⟩))
      have hgb := hgbound (ρf u).re (t - u) hβ hz.2.2.le
      have hp3 := Real.pow_div_factorial_le_exp (1 + |t - u|) (by positivity) 3
      norm_num at hp3
      have he1 : Real.exp (1 + |t - u|) * Real.exp (-|t - u|) = Real.exp 1 := by rw [← Real.exp_add]; congr 1; ring
      apply (le_div_iff₀ (by positivity : 0 < (1 + |t - u|) ^ 2)).mpr
      have hprod : (1 + |t - u|) ^ 3 * Real.exp (-|t - u|) ≤ 6 * Real.exp 1 := by
        calc
          _ ≤ (6 * Real.exp (1 + |t - u|)) * Real.exp (-|t - u|) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ = 6 * Real.exp 1 := by rw [mul_assoc, he1]
      calc
        g (t - u) * (1 + |t - u|) ^ 2 ≤ Cg * (1 + |t - u|) * Real.exp (-|t - u|) * (1 + |t - u|) ^ 2 :=
          mul_le_mul_of_nonneg_right hgb (by positivity)
        _ = Cg * ((1 + |t - u|) ^ 3 * Real.exp (-|t - u|)) := by ring
        _ ≤ Kdec := by dsimp [Kdec]; nlinarith
    calc
      (∑ u ∈ W, J u) ≤ ∑ u ∈ W, ∫ t in Icc (H/2) (3*H), q u t * F4 t := Finset.sum_le_sum honeP
      _ = ∫ t in Icc (H/2) (3*H), ∑ u ∈ W, q u t * F4 t := (integral_finsetSum W fun u _ => hiq u).symm
      _ ≤ ∫ t in Icc (H/2) (3*H), Bpack * F4 t := by
        refine integral_mono (integrable_finsetSum W fun u _ => hiq u) (hf4.integrableOn_Icc.const_mul _) fun t => ?_
        dsimp only; rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by unfold inghamTwistedNorm; positivity) 4)
        have hh := mul_le_mul_of_nonneg_left (separated_decay_row hsep t) hKdec.le
        have he : (∑ u ∈ W, q u t) = Kdec * ∑ u ∈ W, 1 / (1 + |t - u|) ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by dsimp [q]; ring
        dsimp [Bpack]; linarith
      _ = Bpack * ∫ t in Icc (H/2) (3*H), F4 t := integral_const_mul _ _
  -- Fourth moment bound
  have hmom : (∫ t in Icc (H/2) (3*H), F4 t) ≤ Cm * H ^ (1 + 2 / (M : ℝ) + η) := by
    let f0 := fun t => (zetaMomentCriticalNorm t) ^ 4
    have hc0 : Continuous f0 := continuous_zetaMomentCriticalNorm.pow 4
    have hpt (t : ℝ) : F4 t ≤ 64 * H ^ (2 / (M : ℝ)) * f0 t := by
      have hm := norm_zetaMollifier_le_two_sqrt (X := inghamX M H) (s := (1/2 : ℂ) + (t : ℂ) * I) (by unfold inghamX; positivity) (by norm_num)
      have hp : inghamTwistedNorm M H t ≤ zetaMomentCriticalNorm t * (2 * Real.sqrt (inghamX M H)) := by
        unfold inghamTwistedNorm zetaMomentCriticalNorm; rw [norm_mul]
        simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
          mul_le_mul_of_nonneg_left hm (norm_nonneg (riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)))
      have hh := pow_le_pow_left₀ (by unfold inghamTwistedNorm; positivity) hp 4
      have he : (2 * Real.sqrt (inghamX M H)) ^ 4 = 64 * H ^ (2 / (M : ℝ)) := by
        unfold inghamX
        have hs := Real.sq_sqrt (show 0 ≤ 2 * H ^ ((M : ℝ)⁻¹) by positivity)
        calc
          (2 * Real.sqrt (2 * H ^ ((M : ℝ)⁻¹))) ^ 4 = 16 * (Real.sqrt (2 * H ^ ((M : ℝ)⁻¹)) ^ 2) ^ 2 := by ring
          _ = 64 * (H ^ ((M : ℝ)⁻¹)) ^ 2 := by rw [hs]; ring
          _ = 64 * H ^ (2 / (M : ℝ)) := by
            rw [← Real.rpow_natCast (H ^ ((M : ℝ)⁻¹)) 2, ← Real.rpow_mul hHpos.le]; congr 2; ring
      rw [mul_pow, he] at hh; dsimp [F4, f0]; linarith
    have hbnd (x : ℝ) (hx : Hb ≤ x) (hx0 : 0 < x) (hxH : x ≤ 2 * H) : (∫ t in x..2*x, f0 t) ≤ (Bf + 1) * (2 * H) ^ (1 + η) :=
      (hbf x hx hx0).trans (mul_le_mul (by linarith) (Real.rpow_le_rpow hx0.le hxH (by linarith)) (by positivity) (by positivity))
    have h1 := hbnd (H/2) (by linarith) (by positivity) (by linarith)
    have h2 := hbnd H (by linarith) hHpos (by linarith)
    have h3 := hbnd (2*H) (by linarith) (by positivity) le_rfl
    have hs3 : (∫ t in H/2..4*H, f0 t) ≤ 3 * (Bf + 1) * (2 * H) ^ (1 + η) := by
      have hs1 := intervalIntegral.integral_add_adjacent_intervals (hc0.intervalIntegrable (μ := volume) (a := H/2) (b := H)) (hc0.intervalIntegrable (μ := volume) (a := H) (b := 2*H))
      have hs2 := intervalIntegral.integral_add_adjacent_intervals (hc0.intervalIntegrable (μ := volume) (a := H/2) (b := 2*H)) (hc0.intervalIntegrable (μ := volume) (a := 2*H) (b := 4*H))
      rw [show 2 * (H/2) = H by ring] at h1; rw [show 2 * (2*H) = 4*H by ring] at h3; linarith
    have hi0 : (∫ t in Icc (H/2) (3*H), f0 t) ≤ 3 * (Bf + 1) * (2 * H) ^ (1 + η) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      exact (intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
        (Eventually.of_forall fun _ => by dsimp [f0]; positivity) (hc0.intervalIntegrable (μ := volume) (a := H/2) (b := 4*H))).trans hs3
    calc
      _ ≤ ∫ t in Icc (H/2) (3*H), 64 * H ^ (2 / (M : ℝ)) * f0 t :=
        integral_mono hf4.integrableOn_Icc (hc0.const_mul _).integrableOn_Icc hpt
      _ = 64 * H ^ (2 / (M : ℝ)) * ∫ t in Icc (H/2) (3*H), f0 t := integral_const_mul _ _
      _ ≤ 64 * H ^ (2 / (M : ℝ)) * (3 * (Bf + 1) * (2 * H) ^ (1 + η)) := mul_le_mul_of_nonneg_left hi0 (by positivity)
      _ = Cm * H ^ (1 + 2 / (M : ℝ) + η) := by
        dsimp [Cm]; rw [Real.mul_rpow (by norm_num) hHpos.le]
        have : H ^ (2 / (M : ℝ)) * H ^ (1 + η) = H ^ (1 + 2 / (M : ℝ) + η) := by rw [← Real.rpow_add hHpos]; congr 1; ring
        linear_combination 192 * (Bf + 1) * (2 : ℝ) ^ (1 + η) * this
  rw [← hcard]
  calc
    (W.card : ℝ) ≤ A * H ^ (1 - 2 * σ) * (Bpack * (Cm * H ^ (1 + 2 / (M : ℝ) + η))) :=
      hsW.trans (mul_le_mul_of_nonneg_left (hpack.trans (mul_le_mul_of_nonneg_left hmom hBpack.le)) (by dsimp [A]; positivity))
    _ = (A * Bpack * Cm) * (H ^ (1 - 2 * σ) * H ^ (1 + 2 / (M : ℝ) + η)) := by ring
    _ = (A * Bpack * Cm) * H ^ (2 - 2 * σ + 2 / (M : ℝ) + η) := by rw [← Real.rpow_add hHpos]; congr 2; ring

private def inghamBlockArith (M : ℕ) (T : ℝ) (N j : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc N (2 * N) then genericTaylorCoefficient (inghamCoeff M T) N j n else 0
  map_zero' := by simp

private theorem ingham_typeI_slab_count {σ : ℝ} (hσ : 1/2 < σ) (hσ' : σ ≤ 9/13)
    {M : ℕ} (hM : 1 ≤ M) {η : ℝ} (hη : 0 < η) (hηs : η ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ R : Finset ℂ,
      R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3 : ℝ) ≤ ‖inghamFiniteDetector M ρ H‖) →
      (R.card : ℝ) ≤ C * H ^ (3 * (1 - σ) / (2 - σ) + 12 * η) := by
  classical
  let a : ℝ := 1 / (2 - σ)
  have ha_gt : 2/3 < a := by dsimp [a]; rw [lt_div_iff₀ (by linarith)]; linarith
  have ha_hi : a ≤ 13/17 := by dsimp [a]; rw [div_le_iff₀ (by linarith)]; linarith
  have ha_pos : 0 < a := by linarith
  let p : ℝ := 3 * (1 - σ) / (2 - σ)
  let δb : ℝ := (3 * a / 2 - 1) / 2
  have hδb : 0 < δb := by dsimp [δb]; linarith
  let Ch : ℝ := 2 ^ M * (M : ℝ) * 60 ^ M
  have hCh : 0 < Ch := by dsimp [Ch]; positivity
  obtain ⟨Cd, hCd, hdiv⟩ := divisor_card_subpower (show 0 < η / (8 * (M : ℝ)) by positivity)
  let Acoef : ℝ := Cd ^ (2 * M)
  have hAcoef : 1 ≤ Acoef := one_le_pow₀ hCd
  let Dlog : ℝ := Real.log 2 + 1 / η
  have hDlog : 0 < Dlog := add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hη)
  let CLV : ℝ := 102 * (1 + Dlog)
  have hlog4Lim := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) hδb).tendsto_div_nhds_zero
  norm_num at hlog4Lim
  have hlogMLim := (isLittleO_log_rpow_rpow_atTop (M : ℝ) hη).tendsto_div_nhds_zero
  norm_num at hlogMLim
  have hlog2Lim := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).tendsto_div_nhds_zero
  norm_num at hlog2Lim
  refine ⟨CLV, by dsimp [CLV]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    short_detector_family_scales_eventually,
    hlog4Lim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hlogMLim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / Ch by positivity)),
    hlog2Lim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (60 * (M : ℝ) ^ 2) by positivity)),
    (tendsto_rpow_atTop (show (0 : ℝ) < 1/4 by norm_num)).eventually_ge_atTop ((2 : ℝ) ^ M),
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2 : ℝ) ^ M),
    (tendsto_rpow_atTop (show 0 < η / 2 by positivity)).eventually_ge_atTop Acoef,
    (tendsto_rpow_atTop ha_pos).eventually_ge_atTop 2]
    with H hH hsc hbufLog hChLog hcardLog h2M h2Meta hAcoefH hNa2 R hR hcard hsep hlarge
  obtain ⟨_, hlog1, hKsq, hDlog5, hJlog12, hsmallT⟩ := hsc
  have hHpos : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hHgt1 : 1 < H := by linarith
  -- Buffer inequalities
  have hbuf1 : H * (Real.log H) ^ 4 ≤ H ^ (3 * a / 2) := by
    have hb : (Real.log H) ^ 4 ≤ H ^ δb := ((div_lt_one (by positivity)).mp hbufLog).le
    calc
      H * (Real.log H) ^ 4 ≤ H ^ (1 : ℝ) * H ^ δb := by rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hb hHpos.le
      _ = H ^ (1 + δb) := (Real.rpow_add hHpos 1 δb).symm
      _ ≤ H ^ (3 * a / 2) := Real.rpow_le_rpow_of_exponent_le hH1 (by dsimp [δb]; linarith)
  have hbuf2 : (2 : ℝ) ^ M * H ^ (3 * a / 2) ≤ H ^ 2 := by
    calc
      (2 : ℝ) ^ M * H ^ (3 * a / 2) ≤ H ^ (1/4 : ℝ) * H ^ (3 * a / 2) := mul_le_mul_of_nonneg_right h2M (by positivity)
      _ = H ^ (1/4 + 3 * a / 2) := (Real.rpow_add hHpos _ _).symm
      _ ≤ H ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H ^ 2 := Real.rpow_two H
  let idxSet : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (fixedShortDetectorIndices H).product ((Finset.Icc 1 M).product (Finset.range M))
  let scOf := fun q : (ℕ × ℕ) × (ℕ × ℕ) => 2 ^ q.2.2 * (2 ^ q.1.1) ^ q.2.1
  let cfOf := fun (q : (ℕ × ℕ) × (ℕ × ℕ)) (n : ℕ) =>
    conj (((inghamBlockArith M H (2 ^ q.1.1) q.1.2) ^ q.2.1) n) / ((H ^ η : ℝ) : ℂ)
  let J := idxSet.filter fun q =>
    H ^ a ≤ (scOf q : ℝ) ∧ (scOf q : ℝ) ≤ (2 : ℝ) ^ M * H ^ (3 * a / 2) ∧ 2 * (scOf q : ℝ) ≤ H ^ 2
  let W := R.image Complex.im
  let Wj := fun q => W.filter fun t => (scOf q : ℝ) ^ σ * H ^ (-2 * η) ≤ ‖detectingPolynomial (scOf q) (cfOf q) t‖
  have hcoeffNorm (N j : ℕ) (hN : 0 < N) : ∀ n ∈ Finset.Ioc N (2 * N), ‖inghamCoeff M H n‖ ≤ (n.divisors.card : ℝ) := by
    intro n _
    unfold inghamCoeff
    split_ifs with h
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(n : ℝ) / (H ^ (1/2 : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by positivity))
      exact (mul_le_mul (mollifierCoefficient_norm_le _ _) he (by positivity) (by positivity)).trans_eq (mul_one _)
    · simp
  -- Cover W
  have hcover : W ⊆ J.biUnion Wj := by
    intro t ht
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hz, hβ, _, _⟩ := mem_zetaZeroFinset.mp (hR hρ)
    have hβ1 : ρ.re ≤ 1 := hz.2.2.le
    -- Dyadic decomposition of inghamFiniteDetector
    let K := shortDetectorCutoff H
    let L := shortDetectorDyadicCount H
    have hLpos : 0 < L := by unfold L shortDetectorDyadicCount; omega
    have hX1 : 1 ≤ ⌊inghamX M H⌋₊ := Nat.le_floor (by
      unfold inghamX; linarith [Real.one_le_rpow hH1 (show (0 : ℝ) ≤ (M : ℝ)⁻¹ by positivity)])
    have hdyad : inghamFiniteDetector M ρ H = ∑ r ∈ Finset.range L, genericBlock ρ (inghamCoeff M H) (2 ^ r) := by
      let f := fun n : ℕ => inghamCoeff M H n * (n : ℂ) ^ (-ρ)
      have hKL : K < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) K
      have hs1 : ∑ n ∈ Finset.range K, f n = ∑ n ∈ Finset.range (2 ^ L + 1), f n :=
        Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn' => by
          have hz0 : ¬ n < shortDetectorCutoff H := by simpa [K] using hn'
          dsimp [f, inghamCoeff]; rw [ite_eq_right (fun h => hz0 h.2), zero_mul]
      have hs2 : ∑ n ∈ Finset.Ioc 1 (2 ^ L), f n = ∑ n ∈ Finset.range (2 ^ L + 1), f n :=
        Finset.sum_subset (fun n hn => Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp hn).2; omega)) fun n hn hn' => by
          have hnr := Finset.mem_range.mp hn
          have hni : ¬ (1 < n ∧ n ≤ 2 ^ L) := by simpa using hn'
          have hz0 : ¬ ⌊inghamX M H⌋₊ < n := by omega
          dsimp [f, inghamCoeff]; rw [ite_eq_right (fun h => hz0 h.1), zero_mul]
      change ∑ n ∈ Finset.range K, f n = _
      rw [hs1, ← hs2, ← sum_dyadic_Ioc f L]; rfl
    have hexR : ∃ r ∈ Finset.range L, (1/3 : ℝ) / (L : ℝ) ≤ ‖genericBlock ρ (inghamCoeff M H) (2 ^ r)‖ := by
      by_contra h; push Not at h
      have hlt : (∑ r ∈ Finset.range L, ‖genericBlock ρ (inghamCoeff M H) (2 ^ r)‖) < 1/3 := by
        have hne : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
        refine (Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hLpos⟩ h).trans_eq ?_
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; exact mul_div_cancel₀ _ hne
      have hge1 := hlarge ρ hρ
      rw [hdyad] at hge1
      have hge := hge1.trans (norm_sum_le _ _)
      linarith
    obtain ⟨r, hr, hblk⟩ := hexR
    let N0 : ℕ := 2 ^ r
    have hN0 : 0 < N0 := by positivity
    have hblkNe : genericBlock ρ (inghamCoeff M H) N0 ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (div_pos (by norm_num) (by exact_mod_cast hLpos)) hblk)
    obtain ⟨n0, hn0Ioc, hn0Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblkNe
    have hcNe : inghamCoeff M H n0 ≠ 0 := left_ne_zero_of_mul hn0Ne
    have hsupp : inghamX M H < (n0 : ℝ) ∧ (n0 : ℝ) < H ^ (1/2 : ℝ) * (Real.log H) ^ 2 := by
      have hs : ⌊inghamX M H⌋₊ < n0 ∧ n0 < shortDetectorCutoff H := by by_contra hh; simp [inghamCoeff, hh] at hcNe
      exact ⟨(Nat.floor_lt (by unfold inghamX; positivity)).mp hs.1, Nat.lt_ceil.mp hs.2⟩
    have hN0lo : H ^ ((M : ℝ)⁻¹) < (N0 : ℝ) := by
      have : (n0 : ℝ) ≤ 2 * N0 := by exact_mod_cast (Finset.mem_Ioc.mp hn0Ioc).2
      unfold inghamX at hsupp; linarith
    have hN0hi : (N0 : ℝ) < H ^ (1/2 : ℝ) * (Real.log H) ^ 2 := by
      have : (N0 : ℝ) < n0 := by exact_mod_cast (Finset.mem_Ioc.mp hn0Ioc).1
      linarith
    have hN0sq : (N0 : ℝ) ≤ H ^ 2 := hN0hi.le.trans ((Nat.le_ceil _).trans hKsq)
    obtain ⟨j, hj, hcomp⟩ := exists_genericTaylor_component (hcoeffNorm N0 0 hN0) hH1 hN0 hN0sq
      (by linarith) hβ1 (D := (3/2 : ℝ) * L) (by positivity)
      (by convert hsmallT using 1; ring) (by convert hblk using 1; ring)
    have hcomp' : (N0 : ℝ) ^ σ / (60 * Real.log H) ≤ ‖genericTaylorPolynomial (inghamCoeff M H) N0 j ρ.im‖ := by
      have hp : (N0 : ℝ) ^ σ ≤ (N0 : ℝ) ^ ρ.re := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN0) hβ
      have hden : 8 * ((3/2 : ℝ) * L) ≤ 60 * Real.log H := by linarith
      exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans
        ((div_le_div_of_nonneg_right hp (by positivity)).trans hcomp)
    -- Powering k ≤ M
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hMpow : H ^ a ≤ (N0 : ℝ) ^ M := by
      have hp := pow_le_pow_left₀ (Real.rpow_nonneg hHpos.le _) hN0lo.le M
      rw [← Real.rpow_mul_natCast hHpos.le, inv_mul_cancel₀ hMne, Real.rpow_one] at hp
      have ha1 : H ^ a ≤ H := by simpa using Real.rpow_le_rpow_of_exponent_le hH1 (show a ≤ 1 by linarith)
      exact ha1.trans hp
    let hexK : ∃ k : ℕ, H ^ a ≤ (N0 : ℝ) ^ k := ⟨M, hMpow⟩
    let k := Nat.find hexK
    have hklo : H ^ a ≤ (N0 : ℝ) ^ k := Nat.find_spec hexK
    have hkM : k ≤ M := Nat.find_min' hexK hMpow
    have hkpos : 0 < k := by
      by_contra hh; have hz0 : k = 0 := by omega
      rw [hz0, pow_zero] at hklo; exact (not_le_of_gt (Real.one_lt_rpow hHgt1 ha_pos)) hklo
    have hN0gt1 : 1 < (N0 : ℝ) := (Real.one_le_rpow hH1 (by positivity)).trans_lt hN0lo
    have hkhi : (N0 : ℝ) ^ k ≤ H ^ (3 * a / 2) := by
      by_cases hk2 : k ≤ 2
      · have hsq := pow_le_pow_left₀ (by positivity) hN0hi.le 2
        have he : (H ^ (1/2 : ℝ) * (Real.log H) ^ 2) ^ 2 = H * (Real.log H) ^ 4 := by
          rw [mul_pow, ← Real.rpow_mul_natCast hHpos.le]
          norm_num only [Nat.cast_ofNat, show (1/2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
          ring
        rw [he] at hsq
        exact (pow_le_pow_right₀ hN0gt1.le hk2).trans (hsq.trans hbuf1)
      · have hprev : (N0 : ℝ) ^ (k - 1) < H ^ a := lt_of_not_ge (Nat.find_min hexK (by omega))
        have hloglt := Real.log_lt_log (by positivity : (0 : ℝ) < (N0 : ℝ) ^ (k - 1)) hprev
        rw [Real.log_pow, Real.log_rpow hHpos, Nat.cast_sub (by omega), Nat.cast_one] at hloglt
        have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
        have hln : 0 ≤ Real.log (N0 : ℝ) := Real.log_nonneg hN0gt1.le
        rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_rpow hHpos]
        nlinarith
    have hfSupp : ∀ n, inghamBlockArith M H N0 j n ≠ 0 → n ∈ Finset.Ioc N0 (2 * N0) := by
      intro n hn; by_contra hh; exact hn (by change (if n ∈ Finset.Ioc N0 (2 * N0) then _ else 0) = 0; simp [hh])
    obtain ⟨ℓ, hℓ, hpiece⟩ := exists_finiteBlock_powered_piece hN0 hkpos hfSupp ρ.im
    have hLS_eq : ‖LSeries (inghamBlockArith M H N0 j) (I * (ρ.im : ℂ))‖ = ‖genericTaylorPolynomial (inghamCoeff M H) N0 j ρ.im‖ := by
      rw [genericTaylorPolynomial, norm_detectingPolynomial_eq_cpow_sum hN0, LSeries, tsum_eq_sum (s := Finset.Ioc N0 (2 * N0))]
      · exact congrArg norm (Finset.sum_congr rfl fun n hn => by
          rw [LSeries.term_def₀ (inghamBlockArith M H N0 j).map_zero]
          change (if n ∈ Finset.Ioc N0 (2 * N0) then genericTaylorCoefficient (inghamCoeff M H) N0 j n else 0) * _ = _
          rw [ite_eq_left hn])
      · intro n hn
        rw [LSeries.term_def₀ (inghamBlockArith M H N0 j).map_zero]
        change (if n ∈ Finset.Ioc N0 (2 * N0) then genericTaylorCoefficient (inghamCoeff M H) N0 j n else 0) * _ = 0
        rw [ite_eq_right hn, zero_mul]
    rw [hLS_eq] at hpiece
    let q : (ℕ × ℕ) × (ℕ × ℕ) := ((r, j), (k, ℓ))
    have hℓM : ℓ < M := lt_of_lt_of_le (Finset.mem_range.mp hℓ) hkM
    have hqIdx : q ∈ idxSet := by
      dsimp only [idxSet, q]
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hr, hj⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hkM⟩, Finset.mem_range.mpr hℓM⟩⟩
    have hscLo : H ^ a ≤ (scOf q : ℝ) := by
      change H ^ a ≤ ((2 ^ ℓ * N0 ^ k : ℕ) : ℝ); push_cast
      have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
      exact hklo.trans (by nlinarith [pow_nonneg (Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0) k])
    have hscHi : (scOf q : ℝ) ≤ (2 : ℝ) ^ M * H ^ (3 * a / 2) := by
      change ((2 ^ ℓ * N0 ^ k : ℕ) : ℝ) ≤ _; push_cast
      exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hℓM.le) hkhi (by positivity) (by positivity)
    have hsc2 : 2 * (scOf q : ℝ) ≤ H ^ 2 := by
      change 2 * ((2 ^ ℓ * N0 ^ k : ℕ) : ℝ) ≤ _; push_cast
      calc
        2 * ((2 : ℝ) ^ ℓ * (N0 : ℝ) ^ k) = (2 : ℝ) ^ (ℓ + 1) * (N0 : ℝ) ^ k := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ M * H ^ (3 * a / 2) := mul_le_mul (pow_le_pow_right₀ (by norm_num) hℓM) hkhi (by positivity) (by positivity)
        _ ≤ H ^ 2 := hbuf2
    have hChB : Ch * (Real.log H) ^ M ≤ H ^ η := by
      have hb := (div_lt_iff₀ (by positivity : 0 < H ^ η)).mp hChLog
      have hm := mul_le_mul_of_nonneg_left hb.le hCh.le
      exact hm.trans_eq (by field_simp [hCh.ne'])
    have hheight : (scOf q : ℝ) ^ σ * H ^ (-2 * η) ≤ ‖detectingPolynomial (scOf q) (cfOf q) ρ.im‖ := by
      have hscScale : (scOf q : ℝ) ^ σ ≤ (2 : ℝ) ^ M * ((N0 : ℝ) ^ σ) ^ k := by
        change (((2 ^ ℓ * N0 ^ k : ℕ) : ℝ) ^ σ) ≤ _; push_cast
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (Nat.cast_nonneg N0),
          mul_comm (k : ℝ) σ, Real.rpow_mul_natCast (Nat.cast_nonneg N0)]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (show σ ≤ 1 by linarith)).trans
          (by simpa only [Real.rpow_one] using (pow_le_pow_right₀ (by norm_num) hℓM.le : (2 : ℝ) ^ ℓ ≤ 2 ^ M))
      have hdenM : (k : ℝ) * (60 * Real.log H) ^ k ≤ (M : ℝ) * 60 ^ M * (Real.log H) ^ M := by
        simpa only [mul_pow, mul_assoc] using mul_le_mul (by exact_mod_cast hkM : (k : ℝ) ≤ M)
          (pow_le_pow_right₀ (show (1 : ℝ) ≤ 60 * Real.log H by linarith) hkM) (by positivity) (by positivity)
      have hpowD := pow_le_pow_left₀ (by positivity) hcomp' k
      have hraw : (scOf q : ℝ) ^ σ / (Ch * (Real.log H) ^ M) ≤
          ‖detectingPolynomial (scOf q) (fun n => conj (((inghamBlockArith M H N0 j) ^ k) n)) ρ.im‖ := by
        calc
          _ ≤ ((2 : ℝ) ^ M * ((N0 : ℝ) ^ σ) ^ k) / (Ch * (Real.log H) ^ M) := div_le_div_of_nonneg_right hscScale (by positivity)
          _ = ((N0 : ℝ) ^ σ) ^ k / ((M : ℝ) * 60 ^ M * (Real.log H) ^ M) := by
            dsimp [Ch]; rw [mul_assoc ((2 : ℝ) ^ M), mul_assoc ((2 : ℝ) ^ M),
              mul_div_mul_left _ _ (by positivity : (2 : ℝ) ^ M ≠ 0)]
          _ ≤ ((N0 : ℝ) ^ σ) ^ k / ((k : ℝ) * (60 * Real.log H) ^ k) := div_le_div_of_nonneg_left (by positivity) (by positivity) hdenM
          _ = ((N0 : ℝ) ^ σ / (60 * Real.log H)) ^ k / (k : ℝ) := by rw [div_pow]; ring
          _ ≤ _ := (div_le_div_of_nonneg_right hpowD (by positivity)).trans hpiece
      have hdivEq : detectingPolynomial (scOf q) (cfOf q) ρ.im =
          detectingPolynomial (scOf q) (fun n => conj (((inghamBlockArith M H N0 j) ^ k) n)) ρ.im / ((H ^ η : ℝ) : ℂ) := by
        simp only [detectingPolynomial, cfOf, q, Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hdivEq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hHpos η)]
      calc
        (scOf q : ℝ) ^ σ * H ^ (-2 * η) = (scOf q : ℝ) ^ σ / H ^ η / H ^ η := by
          rw [div_div, ← Real.rpow_add hHpos, div_eq_mul_inv, ← Real.rpow_neg hHpos.le]; congr 2; ring
        _ ≤ ((scOf q : ℝ) ^ σ / (Ch * (Real.log H) ^ M)) / H ^ η :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) (by positivity) hChB) (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_right hraw (by positivity)
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨hqIdx, hscLo, hscHi, hsc2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩, hheight⟩⟩
  -- Bound each Wj by separated_second_moment
  have hWj (q : (ℕ × ℕ) × (ℕ × ℕ)) (hq : q ∈ J) : ((Wj q).card : ℝ) ≤ CLV * H ^ (p + 10 * η) := by
    obtain ⟨hqIdx, hlo, hhi, h2sq⟩ := Finset.mem_filter.mp hq
    let N : ℝ := scOf q
    have hN2 : 2 ≤ N := hNa2.trans hlo
    have hN0 : 0 < N := by linarith
    have hupper : N ≤ H ^ (3 * a / 2 + η) := by
      calc
        N ≤ (2 : ℝ) ^ M * H ^ (3 * a / 2) := hhi
        _ ≤ H ^ η * H ^ (3 * a / 2) := mul_le_mul_of_nonneg_right h2Meta (by positivity)
        _ = H ^ (3 * a / 2 + η) := by rw [← Real.rpow_add hHpos]; congr 1; ring
    have hcBound : ∀ n ∈ sourceRatioIndices N, ‖cfOf q n‖ ≤ 1 := by
      intro n hn
      have hn2 : (n : ℝ) ≤ H ^ 2 := by
        have : (n : ℝ) ≤ 2 * N := by
          simpa only [sourceRatioIndices, N, show 2 * (scOf q : ℝ) = ((2 * scOf q : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
            using (show (n : ℝ) ≤ ⌊2 * N⌋₊ by exact_mod_cast (Finset.mem_Ioc.mp hn).2)
        exact this.trans h2sq
      dsimp [cfOf]
      rw [norm_div, norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hHpos η),
        div_le_one (by positivity)]
      rcases eq_or_ne n 0 with rfl | hn0
      · simp; positivity
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hqIdx' : q ∈ (fixedShortDetectorIndices H).product ((Finset.Icc 1 M).product (Finset.range M)) := hqIdx
      have hk_le : q.2.1 ≤ M := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hqIdx').2).1).2
      have hcard1 : (1 : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hnpos.ne'⟩
      have hbase_le : ∀ m, ‖inghamBlockArith M H (2 ^ q.1.1) q.1.2 m‖ ≤ (m.divisors.card : ℝ) := fun m => by
        dsimp [inghamBlockArith]; split_ifs with hm
        · exact norm_genericTaylorCoefficient_le (hcoeffNorm _ 0 (by positivity)) (by positivity) hm _
        · simp
      have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      calc
        ‖((inghamBlockArith M H (2 ^ q.1.1) q.1.2) ^ q.2.1) n‖ ≤ (n.divisors.card : ℝ) ^ (2 * q.2.1) :=
          arithmeticFunction_pow_norm_le hbase_le q.2.1 n
        _ ≤ (n.divisors.card : ℝ) ^ (2 * M) := pow_le_pow_right₀ hcard1 (by omega)
        _ ≤ (Cd * (n : ℝ) ^ (η / (8 * (M : ℝ)))) ^ (2 * M) := pow_le_pow_left₀ (by positivity) (hdiv n hnpos) _
        _ = Acoef * (n : ℝ) ^ (η / 4) := by
          dsimp [Acoef]; rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]; congr 2; push_cast
          field_simp [hMne]; ring
        _ ≤ Acoef * (H ^ 2) ^ (η / 4) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn2 (by positivity)) (by linarith)
        _ = Acoef * H ^ (η / 2) := by rw [← Real.rpow_natCast_mul hHpos.le]; congr 2; norm_num; ring
        _ ≤ H ^ (η / 2) * H ^ (η / 2) := mul_le_mul_of_nonneg_right hAcoefH (by positivity)
        _ = H ^ η := by rw [← Real.rpow_add hHpos]; congr 1; ring
    have hV : 0 < N ^ σ * H ^ (-2 * η) := by positivity
    have hlocW : ∀ t ∈ Wj q, H ≤ t ∧ t ≤ H + H := by
      intro t ht; obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
      obtain ⟨_, _, h1, h2⟩ := mem_zetaZeroFinset.mp (hR hρ); exact ⟨h1, by linarith⟩
    have hsepW : ∀ t ∈ Wj q, ∀ s ∈ Wj q, t ≠ s → 1 ≤ |t - s| := fun t ht s hs =>
      hsep t (Finset.mem_filter.mp ht).1 s (Finset.mem_filter.mp hs).1
    have hlargeW : ∀ t ∈ Wj q, N ^ σ * H ^ (-2 * η) ≤ ‖boundedPolynomial N (cfOf q) t‖ := fun t ht => by
      simpa only [N, ← detectingPolynomial_eq_boundedPolynomial] using (Finset.mem_filter.mp ht).2
    have hmean := separated_second_moment hN2 hHpos.le (cfOf q) hcBound (Wj q) hlocW hsepW
    obtain ⟨_, _, hdivM⟩ := short_density_height_budgets hHpos hN0 σ η
    have hcardW : ((Wj q).card : ℝ) * (N ^ σ * H ^ (-2 * η)) ^ 2 ≤ 102 * N * (H + N * Real.log (2 * N)) :=
      (by simp : _ = ∑ _t ∈ Wj q, _).trans_le ((Finset.sum_le_sum fun t ht => pow_le_pow_left₀ hV.le (hlargeW t ht) 2).trans hmean)
    have hcW : ((Wj q).card : ℝ) ≤ 102 * ((H * N ^ (1 - 2 * σ) + N ^ (2 - 2 * σ) * Real.log (2 * N)) * H ^ (4 * η)) := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hV)).mpr hcardW
      rwa [show 102 * N * (H + N * Real.log (2 * N)) / (N ^ σ * H ^ (-2 * η)) ^ 2 =
        102 * (N * (H + N * Real.log (2 * N)) / (N ^ σ * H ^ (-2 * η)) ^ 2) by ring, hdivM] at hh
    have hsmallN : N ^ η ≤ H ^ (2 * η) :=
      (Real.rpow_le_rpow hN0.le hupper hη.le).trans
        ((Real.rpow_mul hHpos.le _ _).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hH1 (by nlinarith)))
    have hposN : N ^ (2 - 2 * σ) ≤ H ^ (p + 2 * η) := by
      refine (Real.rpow_le_rpow hN0.le hupper (by linarith)).trans ((Real.rpow_mul hHpos.le _ _).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hH1 ?_))
      have hp_eq : (3 * a / 2) * (2 - 2 * σ) = p := by dsimp [a, p]; field_simp [show 2 - σ ≠ 0 by linarith]
      nlinarith [hp_eq]
    have hmean1 : H * N ^ (1 - 2 * σ) ≤ H ^ p := by
      have hp_eq : 1 + a * (1 - 2 * σ) = p := by dsimp [a, p]; field_simp [show 2 - σ ≠ 0 by linarith]; ring
      calc
        H * N ^ (1 - 2 * σ) ≤ H ^ (1 : ℝ) * (H ^ a) ^ (1 - 2 * σ) := by
          rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)) hHpos.le
        _ = H ^ (1 + a * (1 - 2 * σ)) := by rw [← Real.rpow_mul hHpos.le, ← Real.rpow_add hHpos]
        _ = H ^ p := by rw [hp_eq]
    have hlogN : Real.log (2 * N) ≤ Dlog * H ^ (2 * η) :=
      (classical_log_budget (by linarith : 1 ≤ N) hη).trans (mul_le_mul_of_nonneg_left hsmallN hDlog.le)
    have hmean2 : N ^ (2 - 2 * σ) * Real.log (2 * N) ≤ Dlog * H ^ (p + 4 * η) := by
      calc
        _ ≤ H ^ (p + 2 * η) * (Dlog * H ^ (2 * η)) := mul_le_mul hposN hlogN (Real.log_nonneg (by linarith)) (by positivity)
        _ = Dlog * H ^ (p + 4 * η) := by rw [mul_left_comm, ← Real.rpow_add hHpos]; congr 2; ring
    have hmean1' : H * N ^ (1 - 2 * σ) ≤ H ^ (p + 4 * η) := hmean1.trans (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
    have hsumM : H * N ^ (1 - 2 * σ) + N ^ (2 - 2 * σ) * Real.log (2 * N) ≤ (1 + Dlog) * H ^ (p + 4 * η) := by nlinarith
    refine hcW.trans ?_
    calc
      102 * ((H * N ^ (1 - 2 * σ) + N ^ (2 - 2 * σ) * Real.log (2 * N)) * H ^ (4 * η))
        ≤ 102 * (((1 + Dlog) * H ^ (p + 4 * η)) * H ^ (4 * η)) := by gcongr
      _ = CLV * H ^ (p + 8 * η) := by dsimp [CLV]; rw [mul_assoc _ (H ^ _), ← Real.rpow_add hHpos]; ring_nf
      _ ≤ CLV * H ^ (p + 10 * η) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by dsimp [CLV]; positivity)
  have hJcard : (J.card : ℝ) ≤ H ^ η := by
    have hfCard : ((fixedShortDetectorIndices H).card : ℝ) ≤ 60 * (Real.log H) ^ 2 := fixedShortDetectorIndices_card_le (by linarith) hDlog5 hJlog12
    have hidxCard : (idxSet.card : ℝ) ≤ 60 * (M : ℝ) ^ 2 * (Real.log H) ^ 2 := by
      dsimp [idxSet]; simp only [Finset.card_product, Nat.card_Icc, Finset.card_range, Nat.add_sub_cancel]
      push_cast; nlinarith
    have hsmallC : 60 * (M : ℝ) ^ 2 * (Real.log H) ^ 2 ≤ H ^ η := by
      have hh := (div_lt_iff₀ (by positivity : 0 < H ^ η)).mp hcardLog
      have hm := mul_le_mul_of_nonneg_left hh.le (show 0 ≤ 60 * (M : ℝ) ^ 2 by positivity)
      have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact hm.trans_eq (by field_simp [hMne])
    exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans (hidxCard.trans hsmallC)
  have hsumW : (W.card : ℝ) ≤ (J.card : ℝ) * (CLV * H ^ (p + 10 * η)) := by
    calc
      (W.card : ℝ) ≤ ∑ q ∈ J, ((Wj q).card : ℝ) := by exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ J, CLV * H ^ (p + 10 * η) := Finset.sum_le_sum hWj
      _ = _ := by simp
  rw [← hcard]
  calc
    (W.card : ℝ) ≤ H ^ η * (CLV * H ^ (p + 10 * η)) := hsumW.trans (mul_le_mul_of_nonneg_right hJcard (by dsimp [CLV]; positivity))
    _ = CLV * H ^ (p + 11 * η) := by rw [← mul_left_comm, ← Real.rpow_add hHpos]; congr 2; ring
    _ ≤ CLV * H ^ (p + 12 * η) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by dsimp [CLV]; positivity)

/-- Actual Ingham estimate on `[1/2, 9/13]` for global `riemannZeta` zeros with multiplicity. -/
theorem ingham_lower_density : InghamLowerDensity := by
  classical
  intro σ hσLower hσUpper ε hε
  rcases hσLower.eq_or_lt with rfl | hInterior
  · exact ingham_at_half hε
  · let M : ℕ := max 100 (⌈8 / ε⌉₊ + 1)
    have hM1 : 1 ≤ M := by dsimp [M]; omega
    have hM_eps : 2 / (M : ℝ) ≤ ε / 4 := by
      have hgt : 8 / ε < (M : ℝ) := by
        have : ⌈8 / ε⌉₊ + 1 ≤ M := le_max_right _ _
        have h1 : 8 / ε ≤ (⌈8 / ε⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈8 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast this
        push_cast at h2; linarith
      rw [div_le_iff₀ (by positivity)]
      have := (div_lt_iff₀ hε).mp hgt
      linarith
    let η : ℝ := min (ε / 24) (1 / 100)
    have hη : 0 < η := lt_min (by positivity) (by norm_num)
    have hηs : η ≤ 1 / 100 := min_le_right _ _
    have hηe : 12 * η ≤ ε / 2 := by have := min_le_left (ε / 24) (1 / 100); linarith
    obtain ⟨CI, hCI, hI⟩ := ingham_typeI_slab_count hInterior hσUpper hM1 hη hηs
    obtain ⟨CII, hCII, hII⟩ := ingham_typeII_slab_count hInterior hσUpper hM1 (show 0 < ε / 4 by positivity)
    obtain ⟨C₀, hC₀, hrep⟩ := half_separated_representatives
    let p : ℝ := 3 * (1 - σ) / (2 - σ)
    let D : ℝ := Real.log 2 + 1 / (ε / 2)
    have hD : 0 < D := add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr (by positivity))
    have hpII : 2 - 2 * σ ≤ p := by
      dsimp [p]; rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (show 0 ≤ 1 - σ by linarith) (show 0 ≤ 2 * σ - 1 by linarith)]
    have hslab : ∀ᶠ H : ℝ in atTop, (zetaSlabCount σ H (2 * H) : ℝ) ≤ (C₀ * (CI + CII) * D) * H ^ (p + ε) := by
      filter_upwards [eventually_ge_atTop (2 : ℝ), ingham_alternative hInterior hM1, hI, hII]
        with H hH halt hi hii
      have hH1 : 1 ≤ H := by linarith
      have hH0 : 0 < H := by linarith
      obtain ⟨R, hR, hcard, hsep, hcount⟩ := hrep σ H hσLower hH
      let P := fun ρ : ℂ => (1/3 : ℝ) ≤ ‖inghamFiniteDetector M ρ H‖
      let RI := R.filter P
      let RII := R.filter fun ρ => ¬ P ρ
      have hinj : Set.InjOn Complex.im (R : Set ℂ) := Finset.injOn_of_card_image_eq hcard
      have hbI : (RI.card : ℝ) ≤ CI * H ^ (p + ε / 2) :=
        (hi RI ((Finset.filter_subset _ _).trans hR) (Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)))
          (oneSeparated_subset hsep (Finset.image_subset_image (Finset.filter_subset _ _))) fun ρ hρ => (Finset.mem_filter.mp hρ).2).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) hCI.le)
      have hbII : (RII.card : ℝ) ≤ CII * H ^ (p + ε / 2) := by
        refine (hii RII ((Finset.filter_subset _ _).trans hR) (Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)))
          (oneSeparated_subset hsep (Finset.image_subset_image (Finset.filter_subset _ _))) fun ρ hρ => ?_).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) hCII.le)
        obtain ⟨hz, hβ, hγ, hγ'⟩ := mem_zetaZeroFinset.mp (hR ((Finset.filter_subset _ _) hρ))
        have habs : |ρ.im| = ρ.im := abs_of_nonneg (by linarith)
        rcases halt ρ hβ hz.2.2 (by rwa [habs]) (by rwa [habs]) hz.1 with h1 | h2
        · exact ((Finset.mem_filter.mp hρ).2 h1).elim
        · exact h2
      have hRcard : (R.card : ℝ) ≤ (CI + CII) * H ^ (p + ε / 2) := by
        have hc : (RI.card : ℝ) + (RII.card : ℝ) = R.card := by exact_mod_cast Finset.card_filter_add_card_filter_not P
        nlinarith
      have hlog : Real.log (2 * H) ≤ D * H ^ (ε / 2) := classical_log_budget hH1 (by positivity)
      calc
        (zetaSlabCount σ H (2 * H) : ℝ) ≤ C₀ * Real.log (2 * H) * ((CI + CII) * H ^ (p + ε / 2)) :=
          hcount.trans (mul_le_mul_of_nonneg_left hRcard (mul_nonneg hC₀.le (Real.log_nonneg (by linarith))))
        _ ≤ C₀ * (D * H ^ (ε / 2)) * ((CI + CII) * H ^ (p + ε / 2)) := by gcongr
        _ = (C₀ * (CI + CII) * D) * (H ^ (ε / 2) * H ^ (p + ε / 2)) := by ring
        _ = (C₀ * (CI + CII) * D) * H ^ (p + ε) := by rw [← Real.rpow_add hH0]; congr 2; ring
    have hp_pos : 0 < p + ε := add_pos_of_nonneg_of_pos (div_nonneg (by linarith) (by linarith)) hε
    exact zetaDensity_bound_of_eventual_slabs hp_pos (by positivity) hslab

end GuthMaynard.Improvement

