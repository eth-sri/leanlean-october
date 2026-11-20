module
public import GuthMaynard.Improvement.ShortDetectorLocalMass

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- A rescaled version of the audited integrable exponential majorant. -/
theorem short_scaled_majorant_integrable :
    Integrable (fun t : ℝ => detectorGammaMajorant (t/2)) := by
  simpa only [div_eq_mul_inv,mul_comm] using
    integrable_detectorGammaMajorant.comp_mul_left' (by norm_num : (2:ℝ)⁻¹ ≠ 0)

/-- Quantitative tail domination, retaining an integrable common envelope. -/
theorem short_exponential_tail_domination {R t : ℝ} (ht : R ≤ |t|) :
    (1+|t|)^2*Real.exp (-|t|) ≤ detectorGammaMajorant (t/2)*Real.exp (-R/2) := by
  have hab : |t/2| = |t|/2 := by rw [abs_div]; norm_num
  have hp : (1+|t|)^2 ≤ 48*(1+|t|/2)^2 := by nlinarith [abs_nonneg t,sq_nonneg |t|]
  have he : Real.exp (-|t|/2) ≤ Real.exp (-R/2) := Real.exp_le_exp.mpr (by linarith)
  have heq : Real.exp (-|t|) = Real.exp (-|t|/2)*Real.exp (-|t|/2) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold detectorGammaMajorant
  rw [hab,heq]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-|t|/2)).le) he
    (Real.exp_pos (-|t|/2)).le (by positivity)
  simpa only [neg_div,mul_assoc] using hh

/-- Uniform coarse kernel bound down to9/13; independent Y≥1 only improves it. -/
theorem short_detector_kernel_coarse {s : ℝ} (hs : 1/2 < s) {ρ : ℂ} {Y : ℝ} (hY : 1 ≤ Y)
    (hβ : s ≤ ρ.re) (hβ' : ρ.re ≤ 1) (X t : ℝ) :
    ‖detectorKernel ρ X Y (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
      (4*(12/(s-1/2)))*(⌊X⌋₊:ℝ)*(1+|ρ.im|)*(1+|t|)^2*Real.exp (-|t|) := by
  have hYpos : 0 < Y := by linarith
  rw [short_detector_kernel_norm hYpos]
  have ha : 0 < ρ.re-1/2 := by linarith
  have hg := norm_Gamma_negative_strip ha (show ρ.re-1/2 ≤ 1/2 by linarith) t
  rw [show -(ρ.re-1/2)=1/2-ρ.re by ring] at hg
  have hc : 12/(ρ.re-1/2) ≤ 12/(s-1/2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hg' : ‖Complex.Gamma (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
      (12/(s-1/2))*(1+|t|)*Real.exp (-|t|) := hg.trans (by gcongr)
  have hshift : mollifiedNorm X (ρ.im+t) ≤
      4*(⌊X⌋₊:ℝ)*(1+|ρ.im|)*(1+|t|) := by
    apply (mollifiedNorm_bound X (ρ.im+t)).trans
    have hh : 1+|ρ.im+t| ≤ (1+|ρ.im|)*(1+|t|) := by
      nlinarith [abs_add_le ρ.im t,mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    convert mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*(⌊X⌋₊:ℝ) by positivity) using 1; ring
  have hy : Y^(1/2-ρ.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY (by linarith)
  calc
    _ ≤ 1*((12/(s-1/2))*(1+|t|)*Real.exp (-|t|))*(4*(⌊X⌋₊:ℝ)*(1+|ρ.im|)*(1+|t|)) := by
      apply mul_le_mul (mul_le_mul hy hg' (norm_nonneg _) (by norm_num)) hshift (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Actual critical-ordinate tail with a uniform exponential rate. -/
theorem short_detector_ordinate_tail {s : ℝ} (hs : 1/2 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y R : ℝ, ∀ ρ : ℂ,
      1 ≤ Y → s ≤ ρ.re → ρ.re ≤ 1 →
      (∫ t in {t : ℝ | R < |t|},
        ‖detectorKernel ρ X Y (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖) ≤
        C*(⌊X⌋₊:ℝ)*(1+|ρ.im|)*Real.exp (-R/2) := by
  let J := ∫ t : ℝ, detectorGammaMajorant (t/2)
  have hJ : 0 ≤ J := integral_nonneg (fun t => by unfold detectorGammaMajorant; positivity)
  have hsp : 0 < s-1/2 := by linarith
  refine ⟨(4*(12/(s-1/2)))*(J+1),by positivity,?_⟩
  intro X Y R ρ hY hβ hβ'
  let B := (4*(12/(s-1/2)))*(⌊X⌋₊:ℝ)*(1+|ρ.im|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := (integrable_detectorKernel_left (u:=1/2) (X := X)
    (show 0 < Y by linarith) (by linarith) hβ').norm
  have hm := (short_scaled_majorant_integrable.const_mul (B*Real.exp (-R/2)))
  calc
    _ ≤ ∫ t in {t : ℝ | R < |t|}, (B*Real.exp (-R/2))*detectorGammaMajorant (t/2) := by
      apply setIntegral_mono_on hi.integrableOn hm.integrableOn (by measurability)
      intro t ht
      have hh := mul_le_mul_of_nonneg_left (short_exponential_tail_domination ht.le) hB
      apply (short_detector_kernel_coarse hs hY hβ hβ' X t).trans
      convert hh using 1 <;> dsimp [B] <;> ring
    _ ≤ ∫ t : ℝ, (B*Real.exp (-R/2))*detectorGammaMajorant (t/2) :=
      setIntegral_le_integral hm (Filter.Eventually.of_forall (fun t => by unfold detectorGammaMajorant; positivity))
    _ = (B*Real.exp (-R/2))*J := integral_const_mul _ _
    _ ≤ _ := by
      have hh : 0 ≤ (⌊X⌋₊:ℝ)*(1+|ρ.im|)*Real.exp (-R/2) := by positivity
      dsimp [B]
      nlinarith only [mul_nonneg (show 0 ≤ 12/(s-1/2) by positivity) hh]

/-- A single height threshold controls the actual discarded ordinate integral
for every beta and every ordinate in the slab, independently of a zero set. -/
theorem short_detector_ordinate_tail_eventually_small {s δ : ℝ} (hs : 1/2 < s) (hδ : 0 < δ) :
    ∀ᶠ H : ℝ in atTop, ∀ X Y : ℝ, 0 ≤ X → X ≤ 2*H → 1 ≤ Y → ∀ ρ : ℂ,
      s ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ 2*H →
      (∫ t in {t : ℝ | H/2 < |t|},
        ‖detectorKernel ρ X Y
          (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖) < δ := by
  obtain ⟨C,hC,hbound⟩ := short_detector_ordinate_tail hs
  have hlim : Tendsto (fun H : ℝ => 6*C*H^2*Real.exp (-H/4)) atTop (𝓝 0) := by
    have hd : Tendsto (fun H : ℝ => H/4) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
    have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hd).const_mul (96*C)
    convert hh using 1
    · funext H
      dsimp only [Function.comp_def]
      rw [neg_div]
      ring
    · simp
  have hs := hlim.eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop (1:ℝ),hs] with H hH hsmall
  intro X Y hx0 hxH hy ρ hβ hβ' hγ
  have hn : 0 < H := by linarith
  have hx := (Nat.floor_le hx0).trans hxH
  have hh := hbound X Y (H/2) ρ hy hβ hβ'
  have he : -(H/2)/2 = -H/4 := by ring
  rw [he] at hh
  apply (hh.trans _).trans_lt hsmall
  calc
    _ ≤ C*(2*H)*(3*H)*Real.exp (-H/4) := by gcongr; linarith
    _ = _ := by ring

end GuthMaynard.Improvement
