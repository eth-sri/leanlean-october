module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.GoodKernelBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowXiControls

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawGoodNestedControls31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
  DedekindZetaZeroFree.Quantitative.RawLowXiControls31
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

def goodNbhd (u : Frequency D.recipe) : Set ℂ :=
  {ξ : ℂ | Scales.goodLine - EulerDomain.pad / 2 < ξ.re ∧ ξ.re < Scales.rightLine + EulerDomain.pad / 2 ∧
    (pkg D).minus u ξ ≠ 0}

theorem goodNbhd_isOpen (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    IsOpen (goodNbhd D u) := by
  have hxg : (0 : ℝ) < Scales.goodLine - EulerDomain.pad / 2 := by
    unfold Scales.goodLine EulerDomain.pad; norm_num
  rw [isOpen_iff_mem_nhds]
  intro ξ hξ
  obtain ⟨h1, h2, h3⟩ := hξ
  have hcont : ContinuousAt ((pkg D).minus u) ξ :=
    (DedekindZetaZeroFree.Quantitative.RawKernelRegularity31.minus_differentiableAt D u hu ξ
      (by linarith)).continuousAt
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1,
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds h2,
    hcont.eventually_ne h3] with z hz₁ hz₂ hz₃
  exact ⟨hz₁, hz₂, hz₃⟩

private theorem z₀_pos : (0 : ℝ) < Scales.zLine := by unfold Scales.zLine; norm_num

private theorem x_g_le_x₁ : Scales.goodLine ≤ Scales.rightLine := by
  rw [Scales.rightLine_eq]; unfold Scales.goodLine; norm_num

private theorem pad_nn : (0 : ℝ) ≤ EulerDomain.pad := by unfold EulerDomain.pad; norm_num

private theorem freqNorm_pos (u : Frequency D.recipe) : 0 < frequencyNorm D.recipe u := by
  rw [← FixedData.rawFrequency_norm D u]
  exact_mod_cast D.recipe.A.exteriorNorm_pos _

private theorem zpow_bound (Z : ℝ) (hZ : 0 < Z) (c x x₀ : ℝ) (hx : |x - x₀| ≤ 1) :
    Z ^ (c + x) ≤ Real.exp (|Real.log Z| * (|c| + |x₀| + 1)) := by
  rw [Real.rpow_def_of_pos hZ]
  apply Real.exp_le_exp.2
  calc Real.log Z * (c + x) ≤ |Real.log Z * (c + x)| := le_abs_self _
    _ = |Real.log Z| * |c + x| := abs_mul _ _
    _ ≤ |Real.log Z| * (|c| + |x₀| + 1) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h1 := abs_add_le c x
        have h2 := abs_sub_abs_le_abs_sub x x₀
        linarith

private theorem final_ineq (C Cw P Q T x : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hT : 0 ≤ T) (hx : x ≤ Cw * (C * P * Q) * T) : x ≤ (C * Cw + 1) * P * Q * T := by
  have h0 : 0 ≤ P * Q * T := by positivity
  nlinarith

private theorem weight_dom (ξ : ℂ) (v y Cc A : ℝ) (hCc : 0 ≤ Cc) (hA : 0 ≤ A) (p : ℝ × ℝ) :
    Cc * (WeightConvolution.weightModulus D ξ v y p * (2 + |p.2|) ^ A) ≤
      Cc * WeightConvolution.weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ A := by
  rw [← mul_assoc]
  unfold WeightConvolution.weightModulus
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hA) (by positivity)
  linarith [abs_nonneg p.1, abs_nonneg ξ.im]

private theorem exists_Cw (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 0 < Z → ∀ ξ : ℂ, Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine →
      (pkg D).minus u ξ ≠ 0 → ∀ Cf : ℝ, 0 ≤ Cf →
      (∀ p : ℝ × ℝ, ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * I) Z‖ ≤
        Cf * (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A)) →
      ‖Iwz D u ξ Scales.wLine Scales.zLine Z‖ ≤
        Cw * Cf * (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨Cw, hCw, h⟩ := Iwz_bound_of_majorant D Scales.goodLine Scales.rightLine B A x_g_le_x₁ hB hA
  refine ⟨Cw, hCw, fun u hu Z hZ ξ hxg hx1 hne Cf hCf hb => ?_⟩
  exact h u hu Z hZ ξ hxg hx1 (by linarith [pad_nn]) hne Cf hCf
    (fun p => (hb p).trans (weight_dom D ξ Scales.zLine Scales.wLine Cf A hCf hA p))

private theorem plus_line_bound (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ w : ℂ, w.re = Scales.wLine →
      ‖(pkg D).plus u w‖ ≤ C * (2 + |w.im|) ^ A := by
  have hq0 := freqNorm_pos D u
  obtain ⟨Ap, Cp, hAp, hCp, hP⟩ := RawPrimitiveGrowth31.primPlus_fixed_strip D u hu
  obtain ⟨gp, hgp, hgpeq⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A
    (FixedData.primPlus D u) ((pkg D).nonprincipal u hu).1
  obtain ⟨Cm, hCm, hmask⟩ := RawDeletionMask31.plus_mask_subpower D Scales.wLine 1
    (by unfold Scales.wLine; norm_num) one_pos
  refine ⟨Cp * (Cm * frequencyNorm D.recipe u ^ (1 : ℝ)), Ap, by positivity, hAp, fun w hw => ?_⟩
  have hw0 : 0 < w.re := by rw [hw]; unfold Scales.wLine; norm_num
  rw [RawHeckeIdentification31.plus_eq_hecke_mul_mask D u hu w hw0, norm_mul, ← hgpeq w hw0]
  have h1 : ‖gp w‖ ≤ Cp * (2 + |w.im|) ^ Ap :=
    hP gp hgp (fun s hs => (hgpeq s (by linarith)).trans
      (RowHeckeBridge.hecke_eq_idealLSeries _ _ _ s hs)) w
      (by rw [hw]; unfold Scales.wLine; norm_num)
  have h2 := (hmask u w hw.ge).2.1
  refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring))

private theorem local_majorant (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ₀ : ℂ) (h₀ : ξ₀ ∈ goodNbhd D u) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ goodNbhd D u ∧ ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * I) Z‖ ≤
          C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
  have hq0 := freqNorm_pos D u
  have hxg0 : (0 : ℝ) < Scales.goodLine - EulerDomain.pad / 2 := by
    unfold Scales.goodLine EulerDomain.pad; norm_num
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.1 (goodNbhd_isOpen D u hu) ξ₀ h₀
  obtain ⟨hξ1, hξ2, hξ3⟩ := h₀
  have hc : ContinuousAt ((pkg D).minus u) ξ₀ :=
    (DedekindZetaZeroFree.Quantitative.RawKernelRegularity31.minus_differentiableAt D u hu ξ₀
      (by linarith)).continuousAt
  have hnorm : 0 < ‖(pkg D).minus u ξ₀‖ := norm_pos_iff.2 hξ3
  obtain ⟨r1, hr1, hball1⟩ : ∃ r1 : ℝ, 0 < r1 ∧ ∀ ξ : ℂ, dist ξ ξ₀ < r1 →
      ‖(pkg D).minus u ξ₀‖ / 2 < ‖(pkg D).minus u ξ‖ := by
    have := hc.norm.eventually
      (lt_mem_nhds (show ‖(pkg D).minus u ξ₀‖ / 2 < ‖(pkg D).minus u ξ₀‖ by linarith))
    obtain ⟨e, he, h⟩ := Metric.eventually_nhds_iff.1 this
    exact ⟨e, he, fun ξ hξ => h hξ⟩
  obtain ⟨C1, hC1, h1⟩ := RawRightHecke31.recipe_L_right D (2 / 5) (by norm_num)
  obtain ⟨Cp, Ap, hCp, hAp, hplus⟩ := plus_line_bound D u hu
  obtain ⟨C3, hC3, h3⟩ := RawEulerProduct31.correctionProduct_subpower_paddedBoxes D 1 one_pos
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = Scales.kernelExponent 0 Scales.wLine Scales.zLine := ⟨_, rfl⟩
  obtain ⟨Zbd, hZbd⟩ : ∃ Zbd : ℝ,
      Zbd = Real.exp (|Real.log Z| * (|c0| + |ξ₀.re| + 1)) := ⟨_, rfl⟩
  obtain ⟨Cinv, hCinv⟩ : ∃ Cinv : ℝ, Cinv = (‖(pkg D).minus u ξ₀‖ / 2)⁻¹ := ⟨_, rfl⟩
  have hCinv0 : 0 < Cinv := by rw [hCinv]; exact inv_pos.2 (by linarith)
  have hZbd0 : 0 < Zbd := by rw [hZbd]; exact Real.exp_pos _
  have hrr0 : min (min r0 r1) 1 ≤ r0 := (min_le_left _ _).trans (min_le_left _ _)
  have hrr1 : min (min r0 r1) 1 ≤ r1 := (min_le_left _ _).trans (min_le_right _ _)
  have hrr2 : min (min r0 r1) 1 ≤ 1 := min_le_right _ _
  refine ⟨min (min r0 r1) 1, lt_min (lt_min hr0 hr1) one_pos,
    fun ξ hξ => hball0 (Metric.ball_subset_ball hrr0 hξ),
    Zbd * frequencyNorm D.recipe u ^ (-Scales.zLine) *
      (C1 * Cp * (C3 * frequencyNorm D.recipe u ^ (1 : ℝ)) * Cinv), Ap, by positivity, hAp, ?_⟩
  intro ξ hξ p
  have hd : dist ξ ξ₀ < min (min r0 r1) 1 := hξ
  have hd1 : dist ξ ξ₀ < r1 := hd.trans_le hrr1
  have hd2 : dist ξ ξ₀ < 1 := hd.trans_le hrr2
  have hξG : ξ ∈ goodNbhd D u := hball0 (Metric.ball_subset_ball hrr0 hξ)
  have hxg : Scales.goodLine - EulerDomain.pad ≤ ξ.re := by
    have := hξG.1
    linarith [pad_nn]
  have hre : |ξ.re - ξ₀.re| ≤ dist ξ ξ₀ := by
    rw [dist_eq_norm]
    have := Complex.abs_re_le_norm (ξ - ξ₀)
    rwa [Complex.sub_re] at this
  have hLξ : ‖((pkg D).minus u ξ)⁻¹‖ ≤ Cinv := by
    rw [norm_inv, hCinv]
    exact inv_anti₀ (by linarith) (hball1 ξ hd1).le
  have hRb : ∀ w z : ℂ, w.re = Scales.wLine → z.re = Scales.zLine →
      ‖rawFactor D u ξ w z‖ ≤
        C1 * (Cp * (2 + |w.im|) ^ Ap) * (C3 * frequencyNorm D.recipe u ^ (1 : ℝ)) * Cinv := by
    intro w z hw hz
    have hz1 : ‖D.recipe.L (6 * z)‖ ≤ C1 :=
      (h1 z (by rw [hz]; unfold Scales.zLine; norm_num)).2.1
    have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.paddedBoxes := by
      refine Or.inl (Or.inl ?_)
      refine ⟨hxg, ?_, ?_⟩
      · show 3 / 25 - EulerDomain.pad ≤ w.re
        rw [hw]; unfold Scales.wLine EulerDomain.pad; norm_num
      · show 2 / 5 - EulerDomain.pad ≤ z.re
        rw [hz]; unfold Scales.zLine EulerDomain.pad; norm_num
    have hcorr : ‖AllRowEuler.InitialSeparation.correctionProduct D.context
        (FixedData.rawFrequency D u) ξ w z‖ ≤ C3 * frequencyNorm D.recipe u ^ (1 : ℝ) := by
      have := (h3 (FixedData.rawFrequency D u) _ hmem).2
      rw [FixedData.rawFrequency_norm D u] at this
      exact this
    have e : ‖rawFactor D u ξ w z‖ = ‖D.recipe.L (6 * z)‖ * ‖(pkg D).plus u w‖ *
        ‖AllRowEuler.InitialSeparation.correctionProduct D.context
          (FixedData.rawFrequency D u) ξ w z‖ * ‖((pkg D).minus u ξ)⁻¹‖ := by
      unfold FixedData.rawFactor
      simp only [div_eq_mul_inv, norm_mul]
    have hpl := hplus w hw
    have hA : 0 ≤ C1 * (Cp * (2 + |w.im|) ^ Ap) := by positivity
    have hB : 0 ≤ C1 * (Cp * (2 + |w.im|) ^ Ap) * (C3 * frequencyNorm D.recipe u ^ (1 : ℝ)) := by
      positivity
    rw [e]
    exact mul_le_mul (mul_le_mul (mul_le_mul hz1 hpl (norm_nonneg _) hC1.le) hcorr
      (norm_nonneg _) hA) hLξ (norm_nonneg _) hB
  have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * I).re = Scales.wLine := by simp
  have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * I).re = Scales.zLine := by simp
  have him : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * I).im = p.2 := by simp
  have hRb' := hRb _ _ hw hz
  rw [him] at hRb'
  have hZe : Z ^ (Scales.kernelExponent ξ.re Scales.wLine Scales.zLine) ≤ Zbd := by
    have : Scales.kernelExponent ξ.re Scales.wLine Scales.zLine = c0 + ξ.re := by
      rw [hc0]; unfold Scales.kernelExponent; ring
    rw [this, hZbd]
    exact zpow_bound Z hZ c0 ξ.re ξ₀.re (hre.trans hd2.le)
  have hKn := RawKernelNorm.norm_rawKernel D u ξ Scales.zLine Scales.wLine p Z hZ
  rw [hKn]
  have hWn : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := by
    unfold WeightConvolution.weightModulus; exact norm_nonneg _
  have hpoly : (2 + |p.2|) ^ Ap ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ Ap :=
    Real.rpow_le_rpow (by positivity)
      (by linarith [abs_nonneg p.1, abs_nonneg ξ.im]) hAp
  have hqz0 : 0 ≤ frequencyNorm D.recipe u ^ (-Scales.zLine) := Real.rpow_nonneg hq0.le _
  calc Z ^ (Scales.kernelExponent ξ.re Scales.wLine Scales.zLine) * frequencyNorm D.recipe u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        ‖rawFactor D u ξ (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * I)
          (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * I)‖
      ≤ Zbd * frequencyNorm D.recipe u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        (C1 * (Cp * (2 + |p.2|) ^ Ap) * (C3 * frequencyNorm D.recipe u ^ (1 : ℝ)) * Cinv) := by
        apply mul_le_mul _ hRb' (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZe hqz0) hWn
    _ = (Zbd * frequencyNorm D.recipe u ^ (-Scales.zLine) *
          (C1 * Cp * (C3 * frequencyNorm D.recipe u ^ (1 : ℝ)) * Cinv)) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ Ap := by
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hpoly
        positivity

theorem Iwz_differentiableOn_goodNbhd (A : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ (fun ξ : ℂ => Iwz D u ξ Scales.wLine Scales.zLine Z) (goodNbhd D u) := by
  have hxgle : ∀ ξ ∈ goodNbhd D u, Scales.goodLine - EulerDomain.pad ≤ ξ.re := by
    intro ξ hξ
    have := hξ.1
    linarith [pad_nn]
  exact RowKernelHolomorphy.differentiableOn_nested_integral D (goodNbhd D u)
    (goodNbhd_isOpen D u hu) (fun ξ w z => rawKernel D u ξ w z Z) Scales.wLine Scales.zLine z₀_pos
    (fun ξ hξ => rawKernel_diffAt_xi D u hu Z hZ ξ (hxgle ξ hξ) hξ.2.2)
    (fun ξ hξ => rawKernel_continuous_heights D u hu Z hZ ξ (hxgle ξ hξ) hξ.2.2)
    (local_majorant D u hu Z hZ)

theorem Iwz_decay_rect (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ (ξ : ℂ) (Z : ℝ), 0 < Z → Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine → |ξ.im| ≤ 2 * U ^ ρ →
        ‖Iwz D u ξ Scales.wLine Scales.zLine Z‖ ≤
          C * Z ^ (Scales.kernelExponent ξ.re Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
            (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨C, hC, U₀, hU₀, h⟩ :=
    RawGoodKernelBounds31.rawKernel_majorant_rect D A ρ hA hconv hρ ε hε
  obtain ⟨Cw, hCw0, hCw⟩ := exists_Cw D A B hA hB
  refine ⟨C * Cw + 1, by positivity, U₀, hU₀, ?_⟩
  intro U hU u hu hqU hqU2 hex ξ Z hZ hxg hx1 him
  have hU0 : 0 < U := by linarith
  have hnn : 0 ≤ U ^ ρ := Real.rpow_nonneg hU0.le ρ
  have hne : (pkg D).minus u ξ ≠ 0 :=
    (DedekindZetaZeroFree.Quantitative.RawKernelRegularity31.minus_ne_zero_of_not_exceptional D ρ U u hu hqU hqU2
      hex ξ (by unfold DedekindZetaZeroFree.Quantitative.DetectorDef.σ₀; unfold Scales.goodLine at hxg; linarith)
      (by unfold Scales.goodLine at hxg; linarith)
      (by linarith [abs_nonneg ξ.im])).2
  have hle := hCw u hu Z hZ ξ hxg hx1 hne
    (C * Z ^ (Scales.kernelExponent ξ.re Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε)) (by positivity)
    (fun p => h U hU u hu hqU hqU2 hex ξ Z p hZ hxg hx1 him)
  exact final_ineq _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) hle

theorem Iwz_decay_right (A : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U →
      ∀ (ξ : ℂ) (Z : ℝ), 0 < Z → ξ.re = Scales.rightLine →
        ‖Iwz D u ξ Scales.wLine Scales.zLine Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
            (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨C, hC, h⟩ := RawGoodKernelBounds31.rawKernel_majorant_right D A hA hconv ε hε
  obtain ⟨C4, hC4, h4⟩ := RawReciprocal31.raw_reciprocal_right D
  obtain ⟨Cw, hCw0, hCw⟩ := exists_Cw D A B hA hB
  refine ⟨C * Cw + 1, by positivity, ?_⟩
  intro U hU2 u hu hqU hqU2 ξ Z hZ hξ
  have hU0 : 0 < U := by linarith
  have hxg : Scales.goodLine ≤ ξ.re := by
    rw [hξ, Scales.rightLine_eq]; unfold Scales.goodLine; norm_num
  have hne := (h4 u hu ξ hξ.ge).1
  have hle := hCw u hu Z hZ ξ hxg hξ.le hne
    (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε)) (by positivity)
    (fun p => h U hU2 u hu hqU hqU2 ξ Z p hZ hξ)
  exact final_ineq _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) hle

theorem Iwz_integrable_right (A : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A) :
    ∀ U : ℝ, 2 ≤ U → ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
      U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
      ∀ Z : ℝ, 0 < Z → Integrable (fun t : ℝ =>
        Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z) := by
  intro U hU u hu hqU hqU2 Z hZ
  obtain ⟨C, hC, h⟩ := Iwz_decay_right D A hA hconv 1 one_pos 2 two_pos
  obtain ⟨C4, hC4, h4⟩ := RawReciprocal31.raw_reciprocal_right D
  have hdiff := Iwz_differentiableOn_goodNbhd D A hA hconv u hu Z hZ
  have hmem : ∀ t : ℝ, ((Scales.rightLine : ℂ) + (t : ℂ) * I) ∈ goodNbhd D u := by
    intro t
    have hre : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * I).re = Scales.rightLine := by simp
    refine ⟨?_, ?_, (h4 u hu _ hre.ge).1⟩
    · rw [hre, Scales.rightLine_eq]; unfold Scales.goodLine EulerDomain.pad; norm_num
    · rw [hre]
      have : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
      linarith
  have hcont : Continuous (fun t : ℝ =>
      Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z) :=
    hdiff.continuousOn.comp_continuous
      (f := fun t : ℝ => (Scales.rightLine : ℂ) + (t : ℂ) * I) (by fun_prop) hmem
  have hI : Integrable (fun t : ℝ => (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
      U ^ ((1 / 25 : ℝ) + 1)) * (1 + |t|) ^ (-(2 : ℝ))) :=
    (KernelWeightIntegration.one_add_abs_rpow_integrable 2 (by norm_num)).const_mul _
  refine Integrable.mono' hI hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hre : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * I).re = Scales.rightLine := by simp
  have him : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
  have := h U hU u hu hqU hqU2 _ Z hZ hre
  rw [him] at this
  exact this

end

end DedekindZetaZeroFree.Quantitative.RawGoodNestedControls31
