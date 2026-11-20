/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.AngleMeasure
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import BergmanWeakType.Weighted.NormalizerRadial

/-! # Flux of a potential normalized by the circular boundary solution -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType.Weighted

/-- A smooth approximation to `min x c`. -/
private def smoothCap (ε c x : ℝ) : ℝ :=
  (x + c - Real.sqrt ((x - c) ^ 2 + ε)) / 2

/-- The derivative of the smooth truncation with respect to its input. -/
private def smoothCapInputDeriv (ε c x : ℝ) : ℝ :=
  (1 - (x - c) / Real.sqrt ((x - c) ^ 2 + ε)) / 2

private def smoothCapSecondDeriv (ε c x : ℝ) : ℝ :=
  -ε / (2 * Real.sqrt ((x - c) ^ 2 + ε) ^ 3)

@[simp] private theorem smoothCap_zero (c x : ℝ) : smoothCap 0 c x = min x c := by
  simp [smoothCap, Real.sqrt_sq_eq_abs]
  grind

private theorem smoothCap_derivs {ε c : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (smoothCap ε c) (smoothCapInputDeriv ε c x) x ∧
    HasDerivAt (smoothCapInputDeriv ε c) (smoothCapSecondDeriv ε c x) x := by
  have hp : 0 < (x - c) ^ 2 + ε := by positivity
  have dx := (hasDerivAt_id x).sub_const c
  have ds := ((dx.pow 2).add_const ε).sqrt hp.ne'
  have dq := dx.div ds (Real.sqrt_pos.mpr hp).ne'
  constructor
  · unfold smoothCap
    convert (((hasDerivAt_id x).add_const c).sub ds).div_const 2 using 1 <;>
      dsimp [smoothCapInputDeriv]
    ring
  · unfold smoothCapInputDeriv smoothCapSecondDeriv
    convert (dq.const_sub 1).div_const 2 using 1 <;> dsimp
    grind

private abbrev PolarFunction := ℝ → ℝ → ℝ

private abbrev radial (f : ℝ → ℝ) : PolarFunction := fun r _ ↦ f r

private abbrev PolarContinuous (F : PolarFunction) : Prop :=
  ContinuousOn (Function.uncurry F) (radii ×ˢ angleDomain)

def angularMean (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ := ∫ θ, F r θ ∂angleMeasure

private lemma continuousOn_angularMean {F : PolarFunction} (hF : PolarContinuous F) :
    ContinuousOn (angularMean F) (radii) :=
  continuousOn_integral_of_compact_support isCompact_Icc ae_mem_angle hF

private lemma hasDerivAt_angularMean {F Fr : PolarFunction} {r : ℝ} (hr : r ∈ openRadii)
    (hF : PolarContinuous F) (hFr : PolarContinuous Fr)
    (hd : ∀ u ∈ openRadii, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr u θ) u) :
    HasDerivAt (angularMean F) (angularMean Fr r) r := by
  have hs : openRadii ×ˢ angleDomain ⊆ radii ×ˢ angleDomain := prod_mono Ioo_subset_Ico_self Subset.rfl
  exact hasDerivAt_integral_of_compact isCompact_Icc ae_mem_angle isOpen_Ioo hr
    (hF.mono hs) (hFr.mono hs) (fun θ _ u hu ↦ hd u hu θ)

private lemma antitoneOn_unit_of_hasDerivAt_nonpos {f g : ℝ → ℝ} (hc : ContinuousOn f (radii))
    (h : ∀ r ∈ openRadii, HasDerivAt f (g r) r) (hg : ∀ r ∈ openRadii, g r ≤ 0) :
    AntitoneOn f (radii) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) hc
  · simpa only [interior_Ico] using fun r hr ↦ (h r hr).hasDerivWithinAt (s := openRadii)
  aesop

/-- The normalized radial flux uses the Wronskian of the two potentials, avoiding a
second quotient-rule derivative. -/
theorem PolarSource.antitoneOn_normalized_cap (S : PolarSource) (α c : ℝ) :
    AntitoneOn (angularMean (fun r θ ↦
      min (S.integral (polarKernel (-(α + 2) / 2)) r θ / normalizer α r) c)) (radii) := by
  let k := α + 2
  let q := -k / 2
  let J := normalizer α
  let Jr := normalizerFirst α
  let Jrr := normalizerSecond α
  let F := S.integral (polarKernel q)
  let F' d := S.integral (polarKernelD d q)
  let F'' d := S.integral (polarKernelDD d q)
  let G := fun r : ℝ ↦ (1 - r ^ 2) ^ (k - 1)
  let P := fun r : ℝ ↦ r * (1 - r ^ 2) * G r
  let Pr := fun r ↦ radialCoeff k r * G r
  have hP' (r : ℝ) (hr : r ^ 2 < 1) : HasDerivAt P (Pr r) r := by
    have hn := (sub_pos.mpr hr).ne'
    have h := hasDerivAt_id r
    have hd := (h.pow 2).const_sub 1
    convert (h.mul hd).mul (hd.rpow_const (p := k - 1) (Or.inl hn)) using 1
    · rfl
    dsimp [Pr, G, radialCoeff]
    rw [rpow_sub_one hn (k - 1)]
    field_simp
    ring
  let U := F / radial J
  let Ut := F' .angular / radial J
  let W := F' .radial * radial J - F * radial Jr
  let Ur := W / radial J ^ 2
  let V := radial P * W
  let Vr := radial Pr * W + radial P * (F'' .radial * radial J - F * radial Jrr)
  let w := fun r ↦ P r * J r ^ 2
  let v := fun r ↦ G r * J r * ((1 - r ^ 2) / r)
  have hF : PolarContinuous F := S.cont_integral (PolarSource.cont_kernel q)
  have hD (d : Axis) := S.cont_integral (A := angleDomain) (PolarSource.cont_kernelD d q)
  have hDD (d : Axis) := S.cont_integral (A := angleDomain) (PolarSource.cont_kernelDD d q)
  have lift {f : ℝ → ℝ} (h : ContinuousOn f (radii)) : PolarContinuous (radial f) :=
    h.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hJ := lift (continuousOn_normalizer α)
  have hP := lift (f := P) fun r hr ↦ (hP' r (sq_lt_one_of_mem_Ico hr)).continuousAt.continuousWithinAt
  have hPr := lift ((show ContinuousOn (radialCoeff k) radii by unfold radialCoeff; fun_prop).mul
    (continuousOn_radialRpow (k - 1)))
  have hW := ((hD .radial).mul hJ).sub (hF.mul (lift (continuousOn_normalizerFirst α)))
  have hpos {r : ℝ} (hr : r ∈ openRadii) := normalizer_pos α (Ioo_subset_Ico_self hr)
  have hn (p : ℝ × ℝ) (hp : p ∈ radii ×ˢ angleDomain) := (normalizer_pos α hp.1).ne'
  have hs {r : ℝ} (hr : r ∈ openRadii) : r ^ 2 < 1 :=
    sq_lt_one_of_mem_Ico (Ioo_subset_Ico_self hr)
  have cU : PolarContinuous U := hF.div hJ hn
  have cUr := hW.div (hJ.pow 2) (fun p hp ↦ pow_ne_zero _ (hn p hp))
  have cUt := (hD .angular).div hJ hn
  have cV := hP.mul hW
  have cVr := (hPr.mul hW).add (hP.mul (((hDD .radial).mul hJ).sub
    (hF.mul (lift (continuousOn_normalizerSecond α)))))
  have dr r (hr : r ∈ openRadii) θ : HasDerivAt (U · θ) (Ur r θ) r :=
    (S.integral_kernel_hasDerivAt .radial q (hs hr) θ).div
      (normalizer_hasDerivAt α (hs hr)) (hpos hr).ne'
  have dt r (hr : r ∈ openRadii) θ : HasDerivAt (U r) (Ut r θ) θ :=
    (S.integral_kernel_hasDerivAt .angular q (hs hr) θ).div_const (J r)
  have dv r (hr : r ∈ openRadii) θ : HasDerivAt (V · θ) (Vr r θ) r := by
    have h := hs hr
    have dF := S.integral_kernel_hasDerivAt .radial q h θ
    have dFr := S.integral_kernelD_hasDerivAt .radial q h θ
    have dJ := normalizer_hasDerivAt α h
    convert (hP' r h).mul ((dFr.mul dJ).sub (dF.mul (normalizerFirst_hasDerivAt α h))) using 1
    simp only [Vr, W, radial, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Axis.slice, Axis.coord]
    ring
  have hV0 θ : V 0 θ = 0 := by simp [V, P, radial]
  have period r : U r π = U r (-π) := by
    simp [U, F, radial, PolarSource.integral, polarKernel, polarDenominator, radialComponent]
  have period_t r : F' .angular r π = F' .angular r (-π) := by
    simp [F', PolarSource.integral, polarKernelD, polarDenominatorD, polarKernel,
      polarDenominator, radialComponent, angularComponent]
  have pos r (hr : r ∈ openRadii) : 0 < w r := by
    dsimp [w, P]
    positivity [G, hr.1, sub_pos.mpr (hs hr), hpos hr]
  have flux r (hr : r ∈ openRadii) θ : V r θ = w r * Ur r θ := by
    dsimp [V, w, Ur, radial]
    field_simp [show J r ≠ 0 from (hpos hr).ne']
  have div_nonpos r (hr : r ∈ openRadii) θ : Vr r θ + v r * F'' .angular r θ ≤ 0 := by
    calc
      _ = G r * J r * S.potentialOperator k r θ := by
        have hode : polarOperator k r (J r) (Jr r) (Jrr r) 0 = 0 := normalizer_ode α (hs hr) hr.1.ne'
        simp only [polarOperator, mul_zero, add_zero] at hode
        dsimp only [Vr, Pr, v, W, P, radial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
        unfold PolarSource.potentialOperator polarOperator
        dsimp only [F, F', F'', q]
        linear_combination -(S.integral (polarKernel (-k / 2)) r θ * G r) * hode
      _ ≤ 0 := by
        rw [S.operator_eq k (hs hr) hr.1.ne' θ, neg_mul, mul_neg, ← mul_assoc]
        apply neg_nonpos.mpr
        refine mul_nonneg (by positivity [G, hpos hr, sub_pos.mpr (hs hr), hr.1]) (integral_nonneg_of_ae ?_)
        filter_upwards [S.supported] with u hu
        exact mul_nonneg (by simpa using hu) (rpow_nonneg (polarDenominator_pos (hs hr) (by simpa using hu) θ).le _)

  have hC0 : Continuous (fun p : ℝ × ℝ ↦ smoothCap p.1 c p.2) := by unfold smoothCap; fun_prop
  have hsmooth (ε : ℝ) (hε : 0 < ε) :
      AntitoneOn (angularMean (fun r θ ↦ smoothCap ε c (U r θ))) (radii) := by
    let d := smoothCapInputDeriv ε c
    let e := smoothCapSecondDeriv ε c
    let C := fun r θ ↦ smoothCap ε c (U r θ)
    let D := fun r θ ↦ d (U r θ)
    let E := fun r θ ↦ e (U r θ)
    let A := D * V
    let A' := E * Ur * V + D * Vr
    let B := D * F' .angular
    let B' := E * Ut * F' .angular + D * F'' .angular
    let Cr := D * Ur
    have dc x := smoothCap_derivs (c := c) hε x
    have hd : Continuous d := continuous_iff_continuousAt.mpr fun x ↦ (dc x).2.continuousAt
    have he : Continuous e := by unfold e smoothCapSecondDeriv; fun_prop (disch := intro; positivity [hε])
    have hC : PolarContinuous C := hC0.comp_continuousOn (continuousOn_const.prodMk cU)
    have hdU := hd.comp_continuousOn cU
    have heU := he.comp_continuousOn cU
    have hCr : PolarContinuous Cr := hdU.mul cUr
    have hA : PolarContinuous A := hdU.mul cV
    have hA' : PolarContinuous A' := ((heU.mul cUr).mul cV).add (hdU.mul cVr)
    have hB' : PolarContinuous B' := ((heU.mul cUt).mul (hD .angular)).add (hdU.mul (hDD .angular))
    have dA r (hr : r ∈ openRadii) θ :=
      ((dc _).2.comp r (dr r hr θ)).mul (dv r hr θ)
    have dB r (hr : r ∈ openRadii) θ : HasDerivAt (B r) (B' r θ) θ :=
      ((dc _).2.comp θ (dt r hr θ)).mul
        (S.integral_kernelD_hasDerivAt .angular q (hs hr) θ)
    have hanti := antitoneOn_unit_of_hasDerivAt_nonpos (continuousOn_angularMean hA)
      (fun r hr ↦ hasDerivAt_angularMean hr hA hA' dA) (fun r hr ↦ by
      have hr' := Ioo_subset_Ico_self hr
      have hi {F : PolarFunction} (hc : PolarContinuous F) :=
        integrable_compact_slice isCompact_Icc ae_mem_angle hc hr'
      have hn := integral_mono (hi hA') ((hi hB').const_mul (-v r)) (fun θ ↦ by
        dsimp only [A', B', D, E, Pi.add_apply, Pi.mul_apply]
        rw [flux r hr θ]
        have hd' : 0 ≤ d (U r θ) := by
          dsimp [d, smoothCapInputDeriv]
          apply div_nonneg _ (by positivity)
          rw [sub_nonneg, div_le_one (by positivity)]
          exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right hε.le)
        have he' : e (U r θ) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) (by positivity)
        have h1 := mul_nonpos_of_nonneg_of_nonpos hd' (div_nonpos r hr θ)
        have h2 := mul_nonpos_of_nonpos_of_nonneg he'
          (show 0 ≤ w r * Ur r θ ^ 2 + v r * (Ut r θ * F' .angular r θ) by
            dsimp only [Ut, radial, Pi.div_apply, v, G]
            rw [div_mul_eq_mul_div, ← sq]
            positivity [pos r hr, hpos hr, hr.1, sub_pos.mpr (hs hr)])
        nlinarith)
      rw [integral_const_mul, integral_angleMeasure_eq (B' r), intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ ↦ dB r hr θ) ((hB'.uncurry_left r hr').intervalIntegrable_of_Icc (by linarith [pi_pos]))] at hn
      simpa [angularMean, B, D, period r, period_t r] using hn)
    apply antitoneOn_unit_of_hasDerivAt_nonpos (continuousOn_angularMean hC)
      (fun r hr ↦ hasDerivAt_angularMean hr hC hCr
        (fun u hu θ ↦ (dc _).1.comp u (dr u hu θ)))
    intro r hr
    have hneg := hanti (show (0 : ℝ) ∈ radii by simp) (Ioo_subset_Ico_self hr) hr.1.le
    apply nonpos_of_mul_nonpos_right _ (pos r hr)
    simpa only [angularMean, A, Cr, D, Pi.mul_apply, hV0, mul_zero, integral_zero, flux r hr,
      mul_left_comm (d _), integral_const_mul] using hneg
  have hc {r : ℝ} (hr : r ∈ radii) :
      ContinuousOn (fun ε ↦ angularMean (fun u θ ↦ smoothCap ε c (U u θ)) r) univ :=
    continuousOn_integral_of_compact_support isCompact_Icc ae_mem_angle
      (hC0.comp_continuousOn (continuousOn_fst.prodMk ((cU.uncurry_left r hr).comp
        continuousOn_snd (fun _ hp ↦ hp.2))))
  intro r hr R hR h
  simpa only [smoothCap_zero, angularMean, U, radial, Pi.div_apply] using le_on_closure
    (fun ε (hε : ε ∈ Ioi 0) ↦ hsmooth ε hε hr hR h) (hc hR |>.mono (subset_univ _)) (hc hr |>.mono (subset_univ _))
    (by simp : (0 : ℝ) ∈ closure (Ioi 0))

/-- With source concentrated at the origin the quotient is the reciprocal normalizer. -/
theorem normalizer_mono (α : ℝ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) :
    normalizer α r ≤ normalizer α R := by
  let S : PolarSource := ⟨Measure.dirac 0, by simp, inferInstance⟩
  have eq (u θ : ℝ) : S.integral (polarKernel (-(α + 2) / 2)) u θ = 1 := by
    simp [S, PolarSource.integral, integral_dirac, polarKernel, polarDenominator, radialComponent]
  have hr' : r ∈ radii := ⟨hr, hrR.trans_lt hR⟩
  have hR' : R ∈ radii := ⟨hr.trans hrR, hR⟩
  have h := S.antitoneOn_normalized_cap α (max (1 / normalizer α r) (1 / normalizer α R)) hr' hR' hrR
  simp only [angularMean, eq, min_eq_left (le_max_left _ _), min_eq_left (le_max_right _ _),
    integral_const, probReal_univ, one_smul, one_div] at h
  exact (inv_le_inv₀ (normalizer_pos α hR') (normalizer_pos α hr')).mp h

end BergmanWeakType.Weighted
