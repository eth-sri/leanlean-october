module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenPositivePartApproximation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10LevelSet
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Shifted positive parts in spatial `H¹₀`

This module constructs `(u - k)₊` without representing the nonzero constant
`k` as an element of `H¹₀`.  The construction works on an arbitrary open set.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The shifted positive-part function has Lipschitz constant one. -/
theorem lipschitzWith_max_sub_zero (k : ℝ≥0) :
    LipschitzWith 1 (fun s : ℝ => max (s - (k : ℝ)) 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [show dist a b = |a - b| by rfl]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right] using
    abs_max_sub_max_le_abs (a - (k : ℝ)) (b - (k : ℝ)) 0

/-- A nonnegative shift sends zero to zero. -/
theorem max_sub_zero_at_zero (k : ℝ≥0) :
    max ((0 : ℝ) - (k : ℝ)) 0 = 0 := by
  rw [max_eq_right]
  exact sub_nonpos.mpr k.2

section
variable (k : ℝ≥0) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))
include k f

/-- The literal `L²` composition representing the shifted positive part. -/
def shiftedPositivePartValue :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  (lipschitzWith_max_sub_zero k).compLp (max_sub_zero_at_zero k) f

/-- Evaluation of the shifted positive-part `L²` composition. -/
theorem coeFn_shiftedPositivePartValue :
    shiftedPositivePartValue k f =ᵐ[PDE.volumeOn Ω]
      fun x => max (f x - (k : ℝ)) 0 := by
  simpa only [shiftedPositivePartValue, Function.comp_def] using
    (lipschitzWith_max_sub_zero k).coeFn_compLp (max_sub_zero_at_zero k) f

private theorem norm_shiftedPositivePartValue_le :
    ‖shiftedPositivePartValue k f‖ ≤ ‖f‖ := by
  simpa only [shiftedPositivePartValue, NNReal.coe_one, one_mul] using
    (lipschitzWith_max_sub_zero k).norm_compLp_le
      (max_sub_zero_at_zero k) f

end

private theorem h1FunctionOfH10_hasSupportedSmoothApproximation
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    Nonempty (h1FunctionOfH10HilbertGraph hΩ u).SupportedSmoothApproximation := by
  let ug := h10HilbertGraphContinuousLinearEquiv hΩ u
  rcases PDE.H10Graph.exists_tendsto_smooth hΩ ug with ⟨φ, hφ⟩
  let w := h1FunctionOfH10HilbertGraph hΩ u
  have hvalue : Tendsto
      (fun n => (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.1)
      atTop (𝓝 (valueCLM hΩ u)) := by
    simpa only [ug, h10HilbertGraphContinuousLinearEquiv, valueCLM_apply,
      h1HilbertGraphContinuousLinearEquiv_apply, Function.comp_def,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans, ContinuousLinearEquiv.ofEq,
      ContinuousLinearEquiv.ofSubmodule'_apply, PDE.H1HilbertGraph.value,
      PDE.H1HilbertGraph.gradient, PDE.H1HilbertGraph.toH1Graph] using!
      ((continuous_fst.comp continuous_subtype_val).tendsto _ |>.comp hφ)
  have hgradient : Tendsto
      (fun n => (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2)
      atTop (𝓝 (gradientCLM hΩ u)) := by
    simpa only [ug, h10HilbertGraphContinuousLinearEquiv, gradientCLM_apply,
      h1HilbertGraphContinuousLinearEquiv_apply, Function.comp_def,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans, ContinuousLinearEquiv.ofEq,
      ContinuousLinearEquiv.ofSubmodule'_apply, PDE.H1HilbertGraph.value,
      PDE.H1HilbertGraph.gradient, PDE.H1HilbertGraph.toH1Graph] using!
      ((continuous_snd.comp continuous_subtype_val).tendsto _ |>.comp hφ)
  refine ⟨{
    approx := fun n => (φ n).toFun
    approx_smooth := fun n => (φ n).contDiff
    approx_hasCompactSupport := fun n => (φ n).hasCompactSupport
    approx_tsupport_subset := fun n => (φ n).tsupport_subset
    tendsto_value := ?_
    tendsto_grad := ?_ }⟩
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (φ n).toFun) (fun n => (φ n).memLp_toFun (2 : ℝ≥0∞))
      w.toFun w.memL2).mp (by
        simpa only [w, h1FunctionOfH10HilbertGraph,
          PDE.smoothCompactlySupportedH1Graph,
          PDE.smoothCompactlySupportedW1pGraph,
          PDE.W1pFunction.toW1pGraph, PDE.W1pFunction.ofContDiff,
          Lp.toLp_coeFn, PDE.w1pGraphOfRepresentatives,
          PDE.weakGradientLpPairOfRepresentatives] using! hvalue)
  · intro i
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i))
      (fun n => (φ n).memLp_partialDeriv i (2 : ℝ≥0∞))
      (fun x => w.grad x i) (w.gradMemL2 i)).mp
    have heval := (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i).continuous.tendsto _ |>.comp hgradient
    have hseq : ∀ n,
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2 =
          ((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
            (fun x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i)) := by
      intro n
      apply Lp.ext
      filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
          (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2,
        PDE.W1pFunction.coeFn_toW1pGraph_snd
          (PDE.W1pFunction.ofContDiff hΩ
            ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2),
        ((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).coeFn_toLp] with x hc hg ht
      have hg' :
          ⇑(PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2 x =
            PDE.toHilbertVecField
              (PDE.W1pFunction.ofContDiff hΩ
                ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2).grad x := by
        simpa only [PDE.smoothCompactlySupportedH1Graph,
          PDE.smoothCompactlySupportedW1pGraph] using hg
      have ht' :
          ⇑(((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
            (fun x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i))) x =
            (fderiv ℝ (φ n).toFun x) (PDE.basisVec i) := by
        exact ht
      rw [hc, hg', ht']
      rfl
    have hlim : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ u) =
        (w.gradMemL2 i).toLp (fun x => w.grad x i) := by
      apply Lp.ext
      filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u),
        (w.gradMemL2 i).coeFn_toLp] with x hc ht
      rw [hc, ht]
      rfl
    rw [← hlim]
    simpa only [Function.comp_def, hseq] using heval

section
variable (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0)
include u k

private theorem exists_shiftedPositivePart_data :
    ∃ v : H10HilbertGraph hΩ,
      valueCLM hΩ v = shiftedPositivePartValue k (valueCLM hΩ u) ∧
      ∀ᵐ x ∂(PDE.volumeOn Ω),
        gradientCLM hΩ v x =
          {y | (k : ℝ) < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  let w := h1FunctionOfH10HilbertGraph hΩ u
  obtain ⟨z, hzValue, hzGrad, hzApprox, _⟩ :=
    PDE.H1Function.exists_shiftedPositivePart_nonnegative_supportedSmoothApproximation w
      (Classical.choice (h1FunctionOfH10_hasSupportedSmoothApproximation hΩ u)) k (by
        filter_upwards [gradientCLM_ae_zero_on_level_set hΩ u (k : ℝ)] with x hx
        exact fun h => (WithLp.ofLp_eq_zero 2).2 (hx h))
  let zg : PDE.H10Graph hΩ :=
    ⟨z.toW1pFunction.toW1pGraph, z.mem_h10Graph_of_supportedSmoothApproximation hΩ hzApprox⟩
  refine ⟨(h10HilbertGraphContinuousLinearEquiv hΩ).symm zg, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [PDE.W1pFunction.coeFn_toW1pGraph_fst z.toW1pFunction,
      coeFn_shiftedPositivePartValue k (valueCLM hΩ u)] with x hx hs
    change (zg : PDE.H1Graph Ω).1.1 x = _
    rw [hx, hs]
    exact congrFun hzValue x
  · filter_upwards [PDE.W1pFunction.coeFn_toW1pGraph_snd z.toW1pFunction] with x hx
    change (zg : PDE.H1Graph Ω).1.2 x = _
    rw [hx]
    ext i
    change z.grad x i = _
    rw [hzGrad]
    simp only [w, h1FunctionOfH10HilbertGraph, indicator_apply]
    split <;> rfl

/-- The shifted positive part has a unique spatial `H¹₀` graph representative. -/
theorem exists_unique_h10ShiftedPositivePart :
    ∃! v : H10HilbertGraph hΩ,
      valueCLM hΩ v = shiftedPositivePartValue k (valueCLM hΩ u) := by
  obtain ⟨v, hv, _⟩ := exists_shiftedPositivePart_data hΩ u k
  exact ⟨v, hv, fun z hz => valueCLM_injective hΩ (hz.trans hv.symm)⟩

/-- The canonical shifted positive part `(u - k)₊` in spatial `H¹₀`. -/
noncomputable def h10ShiftedPositivePart : H10HilbertGraph hΩ :=
  Classical.choose (exists_unique_h10ShiftedPositivePart hΩ u k)

/-- The value component of the canonical shifted positive part. -/
@[simp]
theorem valueCLM_h10ShiftedPositivePart :
    valueCLM hΩ (h10ShiftedPositivePart hΩ u k) =
      shiftedPositivePartValue k (valueCLM hΩ u) :=
  (Classical.choose_spec (exists_unique_h10ShiftedPositivePart hΩ u k)).1

end

section
variable (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0)

/-- Evaluation of the value representative of the shifted positive part. -/
theorem coeFn_valueCLM_h10ShiftedPositivePart :
    valueCLM hΩ (h10ShiftedPositivePart hΩ u k) =ᵐ[PDE.volumeOn Ω]
      fun x => max (valueCLM hΩ u x - (k : ℝ)) 0 := by
  rw [valueCLM_h10ShiftedPositivePart]
  exact coeFn_shiftedPositivePartValue k (valueCLM hΩ u)

/-- The weak gradient of `(u - k)₊` is the original gradient precisely on
the strict superlevel set `{k < u}` and is zero elsewhere. -/
theorem gradientCLM_h10ShiftedPositivePart :
    ∀ᵐ x ∂(PDE.volumeOn Ω),
      gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) x =
        {y | (k : ℝ) < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  obtain ⟨v, hv, hvGrad⟩ := exists_shiftedPositivePart_data hΩ u k
  have heq : h10ShiftedPositivePart hΩ u k = v :=
    valueCLM_injective hΩ (valueCLM_h10ShiftedPositivePart hΩ u k |>.trans hv.symm)
  simpa only [heq] using hvGrad

/-- Shifted positive-part truncation contracts the value `L²` norm. -/
theorem norm_valueCLM_h10ShiftedPositivePart_le :
    ‖valueCLM hΩ (h10ShiftedPositivePart hΩ u k)‖ ≤ ‖valueCLM hΩ u‖ := by
  rw [valueCLM_h10ShiftedPositivePart]
  exact norm_shiftedPositivePartValue_le k (valueCLM hΩ u)

end

section
variable (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0)

/-- Shifted positive-part truncation contracts the weak-gradient `L²` norm. -/
theorem norm_gradientCLM_h10ShiftedPositivePart_le :
    ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ u k)‖ ≤ ‖gradientCLM hΩ u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  calc
    eLpNorm (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k)) 2
        (PDE.volumeOn Ω) =
      eLpNorm ({y | (k : ℝ) < valueCLM hΩ u y}.indicator
        (gradientCLM hΩ u)) 2 (PDE.volumeOn Ω) :=
      eLpNorm_congr_ae (gradientCLM_h10ShiftedPositivePart hΩ u k)
    _ ≤ eLpNorm (gradientCLM hΩ u) 2 (PDE.volumeOn Ω) :=
      eLpNorm_mono_ae
        ((Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable.indicator₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.memLp (valueCLM hΩ u)).aestronglyMeasurable.aemeasurable))
        (Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ x))

/-- Shifted positive-part truncation contracts the full spatial `H¹₀`
graph norm, with sharp constant one. -/
theorem norm_h10ShiftedPositivePart_le :
    ‖h10ShiftedPositivePart hΩ u k‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_h10HilbertGraph hΩ, norm_sq_h10HilbertGraph hΩ]
  exact add_le_add
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_valueCLM_h10ShiftedPositivePart_le hΩ u k))
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_gradientCLM_h10ShiftedPositivePart_le hΩ u k))

end

private theorem tendsto_shifted_value_threshold_eLpNorm
    {f : PDE.Vec d → ℝ} (hf : MemLp f (2 : ℝ≥0∞) (PDE.volumeOn Ω))
    {kn : ℕ → ℝ≥0} {k : ℝ≥0} (hk : Tendsto kn atTop (nhds k)) :
    Tendsto (fun n => eLpNorm
      (fun x => max (f x - (kn n : ℝ)) 0 - max (f x - (k : ℝ)) 0)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
  apply PDE.tendsto_eLpNorm_two_zero_of_ae_dominated
    (bound := fun x => (2 : ℝ) * f x)
  · intro n
    exact (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub
      (((continuous_id.sub continuous_const).max continuous_const)
        |>.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · exact hf.const_mul 2
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hnonneg (a : ℝ≥0) : 0 ≤ max (f x - (a : ℝ)) 0 := le_max_right _ _
    have hle (a : ℝ≥0) : max (f x - (a : ℝ)) 0 ≤ |f x| := by
      rcases le_total (f x) (a : ℝ) with h | h
      · rw [max_eq_right (sub_nonpos.mpr h)]
        exact abs_nonneg _
      · rw [max_eq_left (sub_nonneg.mpr h), abs_of_nonneg (a.2.trans h)]
        exact sub_le_self _ a.2
    calc
      |max (f x - (kn n : ℝ)) 0 - max (f x - (k : ℝ)) 0| ≤
          max (f x - (kn n : ℝ)) 0 + max (f x - (k : ℝ)) 0 :=
        abs_sub_le_iff.2 ⟨by linarith [hnonneg k], by linarith [hnonneg (kn n)]⟩
      _ ≤ |f x| + |f x| := add_le_add (hle (kn n)) (hle k)
      _ = 2 * |f x| := by ring
  · filter_upwards with x
    have hkr : Tendsto (fun n => (kn n : ℝ)) atTop (nhds (k : ℝ)) :=
      continuous_subtype_val.tendsto k |>.comp hk
    have hm : Tendsto (fun a : ℝ => max (f x - a) 0) (nhds (k : ℝ))
        (nhds (max (f x - (k : ℝ)) 0)) :=
      ((show Continuous (fun a : ℝ => max (f x - a) 0) from
        (continuous_const.sub continuous_id).max continuous_const).tendsto _)
    have hc : Tendsto (fun _ : ℕ => max (f x - (k : ℝ)) 0) atTop
        (nhds (max (f x - (k : ℝ)) 0)) := tendsto_const_nhds
    simpa only [Function.comp_def, sub_self] using (hm.comp hkr).sub hc

private theorem tendsto_moving_indicator_sub_indicator
    {f : ℕ → PDE.Vec d → ℝ} {f₀ : PDE.Vec d → ℝ}
    {kn : ℕ → ℝ≥0} {k : ℝ≥0} {g : PDE.Vec d → WithLp 2 (PDE.Vec d)}
    {x : PDE.Vec d} (hf : Tendsto (fun n => f n x) atTop (nhds (f₀ x)))
    (hk : Tendsto kn atTop (nhds k)) (hzero : f₀ x = (k : ℝ) → g x = 0) :
    Tendsto (fun n =>
      {y | (kn n : ℝ) < f n y}.indicator g x -
        {y | (k : ℝ) < f₀ y}.indicator g x) atTop (nhds 0) := by
  have hdiff : Tendsto (fun n => f n x - (kn n : ℝ)) atTop
      (nhds (f₀ x - (k : ℝ))) :=
    hf.sub (continuous_subtype_val.tendsto k |>.comp hk)
  rcases lt_trichotomy (f₀ x) (k : ℝ) with hlt | heq | hgt
  · have hevent : ∀ᶠ n in atTop, f n x - (kn n : ℝ) < 0 :=
      (tendsto_order.1 hdiff).2 _ (sub_neg.mpr hlt)
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, not_lt.mpr (sub_nonpos.mp hn.le),
      hlt.not_gt, sub_self]
  · have hg : g x = 0 := hzero heq
    have hfun : (fun n =>
        {y | (kn n : ℝ) < f n y}.indicator g x -
          {y | (k : ℝ) < f₀ y}.indicator g x) =
        fun _ : ℕ => (0 : WithLp 2 (PDE.Vec d)) := by
      funext n
      simp only [indicator_apply, hg]
      split <;> split <;> simp
    rw [hfun]
    exact tendsto_const_nhds
  · have hevent : ∀ᶠ n in atTop, 0 < f n x - (kn n : ℝ) :=
      (tendsto_order.1 hdiff).1 _ (sub_pos.mpr hgt)
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, sub_pos.mp hn, hgt, sub_self]

private theorem indicator_sub_add_indicator_difference
    {E : Type*} [AddCommGroup E] {A B : Set (PDE.Vec d)}
    (a b : PDE.Vec d → E) (x : PDE.Vec d) :
    A.indicator (a - b) x + (A.indicator b x - B.indicator b x) =
      A.indicator a x - B.indicator b x := by
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    simp [hxA, hxB]

private theorem tendsto_h10_of_value_gradient
    (hΩ : IsOpen Ω) {un : ℕ → H10HilbertGraph hΩ} {u : H10HilbertGraph hΩ}
    (hv : Tendsto (fun n => valueCLM hΩ (un n)) atTop (nhds (valueCLM hΩ u)))
    (hg : Tendsto (fun n => gradientCLM hΩ (un n)) atTop
      (nhds (gradientCLM hΩ u))) : Tendsto un atTop (nhds u) := by
  rw [Metric.tendsto_atTop] at hv hg ⊢
  intro ε hε
  obtain ⟨Nv, hNv⟩ := hv (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  obtain ⟨Ng, hNg⟩ := hg (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  refine ⟨max Nv Ng, fun n hn => ?_⟩
  have hvn := hNv n (le_trans (le_max_left _ _) hn)
  have hgn := hNg n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm]
  change ‖un n - u‖ < ε
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).1
  rw [norm_sq_h10HilbertGraph hΩ]
  simp only [map_sub]
  rw [dist_eq_norm] at hvn hgn
  have hv2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hvn
  have hg2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hgn
  rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at hv2 hg2
  linarith

/-- The shifted positive part is jointly strongly continuous in the spatial
`H¹₀` function and the nonnegative threshold. -/
theorem continuous_h10ShiftedPositivePart (hΩ : IsOpen Ω) :
    Continuous (fun p : H10HilbertGraph hΩ × ℝ≥0 =>
      h10ShiftedPositivePart hΩ p.1 p.2) := by
  rw [continuous_iff_seqContinuous]
  rintro pn ⟨u, k⟩ hpn
  have hu : Tendsto (fun n => (pn n).1) atTop (nhds u) :=
    (continuous_fst.tendsto (u, k)).comp hpn
  have hk : Tendsto (fun n => (pn n).2) atTop (nhds k) :=
    (continuous_snd.tendsto (u, k)).comp hpn
  have huValue : Tendsto (fun n => valueCLM hΩ (pn n).1)
      atTop (nhds (valueCLM hΩ u)) := ((valueCLM hΩ).continuous.tendsto u).comp hu
  have huGrad : Tendsto (fun n => gradientCLM hΩ (pn n).1)
      atTop (nhds (gradientCLM hΩ u)) := ((gradientCLM hΩ).continuous.tendsto u).comp hu
  let μ := PDE.volumeOn Ω
  let f : ℕ → PDE.Vec d → ℝ := fun n => valueCLM hΩ (pn n).1
  let f₀ : PDE.Vec d → ℝ := valueCLM hΩ u
  let g : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) :=
    fun n => gradientCLM hΩ (pn n).1
  let g₀ : PDE.Vec d → WithLp 2 (PDE.Vec d) := gradientCLM hΩ u
  have hvalue : Tendsto
      (fun n => valueCLM hΩ (h10ShiftedPositivePart hΩ (pn n).1 (pn n).2))
      atTop (nhds (valueCLM hΩ (h10ShiftedPositivePart hΩ u k))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hfun : Tendsto (fun n => eLpNorm
        (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
          max (f₀ x - ((pn n).2 : ℝ)) 0) 2 μ) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'
          (fun n => valueCLM hΩ (pn n).1) (valueCLM hΩ u)).1 huValue)
        (fun _ => zero_le') (fun n => ?_)
      apply eLpNorm_mono_ae
        ((((continuous_id.sub continuous_const).max continuous_const)
          |>.comp_aestronglyMeasurable (Lp.memLp (valueCLM hΩ (pn n).1)).aestronglyMeasurable).sub
          (((continuous_id.sub continuous_const).max continuous_const)
            |>.comp_aestronglyMeasurable (Lp.memLp (valueCLM hΩ u)).aestronglyMeasurable))
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simpa only [f, f₀, Pi.sub_apply, id_eq, sub_sub_sub_cancel_right] using
        abs_max_sub_max_le_abs (f n x - ((pn n).2 : ℝ))
          (f₀ x - ((pn n).2 : ℝ)) 0
    have hthreshold := tendsto_shifted_value_threshold_eLpNorm
      (Lp.memLp (valueCLM hΩ u)) hk
    have hsum := hfun.add hthreshold
    have hraw : Tendsto (fun n => eLpNorm
        (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
          max (f₀ x - (k : ℝ)) 0) 2 μ) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hsum) (fun _ => zero_le') (fun n => ?_)
      have hdecomp : (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
          max (f₀ x - (k : ℝ)) 0) =
          (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
            max (f₀ x - ((pn n).2 : ℝ)) 0) +
          (fun x => max (f₀ x - ((pn n).2 : ℝ)) 0 -
            max (f₀ x - (k : ℝ)) 0) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [hdecomp]
      exact eLpNorm_add_le (by norm_num)
    refine hraw.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [coeFn_valueCLM_h10ShiftedPositivePart hΩ (pn n).1 (pn n).2,
        coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with x hnx hx
    rw [Pi.sub_apply, hnx, hx]
  let R : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) := fun n x =>
    {y | ((pn n).2 : ℝ) < f n y}.indicator g₀ x -
      {y | (k : ℝ) < f₀ y}.indicator g₀ x
  have hR : Tendsto (fun n => eLpNorm (R n) 2 μ) atTop (nhds 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, hms, hae⟩ :=
      (tendstoInMeasure_of_tendsto_Lp (huValue.comp hns)).exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    apply PDE.tendsto_eLpNorm_two_zero_of_ae_dominated
      (bound := g₀)
    · intro n
      apply AEStronglyMeasurable.sub
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.memLp (valueCLM hΩ (pn (ns (ms n))).1)).aestronglyMeasurable.aemeasurable)]
        exact (Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable.restrict
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.memLp (valueCLM hΩ u)).aestronglyMeasurable.aemeasurable)]
        exact (Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable.restrict
    · exact Lp.memLp (gradientCLM hΩ u)
    · intro n
      filter_upwards with x
      simp only [R, g₀, indicator_apply]
      split <;> split <;> simp
    · filter_upwards [hae, gradientCLM_ae_zero_on_level_set hΩ u (k : ℝ)] with x hx hz
      exact tendsto_moving_indicator_sub_indicator hx
        (hk.comp (hns.comp hms.tendsto_atTop)) hz
  have hgrad : Tendsto
      (fun n => gradientCLM hΩ (h10ShiftedPositivePart hΩ (pn n).1 (pn n).2))
      atTop (nhds (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) := by
    let q : ℕ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := fun n =>
      gradientCLM hΩ (h10ShiftedPositivePart hΩ (pn n).1 (pn n).2)
    let q₀ : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      gradientCLM hΩ (h10ShiftedPositivePart hΩ u k)
    change Tendsto q atTop (nhds q₀)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hfirst : Tendsto (fun n => eLpNorm
        ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀)) 2 μ)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 huGrad)
        (fun _ => zero_le') (fun n => eLpNorm_mono_ae
          (((Lp.memLp (gradientCLM hΩ (pn n).1)).aestronglyMeasurable.sub
            (Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable).indicator₀
            (nullMeasurableSet_lt aemeasurable_const
              (Lp.memLp (valueCLM hΩ (pn n).1)).aestronglyMeasurable.aemeasurable))
          (Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ x)))
    have hraw : Tendsto (fun n => eLpNorm
        ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀) + R n) 2 μ)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hfirst.add hR) (fun _ => zero_le') (fun n => ?_)
      exact eLpNorm_add_le (by norm_num)
    refine hraw.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [gradientCLM_h10ShiftedPositivePart hΩ (pn n).1 (pn n).2,
        gradientCLM_h10ShiftedPositivePart hΩ u k] with x hnx hx
    have hpoint :
        ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀) + R n) x =
          q n x - q₀ x := by
      calc
      ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀) + R n) x =
          {y | ((pn n).2 : ℝ) < f n y}.indicator (g n) x -
            {y | (k : ℝ) < f₀ y}.indicator g₀ x := by
          rw [Pi.add_apply]
          exact indicator_sub_add_indicator_difference (g n) g₀ x
      _ = q n x - q₀ x := by
          dsimp only [f, f₀, g, g₀, q, q₀]
          exact congrArg₂ (fun a b : WithLp 2 (PDE.Vec d) => a - b)
            hnx.symm hx.symm
    simpa only [Pi.sub_apply] using hpoint
  exact tendsto_h10_of_value_gradient hΩ hvalue hgrad

end HypoellipticAleksandrov.Parabolic.Dirichlet
