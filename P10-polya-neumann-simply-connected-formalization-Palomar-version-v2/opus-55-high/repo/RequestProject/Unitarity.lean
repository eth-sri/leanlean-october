module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Star
public import RequestProject.Picard

/-!
# Unitarity of solutions of skew-adjoint linear Volterra equations

If `C : ℝ → A` is a bounded strongly measurable coefficient with values in a complete normed
star algebra and `C(s)^* = -C(s)`, then every continuous solution of
`W(θ) = 1 + ∫₀^θ C(s) W(s) ds` on `[0, L]` is unitary.  This is the unitarity part of
Lemma 10.2 of the paper.

The proof goes through the almost-everywhere derivative of the solution, using the
Lebesgue differentiation theorem for Banach-valued functions and the fact that an absolutely
continuous function with vanishing a.e. derivative is constant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace PolyaNeumann

variable {E : Type*}

/-- The interval version of the Lebesgue differentiation theorem for Banach-valued
functions: if `f` is locally integrable then, for almost every `x` and every `c`,
`x ↦ ∫_c^x f` has derivative `f x` at `x`. -/
theorem ae_hasDerivAt_integral_of_locallyIntegrable [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc    |>.symm
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily volume 1).ae_tendsto_average hf] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg, intervalIntegral.integral_of_ge, hy, this, ← neg_smul, ← inv_neg]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, this]

/-- Integral form of an a.e. derivative: a Lipschitz function on `[0, L]` whose a.e.
derivative is a bounded integrable `g` is `f 0 + ∫₀^θ g`. -/
theorem eq_add_integral_of_ae_hasDerivAt [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {L B : ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc 0 L)) (hg : IntegrableOn g (Icc 0 L))
    (hgB : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ B)
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in 0..θ, g s := by
  set G : ℝ → E := (Icc 0 L).indicator g
  have hGi  := hg.integrable_indicator measurableSet_Icc
  have hGB : ∀ x, ‖G x‖ ≤ max B 0 := fun x => by
    by_cases hx : x ∈ Icc 0 L
    · simp_all [G]
    simp [G, indicator_of_notMem hx]
  set F : ℝ → E := fun x => ∫ t in 0..x, G t
  have hFL : LipschitzOnWith (max B 0).toNNReal F (Icc 0 L) := by
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)]
    rw [intervalIntegral.integral_interval_sub_left hGi.intervalIntegrable
      hGi.intervalIntegrable]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hGB t)
  have hFeq : ∀ θ ∈ Icc 0 L, F θ = ∫ t in 0..θ, g t := fun θ hθ =>
    intervalIntegral.integral_congr fun t ht => by
      have : t ∈ Icc 0 L := by rw [uIcc_of_le hθ.1] at ht; grind
      simp [G, indicator_of_mem this]
  rcases lt_or_ge L 0 with hL | hL
  · simp_all
  have hac : AbsolutelyContinuousOnInterval (f - F) 0 L := by
    rw [← uIcc_of_le hL] at hf hFL
    exact hf.absolutelyContinuousOnInterval.sub hFL.absolutelyContinuousOnInterval
  obtain ⟨c, hc⟩ := hac.const_of_ae_hasDerivAt_zero (by
    have h₁ : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    have h₂ : ∀ᵐ x : ℝ, x ≠ L := by simp [ae_iff]
    filter_upwards [hd, ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable,
      h₁, h₂] with x hx hxF hx0 hxL hxI
    rw [uIcc_of_le hL] at hxI
    have := (hx ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxL⟩).sub (hxF 0)
    simpa [indicator_of_mem hxI] using this)
  intro θ hθ
  have h0 := hc 0 (by norm_num)
  have hθ' := hc θ (by simp_all)
  simp only [Pi.sub_apply, F, intervalIntegral.integral_same] at h0 hθ'
  grind

/-- A Grönwall-type lemma: if `‖D θ‖ ≤ ∫₀^θ K ‖D‖` on `[0, L]` then `D = 0` there. -/
theorem eq_zero_of_norm_le_integral [NormedAddCommGroup E] {D : ℝ → E}
    {L K : ℝ} (hK : 0 ≤ K) (hD : ContinuousOn D (Icc 0 L))
    (h : ∀ θ ∈ Icc 0 L, ‖D θ‖ ≤ ∫ s in 0..θ, K * ‖D s‖) :
    ∀ θ ∈ Icc 0 L, D θ = 0 := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hbound : ∀ n : ℕ, ∀ θ ∈ Icc 0 L, ‖D θ‖ ≤ S * (K * θ) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => simp_all
    | succ n ih =>
      intro θ hθ
      refine (h θ hθ).trans ?_
      have hint2 : IntervalIntegrable
          (fun s => K * (S * (K * s) ^ n / n.factorial)) volume 0 θ := by
        apply Continuous.intervalIntegrable; fun_prop
      refine (intervalIntegral.integral_mono_on hθ.1 (ContinuousOn.intervalIntegrable (continuousOn_const.mul (hD.mono (by
        rw [uIcc_of_le hθ.1]; grind)).norm)) hint2 fun s hs => ?_).trans_eq ?_
      · exact mul_le_mul_of_nonneg_left (ih s ⟨hs.1, hs.2.trans hθ.2⟩) hK
      · have : (fun s  => K * (S * (K * s) ^ n / n.factorial)) =
            fun s => (K * S * K ^ n / n.factorial) * s ^ n := by
          funext s; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
        push_cast
        field_simp
        ring
  intro θ hθ
  have h0  := ge_of_tendsto' (by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (K * θ)).const_mul S
    simpa [mul_div_assoc] using this) fun n => hbound n θ hθ
  simp_all

/-- A product of bounded Lipschitz functions is Lipschitz. -/
theorem lipschitzOnWith_mul_of_bounded {A : Type*} [NormedRing A] {f g : ℝ → A}
    {s : Set ℝ} {Kf Kg : NNReal} {B : ℝ} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) (hfB : ∀ x ∈ s, ‖f x‖ ≤ B) (hgB : ∀ x ∈ s, ‖g x‖ ≤ B) :
    LipschitzOnWith (Kf * B.toNNReal + B.toNNReal * Kg) (fun x => f x * g x) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hB  := (norm_nonneg _).trans (hfB x hx)
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm] at h1 h2 ⊢
  have e : f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) := by noncomm_ring
  rw [e]
  push_cast
  rw [Real.coe_toNNReal _ hB]
  calc ‖(f x - f y) * g x + f y * (g x - g y)‖
      ≤ ‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (Kf * dist x y) * B + B * (Kg * dist x y) := by
        gcongr
        all_goals simp_all
    _ = _ := by ring

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}

/-- A solution of the Volterra equation has a.e. derivative `C W` in `(0, L)`. -/
theorem volterra_ae_hasDerivAt (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in 0..θ, C s * W s) :
    ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt W (C θ * W θ) θ := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun θ hθ =>
      absurd (hθ.1.trans hθ.2) (not_lt.mpr hL.le)
  set g : ℝ → A := (Icc 0 L).indicator (fun s => C s * W s)
  have hgi : Integrable g := by
    have h1 := intervalIntegrable_mul_of_continuousOn hC hM hW  ⟨hL, le_rfl⟩
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL,
      ← integrableOn_Icc_iff_integrableOn_Ioc] at h1
    exact h1.integrable_indicator measurableSet_Icc
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hgi.locallyIntegrable]
    with θ hθ hmem
  have h1 := (hθ 0).const_add 1
  rw [show g θ = C θ * W θ by simp [g, indicator_of_mem (Ioo_subset_Icc_self hmem)]] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
  rw [eW x (Ioo_subset_Icc_self hx)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  have : t ∈ Icc 0 L := by rw [uIcc_of_le hx.1.le] at ht; grind
  simp [g, indicator_of_mem this]

omit [CompleteSpace A] in
/-- A solution of the Volterra equation is Lipschitz on `[0, L]`. -/
theorem volterra_lipschitzOn (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in 0..θ, C s * W s) :
    ∃ K, LipschitzOnWith K W (Icc 0 L) := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hM0  := (norm_nonneg _).trans (hM 0)
  refine ⟨(M * max S 0).toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hM0 (le_max_right _ _)), eW x hx, eW y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_mul_of_continuousOn hC hM hW hx)
      (intervalIntegrable_mul_of_continuousOn hC hM hW hy)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have : t ∈ Icc 0 L := by
    grind
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hM t) ((hS t this).trans (le_max_left _ _)) (norm_nonneg _) hM0)

variable [StarRing A] [StarModule ℝ A] [NormedStarGroup A]

/-- Unitarity for skew-adjoint linear Volterra equations. -/
theorem volterra_unitary (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hskew : ∀ s, star (C s) = -C s) (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in 0..θ, C s * W s) :
    ∀ θ ∈ Icc 0 L, star (W θ) * W θ = 1 ∧ W θ * star (W θ) = 1 := by
  rcases lt_or_ge L 0 with hL | hL
  · simp_all
  have hM0  := (norm_nonneg _).trans (hM 0)
  have hW0 : W 0 = 1 := by simp_all
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hS0  := (norm_nonneg _).trans (hS 0 ⟨le_rfl, hL⟩)
  obtain ⟨K, hK⟩ := volterra_lipschitzOn hC hM hW eW
  have hKs : LipschitzOnWith K (fun θ => star (W θ)) (Icc 0 L) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ← star_sub, norm_star, ← dist_eq_norm]
      exact hK.dist_le_mul x hx y hy
  have hSs : ∀ x ∈ Icc 0 L, ‖star (W x)‖ ≤ S := fun x hx => by rw [norm_star]; simp_all
  have hd := volterra_ae_hasDerivAt hC hM hW eW
  have hds : ∀ᵐ θ, θ ∈ Ioo 0 L →
      HasDerivAt (fun θ => star (W θ)) (-(star (W θ) * C θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    have := (hθ hmem).star
    simp_all
  intro θ hθ
  constructor
  · have hP := eq_add_integral_of_ae_hasDerivAt  (B := 0)
      (lipschitzOnWith_mul_of_bounded hKs hK hSs hS) integrableOn_zero
      (fun _ _ => by simp) (by
        filter_upwards [hd, hds] with θ h1 h2 hmem
        have := (h2 hmem).mul (h1 hmem)
        convert this using 1
        noncomm_ring)
    simp_all
  · set Q : ℝ → A := fun θ => W θ * star (W θ)
    have hQc  := hW.mul hW.star
    have hQB  := fun x hx =>
      (norm_mul_le _ _).trans (mul_le_mul (hS x hx) (hSs x hx) (norm_nonneg _) hS0)
    set g : ℝ → A := fun s => C s * Q s - Q s * C s
    have hgB : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ 2 * M * (S * S) := fun x hx => by
      calc ‖g x‖ ≤ ‖C x * Q x‖ + ‖Q x * C x‖ := norm_sub_le _ _
        _ ≤ M * (S * S) + (S * S) * M :=
          add_le_add
            ((norm_mul_le _ _).trans (mul_le_mul (hM x) (hQB x hx) (norm_nonneg _) hM0))
            ((norm_mul_le _ _).trans
              (mul_le_mul (hQB x hx) (hM x) (norm_nonneg _) (mul_nonneg hS0 hS0)))
        _ = _ := by ring
    have hgi : IntegrableOn g (Icc 0 L) :=
      Integrable.of_bound ((hC.restrict.mul (hQc.aestronglyMeasurable measurableSet_Icc)).sub
        ((hQc.aestronglyMeasurable measurableSet_Icc).mul hC.restrict)) (2 * M * (S * S))
        ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB))
    have hQ := eq_add_integral_of_ae_hasDerivAt (lipschitzOnWith_mul_of_bounded hK hKs hS hSs)
      hgi hgB (by
        filter_upwards [hd, hds] with θ h1 h2 hmem
        have := (h1 hmem).mul (h2 hmem)
        convert this using 1
        grind)
    set D : ℝ → A := fun θ => Q θ - 1
    have hDc : ContinuousOn D (Icc 0 L) := hQc.sub continuousOn_const
    have hDeq : ∀ θ ∈ Icc 0 L, D θ = ∫ s in 0..θ, g s := fun θ hθ => by
      grind
    have hgD : ∀ s, ‖g s‖ ≤ 2 * M * ‖D s‖ := fun s => by
      have : g s = C s * D s - D s * C s := by grind
      rw [this]
      calc ‖C s * D s - D s * C s‖ ≤ ‖C s * D s‖ + ‖D s * C s‖ := norm_sub_le _ _
        _ ≤ M * ‖D s‖ + ‖D s‖ * M :=
          add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _)))
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM s) (norm_nonneg _)))
        _ = _ := by ring
    exact sub_eq_zero.mp (eq_zero_of_norm_le_integral (K := 2 * M) (by positivity) hDc (fun θ hθ => by
      rw [hDeq θ hθ]
      refine (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans ?_
      refine intervalIntegral.integral_mono_on hθ.1 ?_ ?_ fun s _ => hgD s
      · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hθ.1).mpr
          (hgi.mono_set (Icc_subset_Icc le_rfl hθ.2))).norm
      · exact ContinuousOn.intervalIntegrable (continuousOn_const.mul (hDc.mono (by
        rw [uIcc_of_le hθ.1]; grind)).norm)) θ hθ)

end PolyaNeumann

end
