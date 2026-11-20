module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Star
public import RequestProject.VolterraUniqueness
public import Mathlib.Topology.Order.ProjIcc
public import RequestProject.VectorFTC
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

/-- A Grönwall-type lemma: if `‖D θ‖ ≤ ∫₀^θ K ‖D‖` on `[0, L]` then `D = 0` there. -/
theorem eq_zero_of_norm_le_integral {E : Type*} [NormedAddCommGroup E] {D : ℝ → E}
    {L K : ℝ} (hK : 0 ≤ K) (hD : ContinuousOn D (Icc 0 L))
    (h : ∀ θ ∈ Icc 0 L, ‖D θ‖ ≤ ∫ s in (0 : ℝ)..θ, K * ‖D s‖) :
    ∀ θ ∈ Icc 0 L, D θ = 0 := by
  intro θ hθ
  let D' := IccExtend (hθ.1.trans hθ.2) (fun t : Icc 0 L => D t)
  have he (t) (ht : t ∈ Icc 0 L) : D' t = D t := IccExtend_of_mem _ _ ht
  rw [← he θ hθ]
  apply continuous_eq_zero_of_norm_le_volterra (h := D') (continuousOn_iff_continuous_domRestrict.mp hD).Icc_extend' hK _ θ hθ
  intro t ht
  rw [he t ht, ← intervalIntegral.integral_const_mul]
  refine (h t ht).trans_eq (intervalIntegral.integral_congr fun x hx => ?_)
  rw [uIcc_of_le ht.1] at hx
  rw [he x ⟨hx.1, hx.2.trans ht.2⟩]

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
  calc _
      ≤ _ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (Kf * dist x y) * B + B * (Kg * dist x y) := by
        bound
    _ = _ := by ring

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}

section

variable (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s)
include eW hC hM hW

/-- A solution of the Volterra equation has a.e. derivative `C W` in `(0, L)`. -/
theorem volterra_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt W (C θ * W θ) θ := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun θ hθ =>
      absurd (hθ.1.trans hθ.2) (not_lt.mpr hL.le)
  have hi := intervalIntegrable_mul_of_continuousOn hC hM hW (θ := L) ⟨hL, le_rfl⟩
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach hL hi] with θ hθ hmem
  apply ((hθ hmem).const_add (1 : A)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
  exact eW x (Ioo_subset_Icc_self hx)

omit [CompleteSpace A] in
/-- A solution of the Volterra equation is Lipschitz on `[0, L]`. -/
theorem volterra_lipschitzOn :
    ∃ K, LipschitzOnWith K W (Icc 0 L) := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hM0  := (norm_nonneg _).trans (hM 0)
  refine ⟨(M * max S 0).toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [dist_eq_norm, Real.coe_toNNReal _ ((by positivity)), Real.dist_eq,
    eW x hx, eW y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_mul_of_continuousOn hC hM hW hx)
      (intervalIntegrable_mul_of_continuousOn hC hM hW hy)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have : t ∈ Icc 0 L := by
    grind
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hM t) ((by grind)) (norm_nonneg _) hM0)

end

variable [StarRing A] [StarModule ℝ A] [NormedStarGroup A]

/-- Unitarity for skew-adjoint linear Volterra equations. -/
theorem volterra_unitary (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hskew : ∀ s, star (C s) = -C s) (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ θ ∈ Icc 0 L, star (W θ) * W θ = 1 ∧ W θ * star (W θ) = 1 := by
  rcases lt_or_ge L 0 with hL | hL
  · grind
  have hM0  := (norm_nonneg _).trans (hM 0)
  have hW0 : W 0 = 1 := by simpa using eW 0 ⟨le_rfl, hL⟩
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hS0  := (norm_nonneg _).trans (hS 0 ⟨le_rfl, hL⟩)
  obtain ⟨K, hK⟩ := volterra_lipschitzOn hC hM hW eW
  have hKs : LipschitzOnWith K (fun θ => star (W θ)) (Icc 0 L) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ← star_sub, norm_star, ← dist_eq_norm]
      exact hK.dist_le_mul x hx y hy
  have hSs : ∀ x ∈ Icc 0 L, ‖star (W x)‖ ≤ S := fun x hx => by rw [norm_star]; exact hS x hx
  have hd := volterra_ae_hasDerivAt hC hM hW eW
  have hds : ∀ᵐ θ, θ ∈ Ioo 0 L →
      HasDerivAt (fun θ => star (W θ)) (-(star (W θ) * C θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    have := (hθ hmem).star
    rwa [star_mul, hskew, mul_neg] at this
  intro θ hθ
  constructor
  · have hP := eq_add_integral_of_ae_hasDerivAt
      (lipschitzOnWith_mul_of_bounded hKs hK hSs hS) integrableOn_zero (by
        filter_upwards [hd, hds] with θ h1 h2 hmem
        have := (h2 hmem).mul (h1 hmem)
        convert this using 1
        noncomm_ring)
    simpa [hW0] using hP θ hθ
  · set Q : ℝ → A := fun θ => W θ * star (W θ)
    have hQc  := hW.mul hW.star
    have hQB  := fun x hx =>
      (norm_mul_le _ _).trans (mul_le_mul (hS x hx) (hSs x hx) (norm_nonneg _) hS0)
    set g : ℝ → A := fun s => C s * Q s - Q s * C s
    have hgm  :=
      (hC.restrict.mul (hQc.aestronglyMeasurable measurableSet_Icc)).sub
        ((hQc.aestronglyMeasurable measurableSet_Icc).mul hC.restrict)
    have hgB : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ 2 * M * (S * S) := fun x hx => by
      calc _ ≤ ‖C x * Q x‖ + ‖Q x * C x‖ := norm_sub_le _ _
        _ ≤ M * (S * S) + (S * S) * M :=
          add_le_add
            ((norm_mul_le _ _).trans (mul_le_mul (hM x) (hQB x hx) (norm_nonneg _) hM0))
            ((norm_mul_le _ _).trans
              (mul_le_mul (hQB x hx) (hM x) (norm_nonneg _) (mul_nonneg hS0 hS0)))
        _ = _ := by ring
    have hgi : IntegrableOn g (Icc 0 L) :=
      Integrable.of_bound hgm (2 * M * (S * S))
        ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB))
    have hQ := eq_add_integral_of_ae_hasDerivAt (lipschitzOnWith_mul_of_bounded hK hKs hS hSs)
      hgi (by
        filter_upwards [hd, hds] with θ h1 h2 hmem
        have := (h1 hmem).mul (h2 hmem)
        convert this using 1
        simp only [g, Q]
        noncomm_ring)
    set D : ℝ → A := fun θ => Q θ - 1
    have hDc : ContinuousOn D (Icc 0 L) := hQc.sub continuousOn_const
    have hDeq : ∀ θ ∈ Icc 0 L, D θ = ∫ s in (0 : ℝ)..θ, g s := fun θ hθ => by
      simp only [D, Q]; rw [hQ θ hθ, hW0, star_one, one_mul, add_sub_cancel_left]
    have hgD : ∀ s, ‖g s‖ ≤ 2 * M * ‖D s‖ := fun s => by
      have : g s = C s * D s - D s * C s := by simp only [g, D]; noncomm_ring
      rw [this]
      calc _ ≤ ‖C s * D s‖ + ‖D s * C s‖ := norm_sub_le _ _
        _ ≤ M * ‖D s‖ + ‖D s‖ * M :=
          add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _)))
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM s) (norm_nonneg _)))
        _ = _ := by ring
    have hD0 := eq_zero_of_norm_le_integral (K := 2 * M) (by positivity) hDc (fun θ hθ => by
      rw [hDeq θ hθ]
      refine (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans ?_
      have hsub : uIcc 0 θ ⊆ Icc 0 L := by
        rw [uIcc_of_le hθ.1]; exact Icc_subset_Icc le_rfl hθ.2
      refine intervalIntegral.integral_mono_on hθ.1 ?_ ?_ fun s _ => hgD s
      · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hθ.1).mpr
          (hgi.mono_set (Icc_subset_Icc le_rfl hθ.2))).norm
      · exact ContinuousOn.intervalIntegrable (continuousOn_const.mul (hDc.mono hsub).norm))
    exact sub_eq_zero.mp (hD0 θ hθ)

end PolyaNeumann

end
