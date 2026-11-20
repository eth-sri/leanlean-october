module

public import RequestProject.IntervalFTC
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.CStarAlgebra.Basic
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

/-- A product of bounded Lipschitz functions is Lipschitz. -/
private theorem lipschitzOnWith_mul_of_bounded {A : Type*} [NormedRing A] {f g : ℝ → A}
    {s : Set ℝ} {Kf Kg : NNReal} {B : ℝ} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) (hfB : ∀ x ∈ s, ‖f x‖ ≤ B) (hgB : ∀ x ∈ s, ‖g x‖ ≤ B) :
    LipschitzOnWith (Kf * B.toNNReal + B.toNNReal * Kg) (fun x => f x * g x) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hB := (norm_nonneg _).trans (hfB x hx)
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
        all_goals tauto
    _ = _ := by ring

/-- On a compact set, products of Lipschitz functions are Lipschitz. -/
theorem exists_lipschitzOnWith_mul {A : Type*} [NormedRing A] {f g : ℝ → A}
    {s : Set ℝ} (hs : IsCompact s) {Kf Kg : NNReal} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) : ∃ K, LipschitzOnWith K (fun x => f x * g x) s := by
  obtain ⟨Bf, hBf⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Bg, hBg⟩ := hs.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨_, lipschitzOnWith_mul_of_bounded hf hg
    (fun x hx => (hBf x hx).trans (le_max_left ..))
    (fun x hx => (hBg x hx).trans (le_max_right ..))⟩

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}

/-- A solution of the Volterra equation has a.e. derivative `C W` in `(0, L)`. -/
theorem volterra_ae_hasDerivAt (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt W (C θ * W θ) θ := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun θ hθ =>
      absurd (hθ.1.trans hθ.2) (not_lt.mpr hL.le)
  have hi := intervalIntegrable_mul_of_continuousOn hC hM hW (θ := L) ⟨hL, le_rfl⟩
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach hL hi] with t ht hm
  refine ((ht hm).const_add (1 : A)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x hx
  grind

omit [CompleteSpace A] in
/-- A solution of the Volterra equation is Lipschitz on `[0, L]`. -/
theorem volterra_lipschitzOn (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∃ K, LipschitzOnWith K W (Icc 0 L) := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hM0 := (norm_nonneg _).trans (hM 0)
  refine ⟨(M * max S 0).toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hM0 (le_max_right _ _)), eW x hx, eW y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_mul_of_continuousOn hC hM hW hx)
      (intervalIntegrable_mul_of_continuousOn hC hM hW hy)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have : t ∈ Icc 0 L := by
    have := uIoc_subset_uIcc ht
    rw [mem_uIcc] at this
    rcases this with h | h
    grind
    grind
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hM t) ((hS t this).trans (le_max_left _ _)) (norm_nonneg _) hM0)

variable [StarRing A] [StarModule ℝ A] [NormedStarGroup A]

theorem volterra_ae_hasDerivAt_star (hC : AEStronglyMeasurable C volume)
    (hM : ∀ s, ‖C s‖ ≤ M) (hskew : ∀ s, star (C s) = -C s)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt (fun θ => star (W θ)) (-(star (W θ) * C θ)) θ := by
  filter_upwards [volterra_ae_hasDerivAt hC hM hW eW] with θ hθ hmem
  simpa [star_mul, hskew] using (hθ hmem).star

/-- Unitarity for skew-adjoint linear Volterra equations. -/
theorem volterra_unitary (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hskew : ∀ s, star (C s) = -C s) (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ θ ∈ Icc 0 L, star (W θ) * W θ = 1 ∧ W θ * star (W θ) = 1 := by
  rcases lt_or_ge L 0 with hL | hL
  · intro θ hθ; simp_all
  have hW0 : W 0 = 1 := by simp_all
  obtain ⟨K, hK⟩ := volterra_lipschitzOn hC hM hW eW
  obtain ⟨_, hKs⟩ := exists_lipschitzOnWith_mul isCompact_Icc
    (star_isometry.lipschitz.comp_lipschitzOnWith hK) hK
  have hleft : ∀ θ ∈ Icc 0 L, star (W θ) * W θ = 1 := by
    have hP := eq_add_integral_of_ae_hasDerivAt (g := fun _ => (0 : A)) hKs integrableOn_zero (by
      have hd := volterra_ae_hasDerivAt hC hM hW eW
      have hds := volterra_ae_hasDerivAt_star hC hM hskew hW eW
      filter_upwards [hd, hds] with θ h1 h2 hmem
      convert (h2 hmem).mul (h1 hmem) using 1 <;> first | rfl | noncomm_ring)
    intro θ hθ
    simpa [hW0] using hP θ hθ
  -- Among left-unitary elements, invertibility is both open and closed.
  let X := Icc (0 : ℝ) L
  letI : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let w : X → A := fun x => W x
  have hw := continuousOn_iff_continuous_restrict.mp hW
  have hr (x : X) : IsUnit (w x) ↔ w x * star (w x) = 1 := by
    constructor
    · rintro hu
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      rwa [left_inv_eq_right_inv (hleft x x.2) hy]
    · exact fun h => ⟨⟨w x, star (w x), h, hleft x x.2⟩, rfl⟩
  let T := {x | IsUnit (w x)}
  have hTc : IsClosed T := by
    simp  [T, hr]
    exact isClosed_eq (hw.mul hw.star) continuous_const
  have hTo := Units.isOpen.preimage hw
  have h0 : (⟨0, le_rfl, hL⟩ : X) ∈ T := by simpa [T, w, hW0]
  have hT := IsClopen.eq_univ ⟨hTc, hTo⟩ ⟨_, h0⟩
  exact fun θ hθ => ⟨hleft θ hθ, (hr ⟨θ, hθ⟩).mp (show (⟨θ, hθ⟩ : X) ∈ T by simp [hT])⟩

end PolyaNeumann

end
