module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Regularize
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib

/-! # Control of the stationary error on the rescaled core

After dilating back to the unit ball both terms of the operator have the same
factor. No homogeneity or continuity of the coefficient field is needed.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Real Filter MeasureTheory Set
open scoped Topology ContDiff MatrixOrder

variable {d : ℕ} {F : XV d → ℝ}

private theorem deriv_pullback (c s : ℝ) (hf : Differentiable ℝ F) (q w : XV d) :
    fderiv ℝ (fun z => c * F (dilate s z)) q w = c * fderiv ℝ F (dilate s q) (dilate s w) := by
  have he := ((hf _).hasFDerivAt.comp q (hasFDerivAt_dilate s q) |>.const_mul c).fderiv
  simp only [Function.comp_def] at he; rw [he]; rfl

private theorem dx_pullback (c s : ℝ) (hf : Differentiable ℝ F) (q : XV d) (i : Fin d) :
    dx (fun z => c * F (dilate s z)) q i = (c * s^3) * dx F (dilate s q) i := by
  have e : dilate s ((Pi.single i 1,0) : XV d) = s^3 • (Pi.single i 1,0) := by simp [dilate,Prod.smul_mk]
  simp only [dx,deriv_pullback _ _ hf,e,map_smul,smul_eq_mul,mul_assoc]

private theorem dv_pullback (c s : ℝ) (hf : Differentiable ℝ F) (q : XV d) (i : Fin d) :
    dv (fun z => c * F (dilate s z)) q i = (c * s) * dv F (dilate s q) i := by
  have e : dilate s ((0,Pi.single i 1) : XV d) = s • (0,Pi.single i 1) := by simp [dilate,Prod.smul_mk]
  simp only [dv,deriv_pullback _ _ hf,e,map_smul,smul_eq_mul,mul_assoc]

private theorem smooth_dv (hf : ContDiff ℝ ∞ F) (k : Fin d) : ContDiff ℝ ∞ (fun q => dv F q k) :=
  hf.fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const

private theorem stat_pullback (c s : ℝ) (hf : ContDiff ℝ ∞ F) (B : PDE.Mat d) (q : XV d) :
    statOp (fun _ => B) (fun z => c * F (dilate s z)) q =
      c * s^2 * statOp (fun _ => B) F (dilate s q) := by
  have h := hf.differentiable (by simp)
  have hh (i k : Fin d) : dvv (fun z => c * F (dilate s z)) q i k =
      (c*s*s) * dvv F (dilate s q) i k := by
    change dv (fun z => dv (fun z => c * F (dilate s z)) z k) q i = _
    simp_rw [dv_pullback _ _ h]; exact dv_pullback _ _ ((smooth_dv hf k).differentiable (by simp)) _ _
  simp only [statOp, PDE.vecDot, matrixContraction, dx_pullback _ _ h, hh, mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; change _ = _ * (s * q.2 i * _); ring
  · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intros; ring

private theorem stat_congr {F G : XV d → ℝ} {q} (e : F =ᶠ[𝓝 q] G) (A : XV d → PDE.Mat d) :
    statOp A F q = statOp A G q := by
  have H k : (fun z => dv F z k) =ᶠ[𝓝 q] fun z => dv G z k :=
    e.eventuallyEq_nhds.mono (fun _ h => congrArg (fun L : XV d →L[ℝ] ℝ => L (0,Pi.single k 1)) h.fderiv_eq)
  unfold statOp; rw [show dx F q = dx G q by funext i; simp [dx,e.fderiv_eq],
    show dvv F q = dvv G q by ext i k; simp [dvv,(H k).fderiv_eq]]

namespace ClassicalProfile
variable {α : ℝ} (m : ClassicalProfile d α)

/-- A bounded source of height `O(r^(α−2))`, supported on the gauge ball of radius `r`. -/
theorem core_error : ∃ K : ℝ, 0 ≤ K ∧ ∀ r, 0 < r → ∀ᵐ q ∂volume,
    -statOp m.A (m.regular r) q ≤ {q | rho q ≤ r}.indicator (fun _ => K * r^(α-2)) q := by
  let F := m.core
  let g (q : XV d) := |PDE.vecDot q.2 (dx F q)| + ∑ i, ∑ k, m.Lam * |dvv F q i k|
  have hF := m.core_smooth
  have hx (i : Fin d) : Continuous (fun q => dx F q i) :=
    (hF.fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const).continuous
  have hh (i k : Fin d) : Continuous (fun q => dvv F q i k) :=
    ((smooth_dv hF k).fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const).continuous
  have hg : Continuous g := by unfold g PDE.vecDot; fun_prop (disch := first | apply hx | apply hh)
  obtain ⟨M,hM⟩ := (isCompact_rho_sublevel d 1).bddAbove_image hg.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun r hr => ?_⟩
  filter_upwards [m.super] with q hq
  by_cases hin : rho q ≤ r
  · rw [indicator_of_mem (s := {q : XV d | rho q ≤ r}) hin]
    let z := dilate r⁻¹ q
    have hz : rho z ≤ 1 := by rwa [rho_dilate _ (inv_pos.mpr hr), inv_mul_eq_div, div_le_one hr]
    have hb (i k : Fin d) := abs_apply_le_of_loewner m.hlam (m.elliptic q).1 (m.elliptic q).2 i k
    have he : -statOp (fun _ => m.A q) F z ≤ g z := by
      unfold statOp g; rw [neg_sub, sub_eq_neg_add]
      apply add_le_add (neg_le_abs _)
      apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro k _
      exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hb i k) (abs_nonneg _)))
    have hs : r^α * r⁻¹ ^ 2 = r^(α-2) := by rw [rpow_sub hr, rpow_two, inv_pow, div_eq_mul_inv]
    change -statOp (fun _ => m.A q) (fun z => r^α * F (dilate r⁻¹ z)) q ≤ _
    rw [stat_pullback _ _ hF,hs,mul_comm (max M 0),← mul_neg]
    exact mul_le_mul_of_nonneg_left (he.trans ((hM ⟨_,hz,rfl⟩).trans (le_max_left _ _))) (rpow_nonneg hr.le _)
  · rw [indicator_of_notMem (s := {q : XV d | rho q ≤ r}) hin, stat_congr (A := m.A) (F := m.regular r) (G := m.H)
        (((continuous_rho d).continuousAt.eventually_const_lt (lt_of_not_ge hin)).mono (fun _ h => m.regular_eq hr h.le))]
    exact neg_nonpos.mpr hq

end ClassicalProfile
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
