module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.ProjIcc
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveMollification
import PDEFoundation.Ambient.HilbertVec
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory


/-- Position and velocity compatibility with Euclidean acceleration bound on a closed interval. -/
def IsSkeleton {d : ℕ} (x v : ℝ → PDE.Vec d) (H a b : ℝ) : Prop :=
  ContinuousOn v (Icc a b) ∧
  (∀ s ∈ Icc a b, HasDerivWithinAt x (v s) (Icc a b) s) ∧
  (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)

/-- A closed position–velocity corridor around a compatible path. -/
def corridor {d : ℕ} (tminus a b kx kv : ℝ) (x v : ℝ → PDE.Vec d) :
    Set (KineticPoint d) :=
  {P | P.time - tminus ∈ Icc a b ∧
    PDE.vecEuclideanNorm (P.position - x (P.time - tminus)) ≤ kx ∧
    PDE.vecEuclideanNorm (P.velocity - v (P.time - tminus)) ≤ kv}

/-- A skeleton's position is continuous on its defining interval. -/
theorem IsSkeleton.continuousOn_position {d : ℕ} {x v : ℝ → PDE.Vec d}
    {H a b : ℝ} (hx : IsSkeleton x v H a b) : ContinuousOn x (Icc a b) :=
  fun s hs => (hx.2.1 s hs).continuousWithinAt

/-- Endpoint-constant extension of the velocity of a skeleton. -/
noncomputable def extendVelocity {d : ℕ} (v : ℝ → PDE.Vec d) (a b : ℝ) (hab : a ≤ b) :
    ℝ → PDE.Vec d := fun s => v (projIcc a b hab s)

/-- The extension agrees with the original velocity on the closed interval. -/
theorem extendVelocity_eq {d : ℕ} (v : ℝ → PDE.Vec d) {a b : ℝ}
    (hab : a ≤ b) {s : ℝ} (hs : s ∈ Icc a b) :
    extendVelocity v a b hab s = v s := by
  simp only [extendVelocity, projIcc_of_mem hab hs]

/-- Extending velocity by endpoint constants preserves continuity. -/
theorem continuous_extendVelocity {d : ℕ} {v : ℝ → PDE.Vec d} {a b : ℝ}
    (hab : a ≤ b) (hv : ContinuousOn v (Icc a b)) :
    Continuous (extendVelocity v a b hab) :=
  hv.domRestrict.comp continuous_projIcc

/-- Extending velocity by endpoint constants preserves the Euclidean Lipschitz constant. -/
theorem extendVelocity_lipschitz {d : ℕ} {x v : ℝ → PDE.Vec d} {H a b : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H) (hx : IsSkeleton x v H a b) (s t : ℝ) :
    PDE.vecEuclideanNorm
      (extendVelocity v a b hab s - extendVelocity v a b hab t) ≤ H * |s - t| := by
  have hdist := (LipschitzWith.projIcc hab).dist_le_mul s t
  have hproj : |(projIcc a b hab s : ℝ) - (projIcc a b hab t : ℝ)| ≤ |s - t| := by
    simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using hdist
  exact (hx.2.2 _ (projIcc a b hab s).property _ (projIcc a b hab t).property).trans
    (mul_le_mul_of_nonneg_left hproj hH)



/-- Euclidean interval integral estimate, transported through the existing Hilbert carrier. -/
theorem vecEuclideanNorm_intervalIntegral_le {d : ℕ} {f : ℝ → PDE.Vec d}
    {a b C : ℝ} (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ t ∈ uIoc a b, PDE.vecEuclideanNorm (f t) ≤ C) :
    PDE.vecEuclideanNorm (∫ t in a..b, f t) ≤ C * |b - a| := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he := e.toContinuousLinearMap.intervalIntegral_comp_comm hf
  rw [PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  change ‖e (∫ t in a..b, f t)‖ ≤ C * |b - a|
  change (∫ t in a..b, e (f t)) = e (∫ t in a..b, f t) at he
  rw [← he]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
    change ‖(f t).toHilbertVec‖ ≤ C
    rw [← PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
    exact hbound t ht

/-- The position of a skeleton is the integral of its compatible velocity. -/
theorem IsSkeleton.position_eq_integral {d : ℕ} {x v : ℝ → PDE.Vec d}
    {H a b : ℝ} (hx : IsSkeleton x v H a b) {s : ℝ} (hs : s ∈ Icc a b) :
    x s = x a + ∫ t in a..s, v t := by
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
  have hint : IntervalIntegrable v volume a s := (hx.1.mono hsub).intervalIntegrable_of_Icc hs.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
    (hx.continuousOn_position.mono hsub) (fun t ht =>
      (hx.2.1 t (hsub ⟨ht.1.le, ht.2.le⟩)).hasDerivAt
        (Icc_mem_nhds ht.1 (ht.2.trans_le hs.2))) hint
  rw [hftc]
  abel

/-- Integrating the endpoint-constant velocity gives the tangent extension of position. -/
def extendPosition {d : ℕ} (x v : ℝ → PDE.Vec d) (a b : ℝ) (hab : a ≤ b) :
    ℝ → PDE.Vec d := fun s => x a + ∫ t in a..s, extendVelocity v a b hab t

/-- The tangent extension agrees with the original position throughout its interval. -/
theorem extendPosition_eq {d : ℕ} {x v : ℝ → PDE.Vec d} {H a b : ℝ}
    (hab : a ≤ b) (hx : IsSkeleton x v H a b) {s : ℝ} (hs : s ∈ Icc a b) :
    extendPosition x v a b hab s = x s := by
  rw [hx.position_eq_integral hs]
  unfold extendPosition
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact extendVelocity_eq v hab
    ⟨(mem_Icc.mp ((uIcc_of_le hs.1) ▸ ht)).1,
      (mem_Icc.mp ((uIcc_of_le hs.1) ▸ ht)).2.trans hs.2⟩

/-- The tangent extension is compatible with the endpoint-constant velocity globally. -/
theorem hasDerivAt_extendPosition {d : ℕ} {x v : ℝ → PDE.Vec d} {H a b : ℝ}
    (hab : a ≤ b) (hx : IsSkeleton x v H a b) (s : ℝ) :
    HasDerivAt (extendPosition x v a b hab) (extendVelocity v a b hab s) s := by
  have hc := continuous_extendVelocity hab hx.1
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (x a)

/-- Before the initial time, the extension is exactly the initial tangent line. -/
theorem extendPosition_left {d : ℕ} (x v : ℝ → PDE.Vec d) {a b s : ℝ}
    (hab : a ≤ b) (hs : s ≤ a) :
    extendPosition x v a b hab s = x a + (s - a) • v a := by
  unfold extendPosition
  congr 1
  calc
    _ = ∫ _ in a..s, v a := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_comm, uIcc_of_le hs] at ht
      simp only [extendVelocity, projIcc_of_le_left hab ht.2]
    _ = _ := intervalIntegral.integral_const _

/-- The compatible tangent extension retains the original acceleration bound on any interval. -/
theorem extendPosition_isSkeleton {d : ℕ} {x v : ℝ → PDE.Vec d} {H a b : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H) (hx : IsSkeleton x v H a b) (c e : ℝ) :
    IsSkeleton (extendPosition x v a b hab) (extendVelocity v a b hab) H c e :=
  ⟨(continuous_extendVelocity hab hx.1).continuousOn,
    fun s _ => (hasDerivAt_extendPosition hab hx s).hasDerivWithinAt,
    fun s _ t _ => extendVelocity_lipschitz hab hH hx s t⟩

/-- Smooth approximation preserves the acceleration bound and position–velocity compatibility. -/
theorem smooth_skeleton_approx {d : ℕ} (x v : ℝ → PDE.Vec d)
    (H a b : ℝ) (hab : a < b) (hH : 0 ≤ H)
    (hx : IsSkeleton x v H a b) (eps : ℝ) (heps : 0 < eps) :
    ∃ y w : ℝ → PDE.Vec d,
      ContDiff ℝ (⊤ : ℕ∞) y ∧ ContDiff ℝ (⊤ : ℕ∞) w ∧
      (∀ s, HasDerivAt y (w s) s) ∧
      (∀ s t, PDE.vecEuclideanNorm (w s - w t) ≤ H * |s - t|) ∧
      (∀ s ∈ Icc a b, PDE.vecEuclideanNorm (y s - x s) < eps ∧
        PDE.vecEuclideanNorm (w s - v s) < eps) := by
  let delta := eps / (2 * (b - a + 1))
  have hden : 0 < 2 * (b - a + 1) := by linarith
  have hd : 0 < delta := div_pos heps hden
  obtain ⟨w, hw, hwLip, hwclose⟩ := exists_smooth_lipschitz_approx
    (continuous_extendVelocity hab.le hx.1) hH
    (extendVelocity_lipschitz hab.le hH hx) hd
  let y : ℝ → PDE.Vec d := fun s => x a + ∫ t in a..s, w t
  have hy : ∀ s, HasDerivAt y (w s) s := by
    intro s
    exact (intervalIntegral.integral_hasDerivAt_right
      (hw.continuous.intervalIntegrable a s)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hw.continuous.continuousAt).const_add (x a)
  have hyderiv : deriv y = w := funext fun s => (hy s).deriv
  have hysmooth : ContDiff ℝ (⊤ : ℕ∞) y := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun s => (hy s).differentiableAt, hyderiv.symm ▸ hw⟩
  refine ⟨y, w, hysmooth, hw, hy, hwLip, ?_⟩
  intro s hs
  have hvclose : ∀ t ∈ Icc a b, PDE.vecEuclideanNorm (w t - v t) ≤ delta := by
    intro t ht
    simpa only [extendVelocity_eq v hab.le ht] using hwclose t
  have hdelta : delta < eps := by
    dsimp [delta]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hposclose : PDE.vecEuclideanNorm (y s - x s) ≤ delta * (s - a) := by
    have hiv : IntervalIntegrable v volume a s :=
      (hx.1.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
    have heq : y s - x s = ∫ t in a..s, w t - v t := by
      rw [hx.position_eq_integral hs]
      dsimp [y]
      rw [intervalIntegral.integral_sub (hw.continuous.intervalIntegrable a s) hiv]
      abel
    rw [heq]
    have hi := (hw.continuous.intervalIntegrable a s).sub hiv
    have hle := vecEuclideanNorm_intervalIntegral_le hi (fun t ht =>
      hvclose t ⟨(mem_Ioc.mp ((uIoc_of_le hs.1) ▸ ht)).1.le,
        (mem_Ioc.mp ((uIoc_of_le hs.1) ▸ ht)).2.trans hs.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using hle
  refine ⟨hposclose.trans_lt ?_, (hvclose s hs).trans_lt hdelta⟩
  have hdeq : delta * (2 * (b - a + 1)) = eps := by
    dsimp [delta]
    exact div_mul_cancel₀ eps hden.ne'
  have hsb := hs.2
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder

