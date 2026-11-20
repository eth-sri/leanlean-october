module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import Mathlib

/-! # Coordinate slices in dimension one -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology ContDiff

variable (H : XV 1 → ℝ) (q : XV 1) (hH : DifferentiableAt ℝ H q) (x : ℝ) (v : ℝ)

include q x in
/-- The one-dimensional position slice through a native point. -/
def scalarPositionSlice : XV 1 := (fun _ => x, q.2)

include q v in
/-- The one-dimensional velocity slice through a native point. -/
def scalarVelocitySlice : XV 1 := (q.1, fun _ => v)

/-- The position slice passes through the native point. -/
theorem scalarPositionSlice_at : scalarPositionSlice q (q.1 0) = q := by
  apply Prod.ext
  · funext i
    exact congrArg q.1 (Subsingleton.elim 0 i)
  · rfl

/-- The velocity slice passes through the native point. -/
theorem scalarVelocitySlice_at : scalarVelocitySlice q (q.2 0) = q := by
  apply Prod.ext
  · rfl
  · funext i
    exact congrArg q.2 (Subsingleton.elim 0 i)

/-- The slice tangent is the literal native position basis vector. -/
theorem scalarPositionSlice_hasDerivAt :
    HasDerivAt (scalarPositionSlice q) (Pi.single 0 1, 0) x := by
  have he : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
    grind
  rw [← he]
  exact (hasDerivAt_pi.mpr (fun _ => hasDerivAt_id x)).prodMk (hasDerivAt_const x q.2)

/-- The slice tangent is the literal native velocity basis vector. -/
theorem scalarVelocitySlice_hasDerivAt :
    HasDerivAt (scalarVelocitySlice q) (0, Pi.single 0 1) v := by
  have he : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
    grind
  rw [← he]
  exact (hasDerivAt_const v q.1).prodMk (hasDerivAt_pi.mpr (fun _ => hasDerivAt_id v))

include hH in
/-- Full-product position derivatives agree with their literal scalar slices. -/
theorem dx_eq_scalar_slice :
    dx H q 0 = deriv (fun x => H (scalarPositionSlice q x)) (q.1 0) := by
  have hh := hH.hasFDerivAt
  rw [← scalarPositionSlice_at q] at hh
  have hd := hh.comp_hasDerivAt (q.1 0) (scalarPositionSlice_hasDerivAt q (q.1 0))
  simpa only [dx, scalarPositionSlice_at, Function.comp_def] using hd.deriv.symm

include hH in
/-- Full-product velocity derivatives agree with their literal scalar slices. -/
theorem dv_eq_scalar_slice :
    dv H q 0 = deriv (fun v => H (scalarVelocitySlice q v)) (q.2 0) := by
  have hh := hH.hasFDerivAt
  rw [← scalarVelocitySlice_at q] at hh
  have hd := hh.comp_hasDerivAt (q.2 0) (scalarVelocitySlice_hasDerivAt q (q.2 0))
  simpa only [dv, scalarVelocitySlice_at, Function.comp_def] using hd.deriv.symm

/-- The second native velocity selector agrees with the literal second scalar derivative. -/
theorem dvv_eq_scalar_slice
    (hH : ContDiffAt ℝ 2 H q) :
    dvv H q 0 0 = deriv (deriv (fun v => H (scalarVelocitySlice q v))) (q.2 0) := by
  have hD : DifferentiableAt ℝ (fun z => dv H z 0) q := by
    exact ((hH.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hd := dv_eq_scalar_slice (fun z => dv H z 0) q hD
  have hs : Continuous (scalarVelocitySlice q) := by
    unfold scalarVelocitySlice
    fun_prop
  have he : (fun v => dv H (scalarVelocitySlice q v) 0) =ᶠ[𝓝 (q.2 0)]
      deriv (fun v => H (scalarVelocitySlice q v)) := by
    have ht : Tendsto (scalarVelocitySlice q) (𝓝 (q.2 0)) (𝓝 q) := by
      simpa only [scalarVelocitySlice_at] using hs.continuousAt.tendsto (x := q.2 0)
    have hh := ht.eventually (hH.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞))
    filter_upwards [hh] with v hv
    have ht := dv_eq_scalar_slice H (scalarVelocitySlice q v)
      (hv.differentiableAt (by norm_num))
    simpa only [scalarVelocitySlice, Prod.snd, Prod.fst] using ht
  exact hd.trans he.deriv_eq

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
