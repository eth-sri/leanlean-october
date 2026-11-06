module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfile
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrier
import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrameOperator

/-! # Time and position transport derivatives of the smooth Gaussian profile -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Filter
open scoped Topology
open Parabolic Scaling

/- The profile time derivative on the positive block strip. -/
theorem gaussianProfile_time_deriv {d lam h s}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell sblock : ℝ)
    (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    deriv (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) s =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h - deriv (fun t => qform lam h t y V) (s - sblock)) := by
  have hstrip : -(h / 128) ≤ s - sblock := by linarith only [hs, hh]
  have hqt := hasDerivAt_qform_time hlam hh hstrip y V
  have ht := (hasDerivAt_id s).sub_const sblock
  have he := (((ht.const_mul (-Xi d lam Lam H h)).sub (hqt.comp s ht)).exp.sub_const
    (Real.exp (-L ^ 2))).const_mul ell
  have heq : (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) =ᶠ[𝓝 s]
      (fun t => ell * (Real.exp (-Xi d lam Lam H h * (t - sblock) -
        qform lam h (t - sblock) y V) - Real.exp (-L ^ 2))) := by
    have he : ∀ᶠ t in 𝓝 s, 0 < t - sblock :=
      (continuousAt_id.sub continuousAt_const).eventually (lt_mem_nhds hs)
    filter_upwards [he] with t ht
    exact gaussianProfile_of_pos lam Lam H L ell sblock hh ht y V
  rw [(he.congr_of_eventuallyEq heq).deriv, hqt.deriv]
  simp only [Pi.sub_apply, Function.comp_def, id_eq, mul_one]
  ring

/- The profile position-line derivative at a positive block time. -/
theorem gaussianProfile_position_deriv {d } (lam Lam H L ell sblock : ℝ) {h s }
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    deriv (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
      (s, (y + r • V, V))) 0 =
      -ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        deriv (fun r : ℝ => qform lam h (s - sblock) (y + r • V) V) 0 := by
  have heq : (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
      (s, (y + r • V, V))) =
      (fun r : ℝ => ell * (Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) (y + r • V) V) - Real.exp (-L ^ 2))) := by
    funext r
    exact gaussianProfile_of_pos lam Lam H L ell sblock hh hs _ _
  rw [heq]
  have hq := hasDerivAt_qform_transport lam hh (s - sblock) y V
  have he := (((hasDerivAt_const 0 (-Xi d lam Lam H h * (s - sblock))).sub hq).exp.sub_const
    (Real.exp (-L ^ 2))).const_mul ell
  simp only [Pi.sub_apply] at he
  rw [he.deriv, hq.deriv]
  simp only [zero_smul, add_zero, zero_sub]
  ring

/- Transport cancellation gives the exact scalar Gaussian contribution to the operator. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
