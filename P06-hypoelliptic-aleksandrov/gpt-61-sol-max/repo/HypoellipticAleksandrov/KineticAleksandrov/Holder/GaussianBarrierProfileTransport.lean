module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfile
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! # Time and position transport derivatives of the smooth Gaussian profile -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder




variable {d : ℕ}

/-- The profile time derivative on the positive block strip. -/
theorem gaussianProfile_time_deriv  {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell sblock : ℝ)
    (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    deriv (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) s =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h - deriv (fun t => qform lam h t y V) (s - sblock)) := by

  have hqt := hasDerivAt_qform_time hlam hh (show -(h / 128) ≤ s - sblock by linarith only [hs, hh]) y V
  have ht := (hasDerivAt_id s).sub_const sblock

  have he := (((ht.const_mul (-Xi d lam Lam H h)).sub (hqt.comp s ht)).exp.sub_const
    (Real.exp (-L ^ 2))).const_mul ell


  rw [(he.congr_of_eventuallyEq (gaussianProfile_time_eventuallyEq lam Lam H L ell sblock hh hs y V)).deriv, hqt.deriv]
  simp only [Pi.sub_apply, Function.comp_def, id_eq, mul_one]
  ring

/-- The profile position-line derivative at a positive block time. -/
theorem gaussianProfile_position_deriv  (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    deriv (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
      (s, (y + r • V, V))) 0 =
      -ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        deriv (fun r : ℝ => qform lam h (s - sblock) (y + r • V) V) 0 := by
  let sharedTerm_735d21c96f := ((-Xi d lam Lam H h * (s - sblock)))
  have heq : (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
      (s, (y + r • V, V))) =
      (fun r : ℝ => ell * (Real.exp (sharedTerm_735d21c96f -
        qform lam h (s - sblock) (y + r • V) V) - Real.exp (-L ^ 2))) := by
    funext r
    exact gaussianProfile_of_pos lam Lam H L ell sblock hh hs _ _
  rw [heq]
  have hq := hasDerivAt_qform_transport lam hh (s - sblock) y V
  have he := (((hasDerivAt_const 0 sharedTerm_735d21c96f).sub hq).exp.sub_const
    (Real.exp (-L ^ 2))).const_mul ell
  simp only [Pi.sub_apply] at he
  rw [he.deriv, hq.deriv]
  simp only [zero_smul, add_zero, zero_sub]
  ring

/-- Transport cancellation gives the exact scalar Gaussian contribution to the operator. -/
theorem gaussianProfile_transport  {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell sblock : ℝ)
    (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    deriv (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) s +
      deriv (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
        (s, (y + r • V, V))) 0 =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h + lam * PDE.vecNormSq (pform lam h (s - sblock) y V)) := by
  rw [gaussianProfile_time_deriv hlam hh Lam H L ell sblock hs,
    gaussianProfile_position_deriv lam Lam H L ell sblock hh hs]


  calc
    _ = ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h - (deriv (fun t => qform lam h t y V) (s - sblock) +
          deriv (fun r : ℝ => qform lam h (s - sblock) (y + r • V) V) 0)) := by ring
    _ = _ := by rw [(quadratic_transport_identity lam h (s - sblock) hlam hh (by linarith only [hs, hh]) y V)]; ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
