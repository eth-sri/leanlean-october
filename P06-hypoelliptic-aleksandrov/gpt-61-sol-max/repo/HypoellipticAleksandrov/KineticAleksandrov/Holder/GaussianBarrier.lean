module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # The source Gaussian barrier with its explicit smooth zero extension -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Filter
open scoped Topology

variable {d : ℕ}

/-- The literal Gaussian formula, used analytically only on the definite covariance strip. -/
def gaussianFormula  (chi : ℝ → ℝ)
    (lam Lam H h L ell tminus sblock : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) : ℝ :=
  let s := P.time - tminus
  let sigma := s - sblock
  ell * chi (sigma / h) *
    (Real.exp (-Xi d lam Lam H h * sigma -
      qform lam h sigma (P.position - x s) (P.velocity - v s)) - Real.exp (-L ^ 2))

variable (lam Lam H h L ell tminus sblock : ℝ) (x v : ℝ → PDE.Vec d) (P : KineticPoint d)

/-- The source barrier, extended by zero from the positive-definite cutoff strip. -/
def gaussianBarrier   : ℝ :=
  if -(1 / 128 : ℝ) < (P.time - tminus - sblock) / h then
    gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v P
  else 0

/-- Outside the covariance strip the source cutoff kills the entire formula. -/
theorem gaussianBarrier_eq_formula   :
    gaussianBarrier lam Lam H h L ell tminus sblock x v P =
      gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v P := by
  unfold gaussianBarrier
  split_ifs with hs
  · rfl
  · unfold gaussianFormula
    dsimp only
    rw [barrierCutoff_zero (le_of_not_gt hs), mul_zero, zero_mul]

variable {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ PDE.smoothOrder x) (hv : ContDiff ℝ PDE.smoothOrder v)

include hlam hh hx hv
/-- Smoothness of the literal formula at each point of the closed definite strip. -/
theorem contDiffAt_raw_gaussianFormula   (Q : ℝ × (PDE.Vec d × PDE.Vec d))
    (hQ : -(1 / 128 : ℝ) ≤ (Q.1 - tminus - sblock) / h) :
    ContDiffAt ℝ PDE.smoothOrder
      (rawLift (gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v)) Q := by
  let sharedTerm_a2926d5a72 := (ℝ × (PDE.Vec d × PDE.Vec d))


  have hq := (contDiffAt_qform_raw hlam hh (show -(h / 128) ≤ Q.1 - tminus - sblock by

      linarith only [((le_div_iff₀ hh).mp hQ)])
    (Q.2.1 - x (Q.1 - tminus)) (Q.2.2 - v (Q.1 - tminus))).comp Q (show ContDiff ℝ PDE.smoothOrder
      (fun T : sharedTerm_a2926d5a72 =>
        (T.1 - tminus - sblock, (T.2.1 - x (T.1 - tminus),
          T.2.2 - v (T.1 - tminus)))) by
        exact ((contDiff_fst.sub contDiff_const).sub contDiff_const).prodMk
          ((contDiff_fst.comp contDiff_snd).sub
            (hx.comp (contDiff_fst.sub contDiff_const)) |>.prodMk
            ((contDiff_snd.comp contDiff_snd).sub
              (hv.comp (contDiff_fst.sub contDiff_const))))).contDiffAt
  have htime : ContDiff ℝ PDE.smoothOrder
      (fun T : sharedTerm_a2926d5a72 => T.1 - tminus - sblock) := by fun_prop

  change ContDiffAt ℝ PDE.smoothOrder (fun T : sharedTerm_a2926d5a72 =>
    ell * barrierCutoff ((T.1 - tminus - sblock) / h) *
      (Real.exp (-Xi d lam Lam H h * (T.1 - tminus - sblock) -
        qform lam h (T.1 - tminus - sblock)
          (T.2.1 - x (T.1 - tminus)) (T.2.2 - v (T.1 - tminus))) - Real.exp (-L ^ 2))) Q
  exact (contDiffAt_const.mul (contDiff_barrierCutoff.comp (htime.div_const h)).contDiffAt).mul
    (((contDiffAt_const.mul htime.contDiffAt).sub hq).exp.sub contDiffAt_const)

/-- Global smoothness follows by gluing to zero, without a global inverse smoothness claim. -/
theorem contDiff_raw_gaussianBarrier   :
    ContDiff ℝ PDE.smoothOrder
      (rawLift (gaussianBarrier lam Lam H h L ell tminus sblock x v)) := by
  rw [contDiff_iff_contDiffAt]
  intro Q
  by_cases hs : -(1 / 128 : ℝ) ≤ (Q.1 - tminus - sblock) / h
  ·
    apply (contDiffAt_raw_gaussianFormula hlam hh Lam H L ell tminus sblock hx hv Q hs).congr_of_eventuallyEq
    exact Eventually.of_forall (fun T => gaussianBarrier_eq_formula _ _ _ _ _ _ _ _ _ _ _)
  ·

    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [((show Continuous (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (T.1 - tminus - sblock) / h) by fun_prop).continuousAt.eventually (gt_mem_nhds (lt_of_not_ge hs)))] with T hT
    change gaussianBarrier lam Lam H h L ell tminus sblock x v
      ⟨T.1, T.2.1, T.2.2⟩ = 0
    unfold gaussianBarrier
    exact ite_eq_right (not_lt.mpr hT.le)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
