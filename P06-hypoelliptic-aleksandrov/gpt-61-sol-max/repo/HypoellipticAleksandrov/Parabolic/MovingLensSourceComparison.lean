module

public import HypoellipticAleksandrov.Parabolic.MovingLensSourceLowerBound
public import HypoellipticAleksandrov.Parabolic.MovingLensComparison
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.DensityToPoint
import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.MovingLensSourceABP

open private HypoellipticAleksandrov.Parabolic.movingLensSignXi_nonneg from HypoellipticAleksandrov.Parabolic.MovingLensSourceABP


/-!
# Source-aware small-seed moving-lens comparison

This module subtracts the strictly signed moving-lens barrier from a supplied
inhomogeneous supersolution.  The resulting nonnegative causal boundary data
are passed to the physical-coordinate supplied-source lower bound.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped MatrixOrder Topology

variable {d : Nat} (A : CoefficientField d)



private theorem parabolicOperator_sub_of_contDiffAt
     (u v : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (z : TimeVelocity d) (hu : ContDiffAt Real 2 u z)
    (hv : ContDiffAt Real 2 v z) :
    parabolicOperator A (fun q => u q - v q) z =
      parabolicOperator A u z - parabolicOperator A v z := by
  let sharedTerm_0d5b718341 := ((fun q => u q - v q))
  let sharedTerm_c253890d50 := ((fun q => fderiv Real u q - fderiv Real v q))





  have hsecond : fderiv Real (fderiv Real sharedTerm_0d5b718341) z =
      fderiv Real (fderiv Real u) z - fderiv Real (fderiv Real v) z := by
    calc
      fderiv Real (fderiv Real sharedTerm_0d5b718341) z =
          fderiv Real sharedTerm_c253890d50 z :=
        (show fderiv Real sharedTerm_0d5b718341 =ᶠ[𝓝 z]
      sharedTerm_c253890d50 by
            filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)]
              with q huq hvq
            exact fderiv_fun_sub (huq.differentiableAt (by norm_num))
              (hvq.differentiableAt (by norm_num))).fderiv_eq
      _ = fderiv Real (fderiv Real u) z - fderiv Real (fderiv Real v) z :=
        fderiv_fun_sub ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have htime : timeDerivative sharedTerm_0d5b718341 z =
      timeDerivative u z - timeDerivative v z := by
    unfold timeDerivative
    rw [fderiv_fun_sub (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num))]
    rfl
  have hhessian : velocityHessian sharedTerm_0d5b718341 z =
      velocityHessian u z - velocityHessian v z := by
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, parabolicOperator_apply,
    htime, hhessian]
  simp only [sub_eq_add_neg, HypoellipticAleksandrov.matrixContraction_add_right,
    HypoellipticAleksandrov.matrixContraction_neg_right]
  ring




private theorem movingLensSignExponent_pos (d : Nat) (lam Lam kappa : Real) :
    0 < movingLensSignExponent d lam Lam kappa := by
  unfold movingLensSignExponent
  omega



/-- A supplied nonnegative source changes the small-seed terminal comparison
only by a structural multiple of its restricted parabolic norm. -/
theorem exists_movingLens_source_terminal_lower_bound
    (d : Nat) (hd : 0 < d) (lam Lam kappa : Real)
    (hlam : 0 < lam) (hlamLam : lam <= Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa <= 1) :
    ∃ C : Real, 0 < C ∧
      ∀ (A : CoefficientField d) (U : HypoellipticAleksandrov.Parabolic.Region d)
        (F u : HypoellipticAleksandrov.Parabolic.ScalarField d) (tau eps ell : Real) (y : PDE.Vec d),
        0 < tau -> tau <= kappa⁻¹ -> 0 < eps ->
        2 * eps ^ 2 < kappa ^ 2 ->
        0 < ell ->
        PDE.vecNormSq y <= (d : Real) * kappa ^ (-4 : Int) ->
        IsOpen U ->
        movingLensClosed (movingLensSignXi kappa) eps tau y ⊆ U ->
        IsContinuousCoefficientOn A U ->
        ContinuousOn F U ->
        ContinuousOn u (movingLensClosed (movingLensSignXi kappa) eps tau y) ->
        (∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
          ContDiffAt Real 2 u z) ->
        IsNonnegativeOn u
          (movingLensClosed (movingLensSignXi kappa) eps tau y) ->
        HasLowerEllipticityOn lam A
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        HasUpperEllipticityOn Lam A
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        IsNonnegativeOn F
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        IsParabolicSupersolutionOn A (fun z => -F z) u
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        (∀ v : PDE.Vec d, PDE.vecNormSq v < eps ^ 2 -> ell <= u (0, v)) ->
        ell * eps ^ (2 * movingLensSignExponent d lam Lam kappa) /
            kappa ^ (2 * movingLensSignExponent d lam Lam kappa) <
          u (tau, tau • y) + C * parabolicLpNormOn d F
            (movingLensClosed (movingLensSignXi kappa) eps tau y) := by
  rcases exists_movingLens_source_lower_bound d hd lam Lam kappa
    hlam hlamLam hkappa hkappa_one with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro A U F u tau eps ell y htau htau_upper heps hsmall hell hy hU hLU hAcont
    hF hucont hudiff hunonneg hlower hupper hFnonneg hsuper hseed
  let xi : Real := movingLensSignXi kappa
  let n : Nat := movingLensSignExponent d lam Lam kappa
  let psi  := movingLensBarrier xi eps n y
  let c : Real := ell * eps ^ (2 * n)
  let w  := fun z => u z - c * psi z
  have hxi : 0 <= xi := by
    dsimp only [xi]
    exact _root_.HypoellipticAleksandrov.Parabolic.movingLensSignXi_nonneg hkappa

  have hc : 0 < c := by
    dsimp only [c]
    positivity





  have hsource := hC A U F w tau eps y htau htau_upper heps hsmall hy hU hLU hAcont
    hF (hucont.sub (continuousOn_const.mul (by
            intro z hz
            have hden  :=
              movingLensDenominator_pos hxi heps hz.1
            exact (contDiffAt_movingLensBarrier hden.ne').continuousAt.continuousWithinAt))) (by
        intro z hz
        have hden  :=
          movingLensDenominator_pos hxi heps hz.1.le
        exact (hudiff z hz).sub
          (ContDiffAt.const_smul c (contDiffAt_movingLensBarrier hden.ne'))) hlower hupper hFnonneg (by
          intro z hz
          have hden  :=
            movingLensDenominator_pos hxi heps hz.1.le



          have hoperator : parabolicOperator A w z =
              parabolicOperator A u z - c * parabolicOperator A psi z := by
            dsimp only [w]
            calc
              parabolicOperator A (fun q => u q - c * psi q) z =
                  parabolicOperator A u z - parabolicOperator A (c • psi) z := (parabolicOperator_sub_of_contDiffAt A u (c • psi) z (hudiff z hz)
        (ContDiffAt.const_smul c (contDiffAt_movingLensBarrier (LT.lt.ne' hden))))
              _ = parabolicOperator A u z - c * parabolicOperator A psi z := by
                rw [parabolicOperator_const_smul]
          rw [hoperator]
          have huSuper  := hsuper z hz
          nlinarith [mul_pos hc (neg_pos.mpr (show parabolicOperator A psi z < 0 by
              dsimp only [psi, xi, n]
              exact parabolicOperator_movingLensBarrier_lt_zero_of_pointwise_loewner
                d lam Lam kappa hlam hlamLam hkappa hkappa_one A y z eps
                (hden) ((show movingLensDenominator xi eps z.1 < kappa ^ 2 by
                    dsimp only [xi]
                    exact movingLensDenominator_lt_kappa_sq hkappa hsmall hz.2.1 htau_upper))
                hy (((movingLensRadiusSq_lt_one_iff hden).2 hz.2.2)) (hlower z hz) (hupper z hz)))]) (by
        intro z hz
        rw [mem_movingLensClosed_diff_active_iff] at hz
        rcases hz with hinitial | hlateral
        · rcases hinitial with ⟨hzTime, hzTau, hzSpatial⟩
          have hden  :=
            movingLensDenominator_pos hxi heps hzTime.ge
          have hdispInitial : movingLensDisplacement y z = z.2 := by
            unfold movingLensDisplacement
            rw [hzTime, zero_smul, sub_zero]
          have hdenInitial : movingLensDenominator xi eps z.1 = eps ^ 2 := by
            unfold movingLensDenominator
            rw [hzTime, mul_zero, zero_add]
          by_cases hstrict : PDE.vecNormSq (movingLensDisplacement y z) <
              movingLensDenominator xi eps z.1
          · have hseedPoint : ell <= u z := by

              have hzEq : z = (0, z.2) := by
                apply Prod.ext
                · exact hzTime
                · rfl
              rw [hzEq]
              exact hseed z.2 (by
                  simpa only [hdispInitial, hdenInitial] using hstrict)
            have hrnonneg : 0 <= movingLensRadiusSq xi eps y z := by
              unfold movingLensRadiusSq
              exact div_nonneg (PDE.vecNormSq_nonneg _) hden.le
            have hrle  :=
              (movingLensRadiusSq_le_one_iff hden).2 hzSpatial



            have hbarrier : c * psi z <= ell := by
              calc
                c * psi z = ell * (1 - movingLensRadiusSq xi eps y z) ^ 2 := by
                  dsimp only [c, psi, movingLensBarrier]
                  rw [hdenInitial]
                  rw [show eps ^ (2 * n) = (eps ^ 2) ^ n by ring]
                  field_simp [(pow_pos (sq_pos_of_pos heps) _).ne']
                _ <= ell * 1 := mul_le_mul_of_nonneg_left (by
                    nlinarith [(mul_nonneg hrnonneg (by linarith))]) hell.le
                _ = ell := mul_one ell
            dsimp only [w]
            linarith
          · have hspatialEq  :=
              le_antisymm hzSpatial (le_of_not_gt hstrict)
            have hbarrierZero : psi z = 0 := by
              dsimp only [psi, movingLensBarrier, movingLensRadiusSq]
              rw [hspatialEq]
              field_simp [hden.ne']
              ring
            dsimp only [w]
            rw [hbarrierZero, mul_zero, sub_zero]
            exact hunonneg z ⟨hzTime.ge, hzTau, hzSpatial⟩
        · rcases hlateral with ⟨hzTime, hzTau, hspatialEq⟩

          have hbarrierZero : psi z = 0 := by
            dsimp only [psi, movingLensBarrier, movingLensRadiusSq]
            rw [hspatialEq]
            field_simp [(movingLensDenominator_pos hxi heps hzTime).ne']
            ring
          dsimp only [w]
          rw [hbarrierZero, mul_zero, sub_zero]
          exact hunonneg z ⟨hzTime, hzTau, hspatialEq.le⟩)

  have hdenTerminalPos  :=
    movingLensDenominator_pos hxi heps htau.le
  have hpsiTerminal : psi (tau, tau • y) =
      1 / (movingLensDenominator xi eps tau) ^ n := by
    dsimp only [psi, movingLensBarrier]
    have hdisp : movingLensDisplacement y (tau, tau • y) = 0 := by
      unfold movingLensDisplacement
      rw [sub_self]
    have hradius : movingLensRadiusSq xi eps y (tau, tau • y) = 0 := by
      unfold movingLensRadiusSq
      rw [hdisp]
      simp only [PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, zero_div]
    rw [hradius]
    simp only [sub_zero, one_pow]

  have hdenPow  :=
    pow_lt_pow_left₀ (by
        dsimp only [xi]
        exact movingLensDenominator_lt_kappa_sq hkappa hsmall le_rfl htau_upper) hdenTerminalPos.le (show 0 < n by
            dsimp only [n]
            exact movingLensSignExponent_pos d lam Lam kappa).ne'

  exact (show ell * eps ^ (2 * n) / kappa ^ (2 * n) <
      c / (movingLensDenominator xi eps tau) ^ n by

      calc
        ell * eps ^ (2 * n) / kappa ^ (2 * n) = c / (kappa ^ 2) ^ n := by
          ring
        _ < c / (movingLensDenominator xi eps tau) ^ n :=
          div_lt_div_of_pos_left hc (pow_pos hdenTerminalPos _) hdenPow).trans_le ((by
      have hsource' : -C * parabolicLpNormOn d F
          (movingLensClosed xi eps tau y) <= w (tau, tau • y) := by
        exact hsource
      dsimp only [w] at hsource'
      rw [hpsiTerminal] at hsource'
      have hrewrite : c * (1 / (movingLensDenominator xi eps tau) ^ n) =
          c / (movingLensDenominator xi eps tau) ^ n := by
        ring
      rw [hrewrite] at hsource'
      linarith))

end HypoellipticAleksandrov.Parabolic
