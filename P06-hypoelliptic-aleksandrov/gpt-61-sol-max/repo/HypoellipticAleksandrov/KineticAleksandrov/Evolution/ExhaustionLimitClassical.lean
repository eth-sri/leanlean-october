module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeWeak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Classical recovery for smooth regularized weak solutions

Integration by parts discharges the actual smooth jets. The fundamental lemma
then recovers the pointwise equation, without adding it as a hypothesis.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

open HypoellipticAleksandrov MeasureTheory Set

variable {n : ℕ} {U : Set (EvolutionVec n)} (hU : IsOpen U)

include hU in
private theorem smooth_direction
    {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ PDE.smoothOrder u U) (v : EvolutionVec n) :
    ContDiffOn ℝ PDE.smoothOrder (fun x => fderiv ℝ u x v) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

variable {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)

include hU hB in
/-- The regularized kinetic operator of a smooth function is smooth on an open set. -/
theorem contDiffOn_regularizedOperator

    {b : PDE.VectorField n} (hb : IsSmoothDrift b) (ε : ℝ)
    {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ PDE.smoothOrder u U) :
    ContDiffOn ℝ PDE.smoothOrder (regularizedOperator B b ε u) U := (id
  (id
    (ContDiffOn.add
      (ContDiffOn.add
        (ContDiffOn.add (smooth_direction hU hu basisT)
          (ContDiffOn.sum fun i x =>
            ContDiffOn.sum fun j x =>
              ContDiffOn.mul
                (ContDiff.contDiffOn (ContDiff.comp (hB i j) (ContinuousLinearEquiv.contDiff (evolutionProdCLE n))))
                (smooth_direction hU (smooth_direction hU hu (basisV j)) (basisV i))))
        (ContDiffOn.sum fun i x =>
          ContDiffOn.mul
            (ContDiff.contDiffOn (ContDiff.comp (contDiff_pi.mp hb i) (ContinuousLinearMap.contDiff (diffusedCoord n))))
            (smooth_direction hU hu (basisZ i))))
      (ContDiffOn.mul contDiffOn_const
        (ContDiffOn.sum fun i x => smooth_direction hU (smooth_direction hU hu (basisZ i)) (basisZ i))))))

variable (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.VectorField n} (hb : IsSmoothDrift b) (ε : ℝ) {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ PDE.smoothOrder u U)

include hU hB hBs hb hu
/-- Integration against the regularized adjoint equals integration of the classical
operator for an actually smooth interior function. -/
theorem integral_regularizedAdjoint_contDiffOn

    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ PDE.smoothOrder ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * regularizedAdjoint B b ε ψ x) =
      ∫ x in U, regularizedOperator B b ε u x * ψ x := by
  let D (v : EvolutionVec n) (f : EvolutionVec n → ℝ) (x : EvolutionVec n) :=
    fderiv ℝ f x v
  have hd  :=
    (smooth_direction hU hu)
  have hdd  :=
    fun v w => smooth_direction hU (hd v) w
  have hline : ∀ v x, x ∈ U → HasLineDerivAt ℝ u (D v u x) x v := by
    intro v x hx
    exact ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      ).hasFDerivAt.hasLineDerivAt v
  have hline2 : ∀ v w x, x ∈ U →
      HasLineDerivAt ℝ (D v u) (D w (D v u) x) x w := by
    intro v w x hx
    exact (((hd v).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      ).hasFDerivAt.hasLineDerivAt w
  have key := integral_regularizedAdjoint_of_jets B b ε hB hb u (D basisT u)
    (fun i => D (basisV i) u) (fun i => D (basisZ i) u)
    (fun i j => D (basisV j) (D (basisV i) u))
    (fun i => D (basisZ i) (D (basisZ i) u))
    hu.continuousOn (hd basisT).continuousOn
    (fun i => (hd (basisV i)).continuousOn) (fun i => (hd (basisZ i)).continuousOn)
    (fun i j => (hdd (basisV i) (basisV j)).continuousOn)
    (fun i => (hdd (basisZ i) (basisZ i)).continuousOn)
    (hline basisT) (fun i => hline (basisV i)) (fun i => hline (basisZ i))
    (fun i j => hline2 (basisV i) (basisV j))
    (fun i => hline2 (basisZ i) (basisZ i)) ψ hψ hc hs
  refine key.trans (setIntegral_congr_fun hU.measurableSet fun x _ => ?_)
  congr 1
  dsimp only [D, regularizedOperator, transportedOperator]
  congr 1
  congr 1
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrFun (congrFun (hBs (timeCoord n x) (diffusedCoord n x)
    (transportedCoord n x)) i) j

/-- A smooth regularized weak solution satisfies its zero-source equation pointwise. -/
theorem regularizedOperator_eq_zero_of_smooth_weak

    (hw : IsWeakRegularizedSolution B b ε U u (fun _ => 0)) :
    ∀ x ∈ U, regularizedOperator B b ε u x = 0 := by
  have hop := (contDiffOn_regularizedOperator hU hB hb ε hu).continuousOn
  have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hop.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by


      have hEq : (∫ x in U, regularizedOperator B b ε u x * ψ x) = 0 := by
        rw [← (integral_regularizedAdjoint_contDiffOn hU hB hBs hb ε hu ψ hψ hc hs), (hw.2 ψ hψ hc hs)]
        simp
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero])] at hEq
      simpa only [smul_eq_mul, mul_comm] using hEq)


  exact fun x hx => (Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae0) hU hop continuousOn_const) hx

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
