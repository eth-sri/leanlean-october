module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeWeak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Classical recovery for smooth regularized weak solutions

Integration by parts discharges the actual smooth jets. The fundamental lemma
then recovers the pointwise equation, without adding it as a hypothesis.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

open HypoellipticAleksandrov MeasureTheory Set

variable {n : ℕ} {U : Set (EvolutionVec n)}

private theorem smooth_direction  (hU : IsOpen U)
    {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (v : EvolutionVec n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ u x v) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- The regularized kinetic operator of a smooth function is smooth on an open set. -/
theorem contDiffOn_regularizedOperator  (hU : IsOpen U)
    {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    {b : PDE.Vec n → PDE.Vec n} (hb : IsSmoothDrift b) (ε : ℝ)
    {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (regularizedOperator B b ε u) U := by
  have hA : ∀ i j, ContDiff ℝ _ (fun x : EvolutionVec n =>
      B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE n).contDiff
  have hβ : ∀ i, ContDiff ℝ _ (fun x : EvolutionVec n => b (diffusedCoord n x) i) :=
    fun i => (contDiff_pi.mp hb i).comp (diffusedCoord n).contDiff
  refine (((smooth_direction hU hu basisT).add ?_).add ?_).add ?_
  · exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hA i j).contDiffOn.mul
      (smooth_direction hU (smooth_direction hU hu _) _)
  · exact ContDiffOn.sum fun i _ => (hβ i).contDiffOn.mul
      (smooth_direction hU hu _)
  · exact contDiffOn_const.mul (ContDiffOn.sum fun i _ =>
      smooth_direction hU (smooth_direction hU hu _) _)

/-- Integration against the regularized adjoint equals integration of the classical
operator for an actually smooth interior function. -/
theorem integral_regularizedAdjoint_contDiffOn 
    (hU : IsOpen U) {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.Vec n → PDE.Vec n}
    (hb : IsSmoothDrift b) (ε : ℝ) {u : EvolutionVec n → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * regularizedAdjoint B b ε ψ x) =
      ∫ x in U, regularizedOperator B b ε u x * ψ x := by
  let D (v : EvolutionVec n) (f : EvolutionVec n → ℝ) (x : EvolutionVec n) :=
    fderiv ℝ f x v
  have hd : ∀ v, ContDiffOn ℝ _ (D v u) U :=
    fun v => smooth_direction hU hu v
  have hdd : ∀ v w, ContDiffOn ℝ _ (D w _) U :=
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
  have key := integral_regularizedAdjoint_of_jets B b ε hB hb u _
    _ _
    _
    _
    hu.continuousOn (hd basisT).continuousOn
    (fun i => (hd _).continuousOn) (fun i => (hd _).continuousOn)
    (fun i j => (hdd _ _).continuousOn)
    (fun i => (hdd _ _).continuousOn)
    (hline basisT) (fun i => hline _) (fun i => hline _)
    (fun i j => hline2 _ _)
    (fun i => hline2 _ _) ψ hψ hc hs
  refine key.trans (setIntegral_congr_fun hU.measurableSet fun x _ => ?_)
  congr 1
  congr 1
  congr 1
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrFun (congrFun (hBs _ _
    _) i) j

/-- A smooth regularized weak solution satisfies its zero-source equation pointwise. -/
theorem regularizedOperator_eq_zero_of_smooth_weak 
    (hU : IsOpen U) {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.Vec n → PDE.Vec n}
    (hb : IsSmoothDrift b) (ε : ℝ) {u : EvolutionVec n → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hw : IsWeakRegularizedSolution B b ε U u (fun _ => 0)) :
    ∀ x ∈ U, regularizedOperator B b ε u x = 0 := by
  have hop := (contDiffOn_regularizedOperator hU hB hb ε hu).continuousOn
  have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hop.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
      have h1 := integral_regularizedAdjoint_contDiffOn hU hB hBs hb ε hu ψ hψ hc hs
      have h2 := hw.2 ψ hψ hc hs
      have hEq : (∫ x in U, regularizedOperator B b ε u x * ψ x) = 0 := by
        simp_all
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero])] at hEq
      simpa only [smul_eq_mul, mul_comm] using hEq)
  have hae1 : regularizedOperator B b ε u =ᵐ[volume.restrict U] fun _ => (0) :=
    (ae_restrict_iff' hU.measurableSet).2 hae0
  have heq := Measure.eqOn_open_of_ae_eq hae1 hU hop continuousOn_const
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
