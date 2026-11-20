module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak

/-! # Integration by parts for twice continuously differentiable compact tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set SectionTwo Evolution Occupation
variable {d : ℕ}

/-- Full kinetic integration by parts, with all jets discharged by interior smoothness. -/
theorem integral_transportedAdjoint_contDiffOn_two {U : Set (EvolutionVec d)} (hU : IsOpen U)
    {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (ψ : EvolutionVec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * transportedAdjoint B b ψ x) =
      ∫ x in U, transportedOperator B b u x * ψ x := by
  simpa only [regularizedAdjoint, regularizedOperator, zero_mul, add_zero] using
    integral_regularizedAdjoint_contDiffOn_two hU hB hBs hb 0 hu ψ hψ hc hs

/-- The literal scalar kinetic operator of a C² function is continuous. -/
theorem continuous_transportedOperator_c2 {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {f : EvolutionVec 1 → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f) := by
  have hd (v : EvolutionVec 1) : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    contDiffOn_univ.mp
      ((hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by norm_num)).clm_apply contDiffOn_const)
  have hdd (v w : EvolutionVec 1) :
      Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) :=
    (contDiffOn_univ.mp
      (((hd v).contDiffOn.fderiv_of_isOpen isOpen_univ (by norm_num)).clm_apply
        contDiffOn_const) : ContDiff ℝ 0 _).continuous
  unfold transportedOperator
  refine ((hd basisT).continuous.add ?_).add ?_
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((evolutionCoefficient_smooth A) i j).comp
      (evolutionProdCLE 1).contDiff).continuous.mul (hdd (basisV j) (basisV i))
  · apply continuous_finsetSum
    intro i _
    exact (((contDiff_pi.mp (identityDrift_smooth 1)) i).comp
      (diffusedCoord 1).contDiff).continuous.mul (hd (basisZ i)).continuous

/-- Outside a test's closed support all terms of its actual operator vanish. -/
theorem transportedOperator_eq_zero_of_notMem_tsupport {f : EvolutionVec 1 → ℝ}
    {x : EvolutionVec 1} (hx : x ∉ tsupport f) (B : FullKineticCoefficient 1)
    (b : PDE.Vec 1 → PDE.Vec 1) : transportedOperator B b f x = 0 := by
  have h0 := fderiv_of_notMem_tsupport ℝ hx
  have hn : x ∉ tsupport (fun y => fderiv ℝ f y (basisV (0 : Fin 1))) :=
    fun h => hx (tsupport_fderiv_apply_subset ℝ (basisV 0) h)
  simp only [transportedOperator, Fin.sum_univ_one, h0, (fderiv_of_notMem_tsupport ℝ hn),
    zero_apply, mul_zero, add_zero]

/-- A C² test satisfies the weak equation for its actual kinetic operator. -/
theorem c2_isWeakTransportedSolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {U : Set (EvolutionVec 1)} (hU : IsOpen U) {u : EvolutionVec 1 → ℝ}
    (hu : ContDiffOn ℝ 2 u U) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u
      (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) u) := by
  refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hc hs
  exact integral_transportedAdjoint_contDiffOn_two hU (evolutionCoefficient_smooth A)
    (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hu ψ hψ hc hs

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
