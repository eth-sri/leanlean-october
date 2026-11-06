module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak

/-! # Integration against the full kinetic adjoint for smooth interior functions -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution

variable {d : ℕ}

variable {U : Set (EvolutionVec d)}

/-- Interior smoothness gives smooth directional derivatives on an open set. -/
theorem contDiffOn_duhamel_direction  (hU : IsOpen U)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (v : EvolutionVec d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ u x v) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- Full kinetic integration by parts, with all jets discharged by interior smoothness. -/
theorem integral_transportedAdjoint_contDiffOn  (hU : IsOpen U)
    {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (ψ : EvolutionVec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * transportedAdjoint B b ψ x) =
      ∫ x in U, transportedOperator B b u x * ψ x := by
  let D (v : EvolutionVec d) (f : EvolutionVec d → ℝ) (x : EvolutionVec d) :=
    fderiv ℝ f x v
  have hd : ∀ v, ContDiffOn ℝ _ (D v u) U :=
    fun v => contDiffOn_duhamel_direction hU hu v
  have hdd : ∀ v w, ContDiffOn ℝ _ (D w _) U :=
    fun v w => contDiffOn_duhamel_direction hU (hd v) w
  have hline : ∀ v x, x ∈ U → HasLineDerivAt ℝ u (D v u x) x v := by
    intro v x hx
    exact ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      ).hasFDerivAt.hasLineDerivAt v
  have hline2 : ∀ v w x, x ∈ U →
      HasLineDerivAt ℝ (D v u) (D w (D v u) x) x w := by
    intro v w x hx
    exact (((hd v).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      ).hasFDerivAt.hasLineDerivAt w
  have key := integral_regularizedAdjoint_of_jets B b 0 hB hb u _
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
  simp only [regularizedAdjoint, zero_mul, add_zero] at key
  refine key.trans (setIntegral_congr_fun hU.measurableSet fun x _ => ?_)
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

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
