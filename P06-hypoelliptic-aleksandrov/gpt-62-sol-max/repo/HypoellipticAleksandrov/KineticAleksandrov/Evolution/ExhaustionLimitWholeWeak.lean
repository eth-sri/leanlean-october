module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Weak passage for the actual whole-space ball exhaustion -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- The actual expanding-ball limit satisfies the regularized weak equation on
strict bounded whole-space cylinders. No weak equation or limit estimate is assumed. -/
theorem weakRegularized_wholeSpace_ball_limit :
    IsKineticWeakRegularizedSolution B b ε (wholeSpaceInnerCylinder α τ S0)
      (fun p => limUnder atTop (fun j => v j p)) (fun _ => 0) := by
  let U := wholeSpaceInnerCylinder (n := n) α τ S0
  have hU : IsOpen U := isOpen_wholeSpaceInnerCylinder α τ S0
  let V := evolutionHomeomorph n ⁻¹' U
  have hV : IsOpen V := hU.preimage (evolutionHomeomorph n).continuous
  have ht := (tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε.le hε1 hC F hFC r hrlim v hv).1
  refine weakRegularized_of_tendstoUniformlyOn hBs hbs hU
    (wholeSpaceInnerCylinder_subset_closed α τ S0)
    (isCompact_movingClosedSlab_inter continuous_const α τ S0) ht
    (eventually_continuousOn_abs_le_wholeSpace hlam hB hb hε.le hε1 hC F hFC r hrlim v hv) ?_
  filter_upwards [hrlim.eventually (eventually_gt_atTop |S0|)] with j hj
  have hball (p : KineticPoint n) (hp : p ∈ U) :
      p.position ∈ movingDomain (PDE.euclideanBall 0 (r j)) (fun _ => 0) p.time :=
    mem_movingBall_of_radialSq_le (abs_nonneg S0) hj
      (by simpa only [sq_abs] using (show radialSq p < S0 ^ 2 from hp.2.2).le)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (v j ∘ evolutionHomeomorph n) V :=
    (hv j).2.2.1.comp (evolutionProdCLE n).contDiff.contDiffOn
      (fun x hx => ⟨hx.2.1, hball _ hx⟩)
  refine ⟨U, subset_rfl, (isWeakRegularizedSolution_comp_iff B b ε U _ 0).mp ?_⟩
  refine ⟨hsm.continuousOn.locallyIntegrableOn hV.measurableSet, fun ψ hψ hc hs => ?_⟩
  rw [integral_regularizedAdjoint_contDiffOn hV hBs hBsym hbs ε hsm ψ hψ hc hs]
  refine setIntegral_congr_fun hV.measurableSet fun x hx => ?_
  have hc2 : ContDiffAt ℝ 2 (v j ∘ evolutionHomeomorph n) x :=
    (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by simp)
  rw [regularizedOperator_comp ε hc2]
  exact congrArg (· * ψ x) ((hv j).2.2.2.1 _ ⟨hx.2.1, hball _ hx⟩)

end Data

end HypoellipticAleksandrov.KineticAleksandrov
