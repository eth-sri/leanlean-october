module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Smoothness and the classical source equation for the parabolic Duhamel potential

The packed function `(σ, v, z) ↦ W(σ, v)` is a distributional solution of `Lop u = -g` on the
preimage of `U₀`, so Hörmander's theorem (taken as the explicit hypothesis `hH`) gives a smooth
representative, which equals the continuous `W` pointwise.  The weak equation then becomes the
classical equation `∂_σ W + B : D_v² W = -g` in `U₀`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology MatrixOrder

variable {n : ℕ}

/- Hörmander regularity for a distributional solution of `Lop u = g` with smooth `g`
(packed coordinates), with Hörmander's theorem as the explicit hypothesis `hH`. -/
theorem exists_smooth_representative_transported_source
    (hH : HormanderHypoellipticityStatement) {lam Lam m B b} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hm : 0 < m) (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    {U } (hU : IsOpen U) {u g }
    (hu : IsWeakTransportedSolution B b U u g) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ∃ f : EvolutionVec n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_transportedFields hlam hB_smooth hB_ell hb_smooth hm hb_coercive U
  exact hH hU _ _ _ _ hX hspan contDiffOn_const (hasWeakHormanderEquation_transportedFields hlam hB_smooth hB_ell hb_smooth hu hg)

section Potential

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/- The parabolic operator of a smooth function with continuous coefficient is continuous. -/
theorem continuousOn_scalarParabolicOperator_of_contDiffOn {B' }
    (hBc : ∀ i j, Continuous (fun p : TimeVelocity d => B' p.1 p.2 i j))
    {D } (hD : IsOpen D) {w }
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D) :
    ContinuousOn (scalarParabolicOperator B' (fun _ _ => 0) w) D := by
  have hu :=
    isScalarC12On_of_isOpen_contDiffOn_two hD (hw.of_le (by norm_num))
  have hfun : scalarParabolicOperator B' (fun _ _ => 0) w = fun p =>
      scalarTimeDerivative w p + ∑ i, ∑ j, B' p.1 p.2 i j * scalarSpatialHessian w p i j := by
    funext p
    simp [scalarParabolicOperator_apply, matrixContraction, PDE.vecDot]
  rw [hfun]
  refine hu.continuousOn_scalarTimeDerivative.add (continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => (hBc i j).continuousOn.mul ?_)
  exact (show Continuous (fun A : PDE.Mat d => A i j) from
    (continuous_apply j).comp (continuous_apply i)).comp_continuousOn
      hu.continuousOn_scalarSpatialHessian

/- The lift `(σ, v) ↦ (σ, v, 0)` is smooth. -/
theorem contDiff_zeroLift : ContDiff ℝ (⊤ : ℕ∞) (fun p : TimeVelocity d =>
    packPoint p.1 p.2 (0 : PDE.Vec d) : TimeVelocity d → EvolutionVec d) := by
  have : (fun p : TimeVelocity d => packPoint p.1 p.2 (0 : PDE.Vec d)) =
      (evolutionProdCLE d).symm ∘ (fun p : TimeVelocity d => (p.1, (p.2, (0 : PDE.Vec d)))) := by
    funext p; rfl
  rw [this]
  exact (evolutionProdCLE d).symm.contDiff.comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

/- **Smoothness and the source equation.**  Under Hörmander's theorem (`hH`), the Duhamel
potential is smooth in `U₀` and satisfies `∂_σ W + B : D_v² W = -g` there. -/
end Potential

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
