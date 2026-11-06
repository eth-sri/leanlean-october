module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Ring

/-!
# The weak equation in the zero-viscosity limit

Compact adjoint tests and their regularizing remainders are integrable. Weak
convergence against both tests removes the viscosity term by multiplication
with its vanishing coefficient. No derivative convergence is asserted.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory Evolution
open scoped Topology MatrixOrder

private theorem weak_transport_limit {n : ℕ}
    {B : FullKineticCoefficient n} {b : PDE.VectorField n}
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (U : Set (KineticPoint n)) (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : ℕ → HypoellipticAleksandrov.KineticScalarField n) (u : HypoellipticAleksandrov.KineticScalarField n)
    (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, IsKineticWeakRegularizedSolution B b (ε j) U (v j) (fun _ => 0))
    (hb : ∀ j, ∀ᵐ p ∂volume.restrict U, |v j p| ≤ C)
    (hu : AEStronglyMeasurable u (volume.restrict U))
    (hub : ∀ᵐ p ∂volume.restrict U, |u p| ≤ C)
    (hlim : ∀ ψ : HypoellipticAleksandrov.KineticScalarField n, IntegrableOn ψ U  →
      Tendsto (fun j => ∫ p in U, v j p * ψ p) atTop (𝓝 (∫ p in U, u p * ψ p))) :
    IsKineticWeakTransportedSolution B b U u (fun _ => 0) := by
  let  :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology


  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    ((memLp_top_of_bound hu C (hub)).locallyIntegrable le_top), ?_⟩
  intro ψ hψ hc hs
  let A  := fun p =>
    regularizedAdjoint B b 0 ψ ((evolutionHomeomorph n).symm p)
  let D  := fun p =>
    regularizedAdjoint B b 1 ψ ((evolutionHomeomorph n).symm p) - A p
  have htest (e : ℝ) : IntegrableOn (fun p  =>
      regularizedAdjoint B b e ψ ((evolutionHomeomorph n).symm p)) U  := by

    exact ((contDiff_regularizedAdjoint hBs hbs hψ e).continuous.comp
      (evolutionHomeomorph n).symm.continuous).integrable_of_hasCompactSupport
      ((HasCompactSupport.intro hc fun x hx => regularizedAdjoint_eq_zero_of_notMem_tsupport e ψ hx).comp_homeomorph (evolutionHomeomorph n).symm) |>.integrableOn
  have hA  := htest 0
  have hD  := (htest 1).sub hA
  have hprod (j : ℕ) (f : HypoellipticAleksandrov.KineticScalarField n) (hf : IntegrableOn f U ) :
      IntegrableOn (fun p => v j p * f p) U  := by
    apply hf.bdd_mul (hv j).1.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hb j
  have hsplit (j : ℕ) :
      (∫ p in U, v j p * A p) + ε j * (∫ p in U, v j p * D p) = 0 := by
    have heq := (hv j).2 ψ hψ hc hs
    simp only [zero_mul, integral_zero] at heq
    have hid : (fun p => v j p * regularizedAdjoint B b (ε j) ψ
        ((evolutionHomeomorph n).symm p)) =
        (fun p => v j p * A p + ε j * (v j p * D p)) := by
      funext p
      dsimp [A, D, regularizedAdjoint]
      ring
    rw [hid, integral_add (hprod j A hA) ((hprod j D hD).const_mul (ε j)),
      integral_const_mul] at heq
    exact heq


  have heq := tendsto_nhds_unique ((hlim A hA).add (hεlim.mul (hlim D hD))) (by
      simpa only [hsplit] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
        atTop (𝓝 0)))
  simp only [zero_mul, add_zero] at heq
  simpa only [A, regularizedAdjoint, zero_mul, add_zero, integral_zero] using heq

/-- Bounded weak convergence removes the regularizing viscosity term. -/
theorem weak_transport_equation_of_vanishing_viscosity
    (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.VectorField n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (τ : ℝ) (ε : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hεlim : Tendsto ε atTop (nhds 0))
    (v : ℕ → HypoellipticAleksandrov.KineticScalarField n) (u : HypoellipticAleksandrov.KineticScalarField n)
    (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, IsKineticWeakRegularizedSolution B b (ε j)
      (evolutionPastOpenCylinder Ω γ τ) (v j) (fun _ => 0))
    (hb : ∀ j, ∀ᵐ p ∂volume.restrict (evolutionPastOpenCylinder Ω γ τ),
      |v j p| ≤ C)
    (hu : AEStronglyMeasurable u
      (volume.restrict (evolutionPastOpenCylinder Ω γ τ)))
    (hub : ∀ᵐ p ∂volume.restrict (evolutionPastOpenCylinder Ω γ τ), |u p| ≤ C)
    (hlim : ∀ ψ : HypoellipticAleksandrov.KineticScalarField n,
      IntegrableOn ψ (evolutionPastOpenCylinder Ω γ τ)  →
        Tendsto (fun j => ∫ p in evolutionPastOpenCylinder Ω γ τ, v j p * ψ p)
          atTop (nhds (∫ p in evolutionPastOpenCylinder Ω γ τ, u p * ψ p))) :
    IsKineticWeakTransportedSolution B b
      (evolutionPastOpenCylinder Ω γ τ) u (fun _ => 0) := weak_transport_limit hB_smooth hb_smooth (evolutionPastOpenCylinder Ω γ τ)
    ε hεlim v u C hC hv hb hu hub hlim

end HypoellipticAleksandrov.KineticAleksandrov
