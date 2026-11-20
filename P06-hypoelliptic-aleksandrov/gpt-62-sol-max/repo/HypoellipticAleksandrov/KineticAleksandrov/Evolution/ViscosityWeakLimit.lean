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

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory Evolution
open scoped Topology MatrixOrder

/-- Bounded weak convergence removes the regularizing viscosity term. -/
theorem weak_transport_equation_of_vanishing_viscosity {n : ℕ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (U : Set (KineticPoint n)) (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : ℕ → KineticPoint n → ℝ) (u : KineticPoint n → ℝ)
    (C : ℝ)
    (hv : ∀ j, IsKineticWeakRegularizedSolution B b (ε j) U (v j) (fun _ => 0))
    (hb : ∀ j, ∀ᵐ p ∂volume.restrict U, |v j p| ≤ C)
    (hu : AEStronglyMeasurable u (volume.restrict U))
    (hub : ∀ᵐ p ∂volume.restrict U, |u p| ≤ C)
    (hlim : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ p in U, v j p * ψ p) atTop (𝓝 (∫ p in U, u p * ψ p))) :
    IsKineticWeakTransportedSolution B b U u (fun _ => 0) := by
  let : SecondCountableTopology (KineticPoint n) :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
  have hub' : ∀ᵐ p ∂volume.restrict U, ‖u p‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hub
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    ((memLp_top_of_bound hu C hub').locallyIntegrable le_top), ?_⟩
  intro ψ hψ hc hs
  let A : KineticPoint n → ℝ := fun p =>
    regularizedAdjoint B b 0 ψ ((evolutionHomeomorph n).symm p)
  let D : KineticPoint n → ℝ := fun p =>
    regularizedAdjoint B b 1 ψ ((evolutionHomeomorph n).symm p) - A p
  have htest (e : ℝ) : IntegrableOn (fun p : KineticPoint n =>
      regularizedAdjoint B b e ψ ((evolutionHomeomorph n).symm p)) U volume := by
    have hcompact : HasCompactSupport (regularizedAdjoint B b e ψ) :=
      HasCompactSupport.intro hc fun x hx => regularizedAdjoint_eq_zero_of_notMem_tsupport e ψ hx
    exact ((contDiff_regularizedAdjoint hBs hbs hψ e).continuous.comp
      (evolutionHomeomorph n).symm.continuous).integrable_of_hasCompactSupport
      (hcompact.comp_homeomorph (evolutionHomeomorph n).symm) |>.integrableOn
  have hA : IntegrableOn A U volume := htest 0
  have hD : IntegrableOn D U volume := (htest 1).sub hA
  have hprod (j : ℕ) (f : KineticPoint n → ℝ) (hf : IntegrableOn f U volume) :
      IntegrableOn (fun p => v j p * f p) U volume := by
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
  have ht := (hlim A hA).add (hεlim.mul (hlim D hD))
  have hz : Tendsto (fun j => (∫ p in U, v j p * A p) +
      ε j * (∫ p in U, v j p * D p)) atTop (𝓝 0) := by
    simpa only [hsplit] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 0))
  have heq := tendsto_nhds_unique ht hz
  simp only [zero_mul, add_zero] at heq
  simpa only [A, regularizedAdjoint, zero_mul, add_zero, integral_zero] using heq

end HypoellipticAleksandrov.KineticAleksandrov
