module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeWeak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality

/-!
# Classical recovery for smooth regularized weak solutions

Integration by parts discharges the actual smooth jets. The fundamental lemma
then recovers the pointwise equation, without adding it as a hypothesis.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

open HypoellipticAleksandrov MeasureTheory Set

section
variable {n : ℕ} {U : Set (EvolutionVec n)} (hU : IsOpen U) {B : FullKineticCoefficient n}
  (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
  {b : PDE.Vec n → PDE.Vec n} (hb : IsSmoothDrift b) (ε : ℝ) {u : EvolutionVec n → ℝ}
  (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
include hU hB hBs hb hu

/-- Integration against the regularized adjoint equals integration of the classical
operator for an actually smooth interior function. -/
theorem integral_regularizedAdjoint_contDiffOn
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * regularizedAdjoint B b ε ψ x) =
      ∫ x in U, regularizedOperator B b ε u x * ψ x := integral_regularizedAdjoint_contDiffOn_two hU hB hBs hb ε (hu.of_le (by simp)) ψ hψ hc hs

/-- A smooth regularized weak solution satisfies its zero-source equation pointwise. -/
theorem regularizedOperator_eq_zero_of_smooth_weak
    (hw : IsWeakRegularizedSolution B b ε U u (fun _ => 0)) :
    ∀ x ∈ U, regularizedOperator B b ε u x = 0 := by
  have hop := (contDiffOn_regularizedOperator hU hB hb ε hu).continuousOn
  have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hop.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
      have h1 := integral_regularizedAdjoint_contDiffOn hU hB hBs hb ε hu ψ hψ hc hs
      have h2 := hw.2 ψ hψ hc hs
      have hEq : (∫ x in U, regularizedOperator B b ε u x * ψ x) = 0 := by
        rw [← h1, h2]
        simp only [zero_mul, integral_zero]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero])] at hEq
      simpa only [smul_eq_mul, mul_comm] using hEq)
  have hae1 : regularizedOperator B b ε u =ᵐ[volume.restrict U] fun _ => (0 : ℝ) :=
    (ae_restrict_iff' hU.measurableSet).2 hae0
  have heq := Measure.eqOn_open_of_ae_eq hae1 hU hop continuousOn_const
  exact fun x hx => heq hx

end

/-- A continuous homogeneous viscous weak solution is classical in the open set. -/
theorem classical_kinetic_of_continuous_weak {n : ℕ} {lam Lam ε : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (hε : 0 < ε) {U : Set (KineticPoint n)} (hU : IsOpen U)
    {f : KineticPoint n → ℝ} (hf : ContinuousOn f U)
    (hw : IsKineticWeakRegularizedSolution B b ε U f 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) ∧
    ∀ p ∈ U, viscousTransportedOperator B b ε f p = 0 := by
  obtain ⟨w, hws, hae⟩ := exists_smooth_viscous_kinetic_representative hlam hB hell hb U hU ε hε f hw
  have hV := hU.preimage (evolutionHomeomorph n).continuous
  have hfg := eqOn_of_ae_eq_of_continuousOn_kinetic hU
    (hf.comp (evolutionHomeomorph n).continuous.continuousOn fun _ hx => hx) hws.continuousOn hae
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) :=
    hws.congr (fun _ hx => hfg hx)
  have hOp := regularizedOperator_eq_zero_of_smooth_weak hV hB hBs hb ε hsm
    ((isWeakRegularizedSolution_comp_iff B b ε U f 0).mpr hw)
  refine ⟨hsm, fun p hp => ?_⟩
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by simpa [x] using hp
  have hz := hOp x hx
  rw [regularizedOperator_comp ε ((hsm.contDiffAt (hV.mem_nhds hx)).of_le (by simp))] at hz
  simpa only [x, Homeomorph.apply_symm_apply, viscousTransportedOperator] using hz

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
