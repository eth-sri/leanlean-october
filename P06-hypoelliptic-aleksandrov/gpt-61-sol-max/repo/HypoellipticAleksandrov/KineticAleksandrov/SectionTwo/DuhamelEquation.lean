module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelRegularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import PDEFoundation.Calculus.RegularityOrder


/-! # Pointwise source equation for the kinetic Duhamel potential -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution

variable {d : ℕ}

section
variable {U : Set (EvolutionVec d)} (hU : IsOpen U) {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)

include hU hB
/-- The full kinetic operator preserves smoothness on an open set with smooth coefficients. -/
theorem contDiffOn_duhamel_operator
    {b : PDE.VectorField d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ PDE.smoothOrder u U) :
    ContDiffOn ℝ PDE.smoothOrder (transportedOperator B b u) U := (id
  (ContDiffOn.add
    (ContDiffOn.add (contDiffOn_duhamel_direction hU hu basisT)
      (ContDiffOn.sum fun i x =>
        ContDiffOn.sum fun j x =>
          ContDiffOn.mul
            (ContDiff.contDiffOn (ContDiff.comp (hB i j) (ContinuousLinearEquiv.contDiff (evolutionProdCLE d))))
            (contDiffOn_duhamel_direction hU (contDiffOn_duhamel_direction hU hu (basisV j)) (basisV i))))
    (ContDiffOn.sum fun i x =>
      ContDiffOn.mul
        (ContDiff.contDiffOn (ContDiff.comp (contDiff_pi.mp hb i) (ContinuousLinearMap.contDiff (diffusedCoord d))))
        (contDiffOn_duhamel_direction hU hu (basisZ i)))))

/-- A smooth kinetic weak solution satisfies its source equation at every interior point. -/
theorem duhamel_operator_eq_of_smooth_weak
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.VectorField d} (hb : IsSmoothDrift b)
    {u f : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ PDE.smoothOrder u U)
    (hf : ContinuousOn f U) (hweak : IsWeakTransportedSolution B b U u f) :
    ∀ x ∈ U, transportedOperator B b u x = f x := by
  have hop := (contDiffOn_duhamel_operator hU hB hb hu).continuousOn
  have hcont := hop.sub hf
  have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by




      have hAe : (∫ x in U, transportedOperator B b u x * ψ x) =
          ∫ x, transportedOperator B b u x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
      have hFe : (∫ x in U, f x * ψ x) = ∫ x, f x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
      have hEq := (integral_transportedAdjoint_contDiffOn hU hB hBs hb hu ψ hψ hc hs).symm.trans (hweak.2 ψ hψ hc hs)
      rw [hAe, hFe] at hEq
      have hfun : (fun x => ψ x • (transportedOperator B b u x - f x)) =
          fun x => transportedOperator B b u x * ψ x - f x * ψ x := by
        funext x
        simp only [smul_eq_mul]
        ring
      simp only [Pi.sub_apply]
      rw [hfun, integral_sub (integrable_evolution_mul_test hop hψ.continuous hc hs) (integrable_evolution_mul_test hf hψ.continuous hc hs), hEq, sub_self])


  intro x hx
  exact sub_eq_zero.mp ((Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae0) hU hcont continuousOn_const) hx)
end


variable {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

/-- The full kinetic Duhamel potential satisfies `Lop W = -g` pointwise in the past cylinder. -/
theorem duhamelPotential_source_equation (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.VectorField d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : HypoellipticAleksandrov.KineticScalarField d) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ PDE.smoothOrder (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    {lam Lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) :
    ∀ p ∈ evolutionPastOpenCylinder Ω γ T,
      transportedForwardOperator B b (duhamelPotential K T g) p = -g p := by
  have hU := (isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
    ).preimage (evolutionHomeomorph d).continuous
  have hsm := duhamelPotential_contDiffOn hH hΩa hΩ hγ B b S K hreal hB hBs hb
    g hgn hg hgc hgs T hgU hlam hm hell hcoerc
  have hweak := (isWeakTransportedSolution_comp_iff B b _ _ _).2
    (duhamel_isKineticWeakTransportedSolution hΩa hΩ hγ B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU)
  have hf : ContinuousOn ((fun p => -g p) ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :=
    (hg.neg.comp (evolutionHomeomorph d).continuous).continuousOn

  intro p hp
  have hx : (evolutionHomeomorph d).symm p ∈
      evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T := by simpa
  have key := (duhamel_operator_eq_of_smooth_weak hU hB hBs hb hsm hf hweak) _ hx
  rw [transportedOperator_comp ((hsm.contDiffAt (hU.mem_nhds hx)).of_le (by simp))] at key
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using key

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
