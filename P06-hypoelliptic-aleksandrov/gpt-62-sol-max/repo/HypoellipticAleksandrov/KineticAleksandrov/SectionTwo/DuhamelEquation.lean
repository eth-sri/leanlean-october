module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelWeak
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Interior regularity and the pointwise source equation for the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ}

section
variable {U : Set (EvolutionVec d)} (hU : IsOpen U) {B : FullKineticCoefficient d}
  (hB : IsSmoothFullKineticCoefficient B)
include hU hB

/-- The full kinetic operator preserves smoothness on an open set with smooth coefficients. -/
theorem contDiffOn_duhamel_operator
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (transportedOperator B b u) U := by
  have hzero : regularizedOperator B b 0 u = transportedOperator B b u :=
    funext fun x => by simp [regularizedOperator]
  simpa only [hzero] using contDiffOn_regularizedOperator hU hB hb 0 hu

/-- A smooth kinetic weak solution satisfies its source equation at every interior point. -/
theorem duhamel_operator_eq_of_smooth_weak
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u f : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hf : ContinuousOn f U) (hweak : IsWeakTransportedSolution B b U u f) :
    ∀ x ∈ U, transportedOperator B b u x = f x := by
  have hop := (contDiffOn_duhamel_operator hU hB hb hu).continuousOn
  have hcont := hop.sub hf
  have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
      have h1 := integral_transportedAdjoint_contDiffOn hU hB hBs hb hu ψ hψ hc hs
      have h2 := hweak.2 ψ hψ hc hs
      have iA := integrable_evolution_mul_test hop hψ.continuous hc hs
      have iF := integrable_evolution_mul_test hf hψ.continuous hc hs
      have hAe : (∫ x in U, transportedOperator B b u x * ψ x) =
          ∫ x, transportedOperator B b u x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
      have hFe : (∫ x in U, f x * ψ x) = ∫ x, f x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
      have hEq := h1.symm.trans h2
      rw [hAe, hFe] at hEq
      have hfun : (fun x => ψ x • (transportedOperator B b u x - f x)) =
          fun x => transportedOperator B b u x * ψ x - f x * ψ x := by
        funext x
        simp only [smul_eq_mul]
        ring
      simp only [Pi.sub_apply]
      rw [hfun, integral_sub iA iF, hEq, sub_self])
  have hae1 : (fun x => transportedOperator B b u x - f x)
      =ᵐ[volume.restrict U] fun _ => (0 : ℝ) :=
    (ae_restrict_iff' hU.measurableSet).2 hae0
  have heq := Measure.eqOn_open_of_ae_eq hae1 hU hcont continuousOn_const
  intro x hx
  exact sub_eq_zero.mp (heq hx)

end

variable {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The continuous Duhamel potential solves the weak equation, hence Hörmander regularity
gives a smooth interior representative which satisfies the equation pointwise. -/
theorem duhamelPotential_regular
    (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    {lam Lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) :
    ContinuousOn (duhamelPotential K T g) (evolutionPastClosedCylinder Ω γ T) ∧
    IsKineticWeakTransportedSolution B b (evolutionPastOpenCylinder Ω γ T)
      (duhamelPotential K T g) (fun p => -g p) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (duhamelPotential K T g ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) ∧
    (∀ p ∈ evolutionPastOpenCylinder Ω γ T,
      transportedForwardOperator B b (duhamelPotential K T g) p = -g p) := by
  let D := evolutionPastOpenCylinder Ω γ T
  let e := evolutionHomeomorph d
  let W := duhamelPotential K T g
  have hU : IsOpen (e ⁻¹' D) :=
    (isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).preimage e.continuous
  have hc := continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal g hgn hg hgc hgs T hgU
  have hWQ : ContinuousOn (W ∘ e) (e ⁻¹' D) :=
    (hc.mono (fun p (hp : p ∈ D) => ⟨hp.1.le, subset_closure hp.2⟩)).comp
      e.continuous.continuousOn (mapsTo_preimage e D)
  have hweak : IsWeakTransportedSolution B b (e ⁻¹' D) (W ∘ e) ((fun p => -g p) ∘ e) := by
    refine ⟨hWQ.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
    have hfull := duhamel_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU hψ hc hs
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [Function.comp_apply, neg_mul, integral_neg]
      exact hfull
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
    · intro x hx
      rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) ((fun p => -g p) ∘ e) (e ⁻¹' D) :=
    ((hgs.comp (evolutionProdCLE d).contDiff).neg).contDiffOn
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hlam hB hell hb
    hm hcoerc hU hweak hg'
  have hsm := hf.congr (Measure.eqOn_open_of_ae_eq hae hU hWQ hf.continuousOn)
  refine ⟨hc, (isWeakTransportedSolution_comp_iff B b D W _).mp hweak, hsm, ?_⟩
  have heq := duhamel_operator_eq_of_smooth_weak hU hB hBs hb hsm hg'.continuousOn hweak
  intro p hp
  have hx : e.symm p ∈ e ⁻¹' D := by simpa using hp
  have key := heq _ hx
  rw [transportedOperator_comp ((hsm.contDiffAt (hU.mem_nhds hx)).of_le (by simp))] at key
  simpa only [e, Function.comp_apply, Homeomorph.apply_symm_apply] using key

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
