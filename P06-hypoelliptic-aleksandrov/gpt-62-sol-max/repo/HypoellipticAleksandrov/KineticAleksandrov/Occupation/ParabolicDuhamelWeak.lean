module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelTerminal
import HypoellipticAleksandrov.Analysis.DuhamelPairing

/-!
# The weak equation of the Duhamel potential

Integrating the slice identities `∫_{σ<r} u_r Lop^*ψ + ∫ g(r,·)ψ(r,·) = 0` over the source time
`r` (Fubini) gives `∫ W Lop^*ψ = -∫ g ψ` for every test `ψ` supported in `π ⁻¹' U₀`, where `W` is
the parabolic Duhamel potential regarded as a `z`-independent function of the packed point.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

section
variable {hΩ : MeasurableSet Ω} (g : TimeVelocity d → ℝ)
  (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (T : ℝ)
  (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (p : TimeVelocity d)
include hg hgU

/-- The source slice integrand vanishes after the terminal time. -/
theorem integrand_eq_zero_of_ge {r : ℝ} (hr : T ≤ r) :
    parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  refine parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg p r (fun v => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact absurd (hgU h).1 (not_lt.2 hr)

/-- The potential is the integral of the integrand over all later source times. -/
theorem potential_eq_integral_Ioi :
    parabolicDuhamelPotential K hΩ T g p =
      ∫ r in Ioi p.1, parabolicDuhamelIntegrand K hΩ g p r := by
  unfold parabolicDuhamelPotential
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self (fun r hr => ?_)
  have hrT : T ≤ r := not_lt.1 fun h => hr.2 ⟨hr.1, h.le⟩
  exact integrand_eq_zero_of_ge K g hg T hgU p hrT

end

/-- **The weak equation of the Duhamel potential.**  For every smooth compactly supported test
`ψ` with support in the preimage of `U₀`, `∫ W Lop^* ψ = -∫ g ψ`. -/
theorem duhamel_weak_identity {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' duhamelFiber Ω γ T) :
    (∫ x, parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g
        (evolutionToTimeVelocity d x) *
        transportedAdjoint (zIndependentCoefficient B) b ψ x) =
      -∫ x, g (evolutionToTimeVelocity d x) * ψ x := by
  have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  obtain ⟨a, b₀, hab⟩ := exists_time_range g hgc
  obtain ⟨C, hC0, hub⟩ := exists_parabolicDuhamelIntegrand_bound K hΩ g hgn hgs.continuous hgc
  have hg (r : ℝ) : Measurable (fun v => g (r, v)) := hgs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  have hmeas := measurable_parabolicDuhamelIntegrand K hΩ hγ g hgs.continuous.measurable
  let Λ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q =>
    transportedAdjoint (zIndependentCoefficient B) b ψ (packQ d q)
  let Ψ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => ψ (packQ d q)
  have hΛc : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛs : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨc : Continuous Ψ := hψ.continuous.comp continuous_packQ
  have hΨs : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
  have per : ∀ r : ℝ, (∫ q : ℝ × (PDE.Vec d × PDE.Vec d),
      {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r * Λ q) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, g (r, w.1) * Ψ (r, w) = 0 := by
    intro r
    obtain ⟨V, -, -, hVsm, hVeq, -, hVint⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
    have hD : IsOpen (sliceOpenCylinder Ω γ r) :=
      isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ r
    exact slice_weak_identity (u := fun p => parabolicDuhamelIntegrand K hΩ g p r) hB hb hD
      hVsm hVeq (fun p hp => hVint p ⟨hp.1.le, subset_closure hp.2⟩)
      (hmeas.comp (measurable_id.prodMk measurable_const)) C hC0 (fun p => hub p r) hψ hc r
      (fun x hx hxr => ⟨hxr, (hψs hx).2⟩)
      (fun w => g (r, w.1) * ψ (packQ d (r, w)))
      (slice_terminal_limit K hΩa hγ hP g hgs hgc T hgU C hub hψ.continuous hψs r)
  let A (z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d))) := parabolicDuhamelIntegrand K hΩ g (z.2.1, z.2.2.1) z.1
  let G (q : ℝ × (PDE.Vec d × PDE.Vec d)) := g (q.1, q.2.1) * Ψ q
  have hA : Measurable A := (hmeas.comp ((measurable_snd.fst.prodMk measurable_snd.snd.fst).prodMk measurable_fst))
  have hG : Integrable G ((volume : Measure ℝ).prod (volume : Measure (PDE.Vec d × PDE.Vec d))) :=
    ((hgs.continuous.comp (continuous_fst.prodMk (continuous_snd.fst))).mul hΨc).integrable_of_hasCompactSupport hΨs.mul_left
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod]
  simp only [evolutionToTimeVelocity_packQ]
  change (∫ q, parabolicDuhamelPotential K hΩ T g (q.1, q.2.1) * Λ q) = -∫ q, G q
  exact Analysis.integral_duhamel_of_slice Prod.fst measurable_fst A Λ
    (fun q => parabolicDuhamelPotential K hΩ T g (q.1, q.2.1)) G hA (hΛc.integrable_of_hasCompactSupport hΛs) hG
    hC0 (fun z => hub _ _) (fun z hr => parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg _ _ (hab _ hr))
    (fun q => potential_eq_integral_Ioi K g hg T hgU _) per

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
