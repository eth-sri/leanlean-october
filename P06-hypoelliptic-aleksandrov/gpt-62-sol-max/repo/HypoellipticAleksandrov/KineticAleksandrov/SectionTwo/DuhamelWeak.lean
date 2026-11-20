module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTerminal
import HypoellipticAleksandrov.Analysis.DuhamelPairing

/-! # Distributional equation for the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Packing the product coordinates agrees with the existing kinetic coordinate homeomorphism. -/
@[simp] theorem duhamel_homeomorph_packQ (q : ℝ × EvolutionAmbientState d) :
    evolutionHomeomorph d (packQ d q) = ⟨q.1, q.2.1, q.2.2⟩ := by
  simp only [evolutionHomeomorph_apply, packQ, timeCoord_packPoint,
    diffusedCoord_packPoint, transportedCoord_packPoint]

section
variable (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ) (T : ℝ)
  (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (p : KineticPoint d)
include hU

/-- Source integrands vanish at all source times at or beyond the terminal face. -/
theorem duhamelIntegrand_eq_zero_of_ge {r : ℝ} (hr : T ≤ r) : duhamelIntegrand K g p r = 0 := by
  unfold duhamelIntegrand
  split
  · unfold duhamelSourceIntegral
    have hz : ∀ w : EvolutionAmbientState d, g ⟨r, w.1, w.2⟩ = 0 := by
      intro w
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact absurd (hU h).1 (not_lt.2 hr)
    simp only [hz, integral_zero]
  · rfl

/-- Compact interior source support allows integration over every later source time. -/
theorem duhamelPotential_eq_integral_Ioi :
    duhamelPotential K T g p = ∫ r in Ioi p.time, duhamelIntegrand K g p r := by
  unfold duhamelPotential
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self (fun r hr => ?_)
  have hrT : T ≤ r := not_lt.1 fun h => hr.2 ⟨hr.1, h.le⟩
  exact duhamelIntegrand_eq_zero_of_ge K g T hU p hrT

end

/-- The kinetic source potential satisfies the exact full adjoint distributional identity. -/
theorem duhamel_weak_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
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
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :
    (∫ x, duhamelPotential K T g (evolutionHomeomorph d x) * transportedAdjoint B b ψ x) =
      -∫ x, g (evolutionHomeomorph d x) * ψ x := by
  obtain ⟨a, b₀, -, hab⟩ := exists_time_window_of_hasCompactSupport g hgc
  obtain ⟨C, hC0, hub⟩ := exists_duhamelIntegrand_bound K g hgn hg hgc
  have hmeas := measurable_duhamelIntegrand K hΩ hγ g hg.measurable
  let Λ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q =>
    transportedAdjoint B b ψ (packQ d q)
  let Ψ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => ψ (packQ d q)
  have hΛc : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛs : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨc : Continuous Ψ := hψ.continuous.comp continuous_packQ
  have hΨs : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
  have per : ∀ r : ℝ, (∫ q : ℝ × (PDE.Vec d × PDE.Vec d),
      {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r * Λ q) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, g ⟨r, w.1, w.2⟩ * Ψ (r, w) = 0 := by
    intro r
    obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal
      g hg hgc hgs T hgU r
    let D := evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ r
    have hD : IsOpen D := (isOpen_duhamelCylinder
      (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ r).preimage (evolutionHomeomorph d).continuous
    have hVsm : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph d) D :=
      hV.2.2.1.comp (evolutionProdCLE d).contDiff.contDiffOn (fun x hx => hx)
    have hVeq : ∀ x ∈ D, transportedOperator B b (V ∘ evolutionHomeomorph d) x = 0 := by
      intro x hx
      rw [transportedOperator_comp ((hVsm.contDiffAt (hD.mem_nhds hx)).of_le (by simp))]
      exact hV.2.2.2.1 _ hx
    have huV : ∀ x ∈ D, duhamelIntegrand K g (evolutionHomeomorph d x) r =
        (V ∘ evolutionHomeomorph d) x := fun x hx =>
      duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe _
        ⟨hx.1.le, subset_closure hx.2⟩
    have hm : Measurable (fun x => duhamelIntegrand K g (evolutionHomeomorph d x) r) :=
      hmeas.comp ((evolutionHomeomorph d).continuous.measurable.prodMk measurable_const)
    have key := kinetic_slice_weak_identity hB hBs hb hD hVsm hVeq huV hm C hC0
      (fun x => hub _ r) hψ hc r (fun x hx hxr => ⟨hxr, (hψs hx).2⟩)
      (fun w => g ⟨r, w.1, w.2⟩ * ψ (packQ d (r, w)))
      (by simpa only [duhamel_homeomorph_packQ] using
        (duhamelSlice_terminalLimit hΩa hΩ hγ B b S K hreal g hg hgc hgs T hgU C hub
          hψ.continuous hψs r))
    simpa only [duhamel_homeomorph_packQ] using key
  let A (z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d))) := duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1
  let G (q : ℝ × (PDE.Vec d × PDE.Vec d)) := g ⟨q.1, q.2.1, q.2.2⟩ * Ψ q
  have hA : Measurable A := (hmeas.comp (((KineticPoint.measurable_equivProd_symm d).comp measurable_snd).prodMk
      measurable_fst))
  have hG : Integrable G ((volume : Measure ℝ).prod (volume : Measure (PDE.Vec d × PDE.Vec d))) :=
    ((hg.comp (KineticPoint.homeomorphProd d).symm.continuous).mul hΨc).integrable_of_hasCompactSupport hΨs.mul_left
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod]
  simp only [duhamel_homeomorph_packQ]
  change (∫ q, duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ * Λ q) = -∫ q, G q
  exact Analysis.integral_duhamel_of_slice Prod.fst measurable_fst A Λ
    (fun q => duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) G hA (hΛc.integrable_of_hasCompactSupport hΛs) hG
    hC0 (fun z => hub _ _) (fun z hr => duhamelIntegrand_eq_zero_of_time_not_mem K g a b₀ hab _ _ hr)
    (fun q => duhamelPotential_eq_integral_Ioi K g T hgU _) per

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
