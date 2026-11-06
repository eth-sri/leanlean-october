module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelLayer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
import Lean.Elab.Tactic.SolveByElim
public import PDEFoundation.Calculus.RegularityOrder




/-! # Terminal source limits for full kinetic Duhamel slices -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

/-- The kinetic past cylinder is open for an open base domain and continuous motion. -/
theorem isOpen_duhamelCylinder (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (evolutionPastOpenCylinder Ω γ T) := (isOpen_evolutionPastOpenCylinder hΩ hγ T)

variable (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (B : FullKineticCoefficient d) (b : PDE.VectorField d) (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ) (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K) (g : HypoellipticAleksandrov.KineticScalarField d) (hg : Continuous g) (hc : HasCompactSupport g) (hs : ContDiff ℝ PDE.smoothOrder (fun q : ℝ × EvolutionAmbientState d => g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ) (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)

include hΩa hγ hreal hg hc hs hU
/-- The source integrand tends to its terminal datum at every interior terminal state. -/
theorem duhamelSlice_leftLimit
    (r : ℝ) (w : EvolutionAmbientState d)
    (hw : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastOpenCylinder Ω γ T) :
    Tendsto (fun t => duhamelIntegrand K g ⟨t, w.1, w.2⟩ r)
      (𝓝[<] r) (𝓝 (g ⟨r, w.1, w.2⟩)) := by
  let sharedTerm_f81cfc9884 := ((KineticPoint.mk r w.1 w.2))
  obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal g hg hc hs T hU r

  have hmapc : Continuous (fun t  => (KineticPoint.mk t w.1 w.2)) :=
    KineticPoint.continuous_mk continuous_id continuous_const continuous_const
  have hcl : sharedTerm_f81cfc9884 ∈ evolutionPastClosedCylinder Ω γ r :=
    ⟨le_rfl, subset_closure hw.2⟩
  have hev : ∀ᶠ t in 𝓝[<] r,
      (KineticPoint.mk t w.1 w.2) ∈ evolutionPastClosedCylinder Ω γ r := by

    filter_upwards [(hmapc.continuousAt.eventually ((isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).mem_nhds hw)).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht2
    exact ⟨le_of_lt ht2, subset_closure ht.2⟩

  have h1 := (hV.2.1 _ hcl).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨(hmapc.tendsto r).mono_left nhdsWithin_le_nhds, hev⟩)
  have ht := hV.2.2.2.2.1 sharedTerm_f81cfc9884 ⟨rfl, hcl.2⟩
  change V sharedTerm_f81cfc9884 = g sharedTerm_f81cfc9884 at ht
  rw [ht] at h1
  refine h1.congr' ?_
  filter_upwards [hev] with t ht
  exact (duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe _ ht).symm

/-- The slice times a compact test has the precise terminal limit, also outside the test support. -/
theorem duhamelSlice_terminalLimit  (C : ℝ)
    (hub : ∀ p r, |duhamelIntegrand K g p r| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : Continuous ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T)
    (r : ℝ) (w : EvolutionAmbientState d) :
    Tendsto (fun t => duhamelIntegrand K g ⟨t, w.1, w.2⟩ r * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (g ⟨r, w.1, w.2⟩ * ψ (packQ d (r, w)))) := by
  have hψt : Tendsto (fun t => ψ (packQ d (t, w))) (𝓝[<] r)
      (𝓝 (ψ (packQ d (r, w)))) :=
    ((hψ.comp (continuous_packQ.comp (continuous_id.prodMk continuous_const))).tendsto r
      ).mono_left nhdsWithin_le_nhds
  by_cases h0 : ψ (packQ d (r, w)) = 0
  · rw [h0, mul_zero]

    refine squeeze_zero_norm (fun t => ?_) (by
        simpa [h0] using hψt.abs.const_mul C)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hub _ _) (abs_nonneg _)
  ·

    exact (duhamelSlice_leftLimit hΩa hΩ hγ B b S K hreal g hg hc hs T hU r w (by
        simpa only [mem_preimage, evolutionHomeomorph_apply, packQ, timeCoord_packPoint,
          diffusedCoord_packPoint, transportedCoord_packPoint] using (hψs (subset_closure h0)))).mul hψt

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
