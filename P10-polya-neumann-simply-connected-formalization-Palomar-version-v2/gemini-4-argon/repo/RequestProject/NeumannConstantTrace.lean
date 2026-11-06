module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import RequestProject.TraceH1
public import RequestProject.NeumannZero
public import RequestProject.NeumannBoundaryPole
public import RequestProject.ReconTrace

/-!
# Constants and the actual boundary trace at zero energy

A compactly supported smooth function which is constant near the closure
of the domain represents the genuine weak-gradient H¹ constant. Agreement
of the constructed trace with smooth boundary values then identifies its
trace with the ordinary `dθ` boundary constant. The zero eigenspace consists
exactly of these constants, so the trace is injective on the zero form kernel.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Metric
open scoped Real InnerProductSpace

/-- The genuine constant H¹ vector, with zero weak derivatives. Finiteness
of the restricted measure follows from the boundedness of the domain. -/
def h1Constant  (hb : Bornology.IsBounded Ω) (c : ℂ) : NeumannH1 Ω :=
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  h1Vector (isWeakGradient_const Ω c)

@[simp] theorem h1Value_h1Constant  hb
    [IsFiniteMeasure (volume.restrict Ω)] c :
    h1Value Ω (h1Constant hb c) = Lp.const 2 (volume.restrict Ω) c := rfl


/-- The actual trace of a genuine H¹ constant is the same boundary constant,
with respect to ordinary parameter measure `dθ`. -/
theorem h1BoundaryTrace_h1Constant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) c :
    h1BoundaryTrace hb hL hγ (h1Constant hb c) =
      Lp.const 2 (volume.restrict (Ioc 0 (2 * π))) c := by
  obtain ⟨f, hfu, hf⟩ : ∃ f : smoothTraceTests, smoothTraceH1 Ω f = h1Constant hb c ∧ ∀ z ∈ closure Ω, f z = c := by
    haveI : IsFiniteMeasure (volume.restrict Ω) :=
      isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
    obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ closure Ω ⊆ ball 0 R := by
      obtain ⟨R, hR⟩ := hb.closure.subset_ball 0
      exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
    obtain ⟨χ, hχs, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
    let f : smoothTraceTests := ⟨fun z => χ z * c,
      ⟨(Complex.ofRealCLM.contDiff.comp hχs).mul contDiff_const,
        (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
        subset_univ _⟩⟩
    have hf : ∀ z ∈ closure Ω, f z = c := by
      intro z hz
      simp [f, (fun z hz => hχ1 z (ball_subset_closedBall hz)) z (hR hz)]
    refine ⟨f, ?_, hf⟩
    apply h1Value_injective hL.1.1
    rw [h1Value_smoothTraceH1, h1Value_h1Constant]
    apply Lp.ext
    filter_upwards [(f.property.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp,
      Lp.coeFn_const 2 (volume.restrict Ω) c,
      ae_restrict_mem hL.1.1.measurableSet] with z hto hconst hz
    exact hto.trans ((hf z (subset_closure hz)).trans hconst.symm)
  rw [← hfu]
  apply Lp.ext
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f,
    Lp.coeFn_const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c,
    ae_restrict_mem measurableSet_Ioc] with θ htrace hconst hθ
  exact htrace.trans ((hf (γ θ) (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ (Ioc_subset_Icc_self hθ)))).trans hconst.symm)

/-- A boundary constant vanishes as an L² class exactly when its value is
zero; the ordinary parameter interval has positive measure. -/
theorem boundaryLpConst_eq_zero_iff (c : ℂ) :
    Lp.const 2 (volume.restrict (Ioc 0 (2 * π))) c = 0 ↔ c = 0 := by
  haveI : NeZero (volume.restrict (Ioc 0 (2 * π))) := ⟨by
    intro hzero
    have hvol := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Ioc, sub_zero] at hvol
    exact (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) hvol⟩
  constructor
  · intro hc
    obtain ⟨_, hc0⟩ := (show ∀ᵐ θ ∂volume.restrict (Ioc 0 (2 * π)), c = 0 by
      filter_upwards [Lp.coeFn_const 2 (volume.restrict (Ioc 0 (2 * π))) c,
        Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 (2 * π)))] with θ hconst hzero
      exact hconst.symm.trans ((congrArg (fun u => u θ) hc).trans hzero)).exists
    exact hc0
  · rintro rfl
    exact map_zero _

/-- The entire actual zero form kernel consists of the genuine constants. -/
theorem h1HelmholtzForm_zero_eq_zero_iff_constant 
    hb (hΩ : IsDomain Ω) u :
    h1HelmholtzForm Ω 0 u = 0 ↔ ∃ c : ℂ, u = h1Constant hb c := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := (mem_neumannEigenspace_zero_iff hΩ (h1Value Ω u)).mp
      (h1HelmholtzForm_kernel_mem Ω 0 u hu)
    refine ⟨c, h1Value_injective hΩ.1 ?_⟩
    simpa using hc
  · rintro ⟨c, rfl⟩
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, inner_zero_right]
    simp [h1Constant]

end PolyaNeumann

end
