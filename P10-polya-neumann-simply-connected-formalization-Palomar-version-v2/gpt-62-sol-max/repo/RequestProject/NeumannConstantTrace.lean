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

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
include Ω hb

/-- The genuine constant H¹ vector, with zero weak derivatives. Finiteness
of the restricted measure follows from the boundedness of the domain. -/
def h1Constant  (c : ℂ) : NeumannH1 Ω :=
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  h1Vector (isWeakGradient_const Ω c)

@[simp] theorem h1Value_h1Constant 
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    h1Value Ω (h1Constant hb c) = Lp.const 2 (volume.restrict Ω) c := rfl

@[simp] theorem h1Gradient_h1Constant 
    (c : ℂ) (i : Fin 2) : h1Gradient Ω i (h1Constant hb c) = 0 := rfl


/-- The actual H¹ constant has a compactly supported smooth representative
which agrees with the constant on a neighbourhood of the domain closure. -/
theorem exists_smoothTraceTest_h1Constant 
    (hΩ : IsOpen Ω) (c : ℂ) :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = h1Constant hb c ∧
      ∀ z ∈ closure Ω, f z = c := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨φ, hφ, hf⟩ := exists_smooth_test_eqOn_bounded hb.closure (contDiff_const (c := c))
  let f : smoothTraceTests := ⟨φ, hφ⟩
  refine ⟨f, ?_, fun z hz => hf hz⟩
  apply h1Value_injective hΩ
  rw [h1Value_h1Constant]
  apply Lp.ext
  filter_upwards [(f.property.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp,
    Lp.coeFn_const 2 (volume.restrict Ω) c,
    ae_restrict_mem hΩ.measurableSet] with z hto hconst hz
  exact hto.trans ((hf (subset_closure hz)).trans hconst.symm)

/-- The actual trace of a genuine H¹ constant is the same boundary constant,
with respect to ordinary parameter measure `dθ`. -/
theorem h1BoundaryTrace_h1Constant 
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (c : ℂ) :
    h1BoundaryTrace hb hL hγ (h1Constant hb c) =
      Lp.const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c := by
  obtain ⟨f, hfu, hf⟩ := exists_smoothTraceTest_h1Constant hb hL.1.1 c
  rw [← hfu]
  apply Lp.ext
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f,
    Lp.coeFn_const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c,
    ae_restrict_mem measurableSet_Ioc] with θ htrace hconst hθ
  have hmem :=
    frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ (Ioc_subset_Icc_self hθ))
  simp_all

end

/-- A boundary constant vanishes as an L² class exactly when its value is
zero; the ordinary parameter interval has positive measure. -/
theorem boundaryLpConst_eq_zero_iff (c : ℂ) :
    Lp.const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c = 0 ↔ c = 0 := by
  haveI : NeZero (volume.restrict (Ioc (0 : ℝ) (2 * π))) := ⟨by simp [Real.volume_Ioc, sub_zero] <;> positivity⟩
  constructor
  · intro hc
    have h : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * π)), c = 0 := by
      filter_upwards [Lp.coeFn_const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c,
        Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) (2 * π)))] with θ hconst hzero
      simp_all
    obtain ⟨_, hc0⟩ := h.exists
    assumption
  tauto

/-- The entire actual zero form kernel consists of the genuine constants. -/
theorem h1HelmholtzForm_zero_eq_zero_iff_constant {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω 0 u = 0 ↔ ∃ c : ℂ, u = h1Constant hb c := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := (mem_neumannEigenspace_zero_iff hΩ (h1Value Ω u)).mp
      (h1HelmholtzForm_kernel_mem Ω 0 u hu)
    refine ⟨c, h1Value_injective hΩ.1 ?_⟩
    assumption
  · rintro ⟨c, rfl⟩
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, inner_zero_right]
    simp

end PolyaNeumann

end
