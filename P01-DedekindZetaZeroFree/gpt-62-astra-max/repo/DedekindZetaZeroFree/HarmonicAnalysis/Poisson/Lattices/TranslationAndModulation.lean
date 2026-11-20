module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.Lattices.ShiftedSummation

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem temperateGrowth_fourierChar_inner (b : V) :
    (fun x : V => (𝐞 (inner ℝ x b) : ℂ)).HasTemperateGrowth := by
  have h2 : (fun x : V => (2 * Real.pi * inner ℝ x b : ℝ)).HasTemperateGrowth := by fun_prop
  solve_by_elim [Complex.hasTemperateGrowth_exp_mul_I.comp]

theorem fourier_smul_fourierChar [MeasurableSpace V] [BorelSpace V]
    (f : 𝓢(V, ℂ)) (b : V) :
    ∀ w : V, 𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : V => (𝐞 (inner ℝ x b) : ℂ)) f :
        V → ℂ)) w = 𝓕 (f : V → ℂ) (w - b) := by
  intro w
  simp [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with v
  rw [(SchwartzMap.smulLeftCLM_apply_apply (temperateGrowth_fourierChar_inner b) f v)]
  rw [Circle.smul_def, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 1
  rw [inner_sub_right]
  ring_nf

theorem summable_norm_modulated_schwartz_translate
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    Summable (fun v : L =>
      ‖𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))‖) := by
  simpa using summable_norm_schwartz_translate L f a

end

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V)

theorem summable_norm_shifted_fourier_schwartz_dual_lattice :
    Summable (fun w : dualLattice L =>
      ‖𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b)‖) := by
  simpa only [Circle.norm_smul, neg_add_eq_sub] using (summable_norm_fourier_schwartz_translate L f (-b))

theorem poisson_shift_modulation :
    (∑' v : L, 𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))) =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        ∑' w : dualLattice L,
          𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b) := by
  set g := SchwartzMap.smulLeftCLM ℂ (fun x : V => (𝐞 (inner ℝ x b) : ℂ)) f with hg
  trans ∑' v : L, g (a + (v : V))
  · exact tsum_congr fun v => Eq.symm (SchwartzMap.smulLeftCLM_apply_apply (temperateGrowth_fourierChar_inner b) f (a + ↑v))
  · rw [poisson_summation_lattice_shift L g a]
    congr 1
    apply tsum_congr
    intro w
    rw [fourier_smul_fourierChar f b (w : V)]

end DedekindZetaZeroFree.PoissonArch

end
