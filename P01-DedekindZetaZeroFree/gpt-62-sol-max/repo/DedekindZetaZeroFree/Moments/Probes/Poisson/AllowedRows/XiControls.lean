module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowKernel
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.ExceptionalPrefix
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.RightHalfPlane
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRowCount
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.MaximalSieve
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.CountCore
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDisks
public import DedekindZetaZeroFree.Analysis.Complex.ThreeCircles
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.EulerBounds
public import DedekindZetaZeroFree.Analysis.ContourIntegration.KernelWeightIntegration
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelHolomorphy
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConductorNormalization
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConvexityData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowXiControls

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions Set Filter Complex
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def DecayOn (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C T0 : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-B)

theorem verticalIntegral_eq_of_decayOn {a b : ℝ} {f : ℂ → ℂ} (hab : a < b)
    (hf : DifferentiableOn ℂ f (comparisonClosedStrip a b)) (hdec : DecayOn f a b) :
    comparisonVerticalIntegral b f = comparisonVerticalIntegral a f := by
  obtain ⟨C, T0, hbound⟩ := hdec 2 (by norm_num)
  set m : ℝ := (a + b) / 2 with hm
  have ham : a < ((m : ℂ)).re := by simp [hm]; linarith
  have hmb : ((m : ℂ)).re < b := by simp [hm]; linarith
  have hnb : comparisonClosedStrip a b ∈ 𝓝 (m : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a < (m : ℂ).re ∧ (m : ℂ).re < b from ⟨ham, hmb⟩))
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hcont := (hf.differentiableAt hnb).continuousAt
  have hres : Tendsto (fun z : ℂ => (z - (m : ℂ)) * f z) (𝓝[≠] (m : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => (z - (m : ℂ)) * f z) (𝓝 (m : ℂ)) (𝓝 ((m - m : ℂ) * f m)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hcont).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have := SimplePoleVerticalShift.verticalIntegral_sub_eq_residue_of_decay ham hmb
    (hf.mono diff_subset) hres C T0
    (fun x hx y hy => by simpa [Real.rpow_neg_natCast] using hbound x hx y hy)
  linear_combination this


















end

end DedekindZetaZeroFree.Quantitative.LowRowXiControls
