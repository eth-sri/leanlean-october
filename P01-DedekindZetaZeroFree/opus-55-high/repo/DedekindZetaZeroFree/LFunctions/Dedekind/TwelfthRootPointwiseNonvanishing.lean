module

public import DedekindZetaZeroFree.LFunctions.Dedekind.FiniteEulerRestoration
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.CauchyIntegral
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.MellinConverseAxisInversion
public import DedekindZetaZeroFree.Nonvanishing.Mellin.HolomorphicZeroTransfer
public import DedekindZetaZeroFree.Moments.Comparison.FarDyadSummability
public import DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel
public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ShiftedKernelFlatness
public import DedekindZetaZeroFree.Nonvanishing.Mellin.TripleMellinInitialEstimates
public import DedekindZetaZeroFree.LFunctions.Hecke.FiniteEulerFactorNonvanishing
public import DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalMu12Pointwise

theorem trivial_modulus_arithmetic_data_exists
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    ∃ S : SArithmeticData F, S.zeta12 = ζ ∧ S.modulus = ⊤ := by
  classical
  have h6 : (Ideal.span {(6 : 𝓞 F)} : Ideal (𝓞 F)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (show (6 : ℚ) ≠ 0 by norm_num)
  refine ⟨{
    zeta12 := ζ
    primitive_zeta12 := hζ
    Sf := (Ideal.finite_factors h6).toFinset
    S₀ := ∅
    bad_subset := Finset.empty_subset _
    modulus := ⊤
    modulus_ne_zero := ?_
    above_six := ?_
    modulus_support := ?_ }, rfl, rfl⟩
  · intro h
    have hmem : (1 : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := by rw [← h]; exact Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp hmem)
  · intro v hv
    rw [Set.Finite.mem_toFinset]
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_iff_mem v.asIdeal |>.mpr hv)
  · intro v hv
    exact absurd (top_le_iff.mp hv) v.isPrime.ne_top

end DedekindZetaZeroFree.PrincipalMu12Pointwise

end

section

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
