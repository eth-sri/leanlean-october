module

public import ClassFieldTheory.All

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations

namespace DedekindZetaZeroFree.PlaceTraceAdapter

private theorem absolute_trace_norm_le_one
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial) (a : AbsoluteValueExtension vK L)
    (x : a.1.Completion) (hx : ‖x‖ ≤ 1) :
    letI := AbsoluteValue.completionAlgebra vK a.1 a.2
    ‖Algebra.trace vK.Completion a.1.Completion x‖ ≤ 1 := by
  letI := AbsoluteValue.completionAlgebra vK a.1 a.2
  letI := completionModuleFinite vK hvK0 a
  have ht := Algebra.isIntegral_trace (L := vK.Completion) (isIntegral_over_baseCompletionIntegers_of_mem vK hvK hvK0 a hx)
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff).mp ht
  rw [← hz]
  exact z.property

theorem adic_trace_mem_integers
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = w})
    (x : W.1.adicCompletion L) (hx : x ∈ W.1.adicCompletionIntegers L) :
    letI := (finitePlaceAdicCompletionMap K L w W).toAlgebra
    Algebra.trace (w.adicCompletion K) (W.1.adicCompletion L) x ∈
      w.adicCompletionIntegers K := by
  classical
  obtain ⟨a, rfl⟩ := (finitePlaceExtensionEquivAbove w).surjective W
  letI : Algebra (w.adicCompletion K)
      ((finitePlaceExtensionCentre w a).adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L w
      (finitePlaceExtensionEquivAbove w a)).toAlgebra
  change x ∈ (finitePlaceExtensionCentre w a).adicCompletionIntegers L at hx
  letI := AbsoluteValue.completionAlgebra (HeightOneSpectrum.adicAbv K w) a.1 a.2
  let y := (finitePlaceExtensionAdicCompletionRingEquiv w a).symm x
  have hxy : finitePlaceExtensionAdicCompletionRingEquiv w a y = x :=
    RingEquiv.apply_symm_apply _ x
  have hy : ‖y‖ ≤ 1 := by
    have h := norm_le_one_of_mem_adicCompletionIntegers _ hx
    rw [← hxy, finitePlaceExtensionAdicCompletionRingEquiv_norm] at h
    apply (Real.rpow_le_rpow_iff (norm_nonneg y) zero_le_one
      (finitePlaceExtensionExponent_pos w a)).mp
    simpa using h
  have hc := Algebra.trace_eq_of_equiv_equiv
    (relativeFinitePlaceCompletionAlgEquiv w).toRingEquiv
    (finitePlaceExtensionAdicCompletionRingEquiv w a)
    (by
      apply RingHom.ext
      intro z
      change finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove w a)
        (relativeFinitePlaceCompletionAlgEquiv w z) =
        finitePlaceExtensionAdicCompletionRingEquiv w a
          (AbsoluteValue.completionMap (HeightOneSpectrum.adicAbv K w) a.1 a.2 z)
      rw [← finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap]
      change finitePlaceExtensionAdicCompletionRingEquiv w a
        (AbsoluteValue.completionMap (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm
            ((relativeFinitePlaceCompletionAlgEquiv w) z))) = _
      rw [AlgEquiv.symm_apply_apply]) y
  rw [hxy] at hc
  apply mem_adicCompletionIntegers_of_norm_le_one
  have hn := relativeFinitePlaceCompletionAlgEquiv_symm_norm w
    (Algebra.trace (w.adicCompletion K)
      ((finitePlaceExtensionCentre w a).adicCompletion L) x)
  change Algebra.trace (HeightOneSpectrum.adicAbv K w).Completion a.1.Completion y =
    (relativeFinitePlaceCompletionAlgEquiv w).symm
      (Algebra.trace (w.adicCompletion K)
        ((finitePlaceExtensionCentre w a).adicCompletion L) x) at hc
  rw [← hc] at hn
  exact hn ▸ (absolute_trace_norm_le_one (HeightOneSpectrum.adicAbv K w)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w) (RayClass.adicAbv_isNontrivial w)
    a y hy)

end DedekindZetaZeroFree.PlaceTraceAdapter

end
