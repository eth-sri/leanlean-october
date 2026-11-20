module

public import DedekindZetaZeroFree.Adeles.Approximation.UniformConjugatedFiniteLevel
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.ArchimedeanRegularity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance finiteStageTopologicalGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance finiteStageT2Space : T2Space (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1

local instance finite_stage_approximation_borel_measurable (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance finiteStageApproximationBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

 section

variable (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ))) (μ : Measure K)
    [IsFiniteMeasure μ]

include hK in
theorem convolution_integrable (h : C(K, ℂ))
    (u : Functions F ζ hζ) (hu : Continuous u) (g : G F ζ hζ) :
    Integrable (fun k : K => h k * u (g * k.val)) μ := by
  let := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun k : K => h k * u (g * k.val)) :=
    h.continuous.mul (hu.comp (continuous_const.mul continuous_subtype_val))
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

 def convolutionLinearMap
    (u : Functions F ζ hζ) (hu : Continuous u) :
    C(K, ℂ) →ₗ[ℂ] Functions F ζ hζ where
  toFun h := compactConvolution F ζ hζ K μ h u
  map_add' h₁ h₂ := by
    ext g
    simp only [compactConvolution, ContinuousMap.add_apply, add_mul, Pi.add_apply]
    exact integral_add (convolution_integrable F ζ hζ K hK μ h₁ u hu g)
      (convolution_integrable F ζ hζ K hK μ h₂ u hu g)
  map_smul' c h := by
    ext g
    simp only [compactConvolution, ContinuousMap.smul_apply, smul_eq_mul,
      Pi.smul_apply, mul_assoc]
    exact integral_const_mul c _

end

section

variable (K : Subgroup (G F ζ hζ)) (μ : Measure K) (h : C(K, ℂ)) (u : Functions F ζ hζ)

private theorem convolution_rational_invariant
    (hu : ∀ γ g, u (rationalLift F ζ hζ γ * g) = u g) :
    ∀ γ g, compactConvolution F ζ hζ K μ h u (rationalLift F ζ hζ γ * g) =
      compactConvolution F ζ hζ K μ h u g := by
  intro γ g
  apply integral_congr_ae
  filter_upwards with k
  simp only [mul_assoc, hu]

private theorem convolution_central_character
    (hu : ∀ ε g, u (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) * u g) :
    ∀ ε g, compactConvolution F ζ hζ K μ h u
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) *
        compactConvolution F ζ hζ K μ h u g := by
  intro ε g
  simp only [compactConvolution, mul_assoc, hu]
  simp_rw [← mul_assoc, mul_comm (h _) (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ),
    mul_assoc]
  exact integral_const_mul _ _

end

private theorem convolution_continuous
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (h : C(K, ℂ))
    (u : Functions F ζ hζ) (hu : Continuous u) :
    Continuous (compactConvolution F ζ hζ K μ h u) := by
  let := isCompact_iff_compactSpace.mp hK
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support isCompact_univ
    ((h.continuous.comp continuous_snd).mul
      (hu.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))).continuousOn (fun _ _ _ hk => (hk (Set.mem_univ _)).elim)

private theorem representative_convolution_kfinite
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (h : C(K, ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K)
    (u : Functions F ζ hζ) (hu : Continuous u) :
    KFinite F ζ hζ K (compactConvolution F ζ hζ K μ h u) := by
  rw [TauCeti.representativeSubmodule_eq_span] at hh
  induction hh using Submodule.span_induction with
  | mem h hh =>
      obtain ⟨n, π, hπ, v, w, rfl⟩ := TauCeti.isRepresentative_iff.mp hh
      let : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let L := (convolutionLinearMap F ζ hζ K hK μ u hu).comp
        (TauCeti.ContRepresentation.matrixCoeffₛₗ π hπ v)
      refine ⟨L.range, Module.Finite.range L, ⟨w, rfl⟩, ?_⟩
      intro a f hf
      obtain ⟨w', rfl⟩ := hf
      refine ⟨(π a⁻¹).adjoint w', ?_⟩
      ext g
      change (∫ k : K, TauCeti.ContRepresentation.matrixCoeff π hπ v
        ((π a⁻¹).adjoint w') k * u (g * k.val) ∂μ) =
        ∫ k : K, TauCeti.ContRepresentation.matrixCoeff π hπ v w' k *
          u ((g * a.val) * k.val) ∂μ
      rw [← integral_mul_left_eq_self (fun k : K =>
        TauCeti.ContRepresentation.matrixCoeff π hπ v ((π a⁻¹).adjoint w') k *
          u (g * k.val)) a]
      apply integral_congr_ae
      filter_upwards with k
      have heq : TauCeti.ContRepresentation.matrixCoeff π hπ v ((π a⁻¹).adjoint w')
          (a * k) = TauCeti.ContRepresentation.matrixCoeff π hπ v w' k := by
        simp only [TauCeti.ContRepresentation.matrixCoeff_apply,
          ContinuousLinearMap.adjoint_inner_right]
        congr 1
        rw [← mul_apply_eq_comp, ← map_mul]
        simp
      rw [heq]
      simp only [Subgroup.coe_mul, mul_assoc]
  | zero =>
      refine ⟨⊥, inferInstance, ?_, ?_⟩
      · rw [Submodule.mem_bot]
        ext g
        simp [compactConvolution]
      · intro k v hv
        rw [Submodule.mem_bot] at hv ⊢
        rw [hv, map_zero]
  | add h₁ h₂ _ _ ih₁ ih₂ =>
      change KFinite F ζ hζ K ((convolutionLinearMap F ζ hζ K hK μ u hu) (h₁ + h₂))
      rw [map_add]
      obtain ⟨S, hS, hfS, hSinv⟩ := ih₁
      obtain ⟨T, hT, hvT, hTinv⟩ := ih₂
      let := hS
      let := hT
      refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup hfS hvT, ?_⟩
      intro k w hw
      obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hw
      exact Submodule.add_mem_sup (hSinv k s hs) (hTinv k t ht)
  | smul c h _ ih =>
      change KFinite F ζ hζ K ((convolutionLinearMap F ζ hζ K hK μ u hu) (c • h))
      rw [map_smul]
      obtain ⟨S, hS, hfS, hSinv⟩ := ih
      exact ⟨S, hS, S.smul_mem c hfS, hSinv⟩

theorem convolution_automorphic
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (h : C(K, ℂ))
    (u : Functions F ζ hζ) (hu : Automorphic F ζ hζ u) :
    Automorphic F ζ hζ (compactConvolution F ζ hζ K μ h u) := by
  refine ⟨?_, convolution_rational_invariant F ζ hζ K μ h u hu.2.1,
    convolution_central_character F ζ hζ K μ h u hu.2.2⟩
  refine ⟨convolution_continuous F ζ hζ K hK μ h u hu.1.1,
    compact_convolution_arch_regular F ζ hζ K hK μ h u hu.1, ?_⟩
  obtain ⟨U, hU⟩ := hu.1.2.2
  obtain ⟨V, hV⟩ := compact_uniform_conjugated_finite_level F ζ hζ
    (K : Set (G F ζ hζ)) hK U
  refine ⟨V, ?_⟩
  intro g a ha
  apply integral_congr_ae
  filter_upwards with k
  have hk := hV k.val k.property a ha
  have heq : (g * a) * k.val =
      (g * k.val) * (k.val⁻¹ * a * k.val) := by group
  rw [heq, hU (g * k.val) (k.val⁻¹ * a * k.val) hk]

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation

end
