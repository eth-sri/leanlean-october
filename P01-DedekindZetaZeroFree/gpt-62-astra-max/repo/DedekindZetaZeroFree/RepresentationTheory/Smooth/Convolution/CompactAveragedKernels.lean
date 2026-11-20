module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactConjugationInvariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.AveragedKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.TaylorJets

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

open MeasureTheory Filter Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open _root_.DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting (projective_t2)
local instance : T2Space (Matrix.ProjGenLinGroup (Fin 2) ℂ) := projective_t2

local instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change LocallyCompactSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

local instance : LocallyCompactSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  infer_instance
local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
  change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
  infer_instance
local instance : SecondCountableTopology ((Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
local instance : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : SecondCountableTopology (Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  infer_instance
local instance : LocallyCompactSpace (L F) :=
  @Pi.locallyCompactSpace_of_finite (NumberField.InfinitePlace F)
    (fun _ => Matrix.ProjGenLinGroup (Fin 2) ℂ) (fun _ => inferInstance)
    (fun _ => inferInstance) inferInstance
local instance : T2Space (L F) :=
  @Pi.t2Space (NumberField.InfinitePlace F)
    (fun _ => Matrix.ProjGenLinGroup (Fin 2) ℂ) (fun _ => inferInstance)
    (fun _ => inferInstance)
local instance : SecondCountableTopology (L F) :=
  @TopologicalSpace.instSecondCountableTopologyForallOfCountable (NumberField.InfinitePlace F)
    (fun _ => Matrix.ProjGenLinGroup (Fin 2) ℂ) inferInstance
    (fun _ => inferInstance) (fun _ => inferInstance)

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel (averaged_kernel_smooth)

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel (averaged_hasCompactSupport averaged_continuous conjugation_saturation_shrinks averaged_integrable_parameter averaged_conjugation_invariant averaged_mass)

def kappa (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) (μK : Measure D.K)
    (b : ContDiffBump (e0 F)) (a : L F) : ℝ :=
  ∫ k : D.K, eta F μL b
    ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val) ∂μK

theorem actual_compact_averaged_kernels
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (μK : Measure D.K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (b : ℕ → ContDiffBump (e0 F)) (hb : BumpSequence F μL b) :
  (∀ k : D.K, Measure.map
    (fun a : L F =>
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val) μL = μL) ∧
  ∀ m, Continuous (kappa F ζ hζ D μL μK (b m)) ∧
    KernelSmooth F (kappa F ζ hζ D μL μK (b m)) ∧
    HasCompactSupport (kappa F ζ hζ D μL μK (b m)) ∧
    ∀ (k : D.K) (a : L F), kappa F ζ hζ D μL μK (b m)
      ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val) =
      kappa F ζ hζ D μL μK (b m) a := by
  letI : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  letI : T2Space (G F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let π : D.K →* L F :=
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).comp D.K.subtype
  have hπ : Continuous π :=
    (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).2.comp continuous_subtype_val
  have hmap : ∀ k : D.K, Measure.map (fun a : L F => (π k)⁻¹ * a * π k) μL = μL :=
    CompactHaar.map_conjugation_compact π hπ μL
  refine ⟨hmap, fun m => ?_⟩
  obtain ⟨hc, hd, hs, _, _⟩ := hb.2.2.2.1 m
  exact ⟨averaged_continuous π hπ μK hc,
    averaged_kernel_smooth F μK π hπ (eta F μL (b m)) hd,
    averaged_hasCompactSupport π hπ μK hs,
    averaged_conjugation_invariant π μK (eta F μL (b m))⟩

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
