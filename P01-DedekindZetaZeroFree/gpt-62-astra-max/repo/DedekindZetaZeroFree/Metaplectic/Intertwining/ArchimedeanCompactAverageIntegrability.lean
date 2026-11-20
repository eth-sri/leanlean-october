module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.GaussChartBumps
public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactConjugationInvariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel
open MeasureTheory Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

theorem pgl_t2 : T2Space PGLComplex.Group := by
  let GeneralLinearGroup₀ := Matrix.GeneralLinearGroup (Fin 2) ℂ
  have hc : IsClosed (Subgroup.center (GeneralLinearGroup₀) :
      Set (GeneralLinearGroup₀)) := by
    have he : (Subgroup.center (GeneralLinearGroup₀) :
        Set (GeneralLinearGroup₀)) =
        ⋂ g : GeneralLinearGroup₀, {x | x * g = g * x} := by
      ext x
      simp [Subgroup.mem_center_iff]
      exact ⟨fun h g => (h g).symm, fun h g => (h g).symm⟩
    rw [he]
    exact isClosed_iInter fun g => isClosed_eq (continuous_mul_const g) (continuous_const_mul g)
  letI : IsClosed (Subgroup.center (GeneralLinearGroup₀) :
      Set (GeneralLinearGroup₀)) := hc
  infer_instance

theorem pgl_locallyCompact : LocallyCompactSpace PGLComplex.Group := by
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
    change LocallyCompactSpace (Fin 2 → Fin 2 → ℂ)
    infer_instance
  infer_instance

theorem pgl_secondCountable : SecondCountableTopology PGLComplex.Group := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  infer_instance

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
