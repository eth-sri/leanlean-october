module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ArchimedeanMatrixParametrization
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalFiniteLevelSmooth
open KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge (matrixClass smooth_matrix_parametrization rightPolynomial rightPolynomial_smooth rightPolynomial_det)

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

variable (u : Cover F ζ hζ → ℂ) (hu : Smooth F ζ hζ u)

include hu in
private theorem native_chart_contDiffOn (g : Cover F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  intro x hx
  have hdet : ∀ w, (rightPolynomial x w).det ≠ 0 := by
    intro w
    rw [rightPolynomial_det]
    exact hx w
  apply (smooth_matrix_parametrization u hu g rightPolynomial x
    rightPolynomial_smooth.contDiffAt hdet).contDiffWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin] with y hy
    congr 2
    rw [KPLiteralChamber.right_insertion F ζ hζ y]
    congr 1
    funext w
    have hyw : (rightPolynomial y w).det ≠ 0 := by
      rw [rightPolynomial_det]
      exact hy w
    simp only [matrixClass, dite_eq_left hyw]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [KPLiteralChamber.rightMatrix_val _ (hy w)]
    rfl
  · exact hx

 include hu in
theorem upstairs_smooth_finiteLevel_rawSmooth
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : ∀ g a, a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U → u (g * a) = u g) :
    KPLiteralRaw.Smooth F ζ hζ u := ⟨hu.1, native_chart_contDiffOn u hu, U, hU⟩

end DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalFiniteLevelSmooth

end
