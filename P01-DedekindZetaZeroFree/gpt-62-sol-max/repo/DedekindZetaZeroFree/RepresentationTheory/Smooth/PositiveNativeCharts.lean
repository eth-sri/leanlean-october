module

public import DedekindZetaZeroFree.Adeles.Archimedean.RightLieWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Adeles.Archimedean.RightFlowCharts
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open Filter KPGlobalResidualConstruction.RightFlowChart
open RightFrame.PullbackWords (directionalWord_map)

theorem word_reindex (w : List (Fin (groupDimension F)))
    (u : G F ζ hζ → ℂ) :
    actualRightWord F ζ hζ w u =
      (w.map (fun b => actualBasisReindex F (lieEnumeration F b))).foldr
        (fun b v => rightDerivative F ζ hζ b v) u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change actualRight F ζ hζ b (actualRightWord F ζ hζ w u) = _
    rw [ih]
    funext g
    change deriv (fun t : ℝ => _) 0 = deriv (fun t : ℝ => _) 0
    congr 1
    funext t
    rw [actual_frame_ray_eq_flow F]

theorem actual_rightWord_chart_realization :
    ∃ (O : Set (ArchCoordinates F))
      (fields : Fin (groupDimension F) → ArchCoordinates F → ArchCoordinates F),
      IsOpen O ∧ archBase F ∈ O ∧ O ⊆ archDomain F ∧
      (∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O) ∧
      ∀ (u : G F ζ hζ → ℂ),
        (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => u (g * archChart F ζ hζ x)) (archDomain F)) →
        ∀ (w : List (Fin (groupDimension F))) (g : G F ζ hζ) (x : ArchCoordinates F),
          x ∈ O → actualRightWord F ζ hζ w u (g * archChart F ζ hζ x) =
            RightFrame.PullbackWords.directionalWord fields w
              (fun y => u (g * archChart F ζ hζ y)) x := by
  obtain ⟨O, hOo, hb, hOD, hμ, _, hprod, _, _⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  let reindex := fun b => actualBasisReindex F (lieEnumeration F b)
  refine ⟨O, fun b => field F (reindex b), hOo, hb, hOD,
    fun b => field_smooth F (reindex b) O hOo hb hμ, ?_⟩
  intro u hu w g x hx
  rw [word_reindex, ← word_eq_foldr, ← directionalWord_map (field F) reindex w]
  exact word_in_chart F ζ hζ u O hOo hb hμ hprod (w.map reindex) g ((hu g).mono hOD) x hx

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart

end
