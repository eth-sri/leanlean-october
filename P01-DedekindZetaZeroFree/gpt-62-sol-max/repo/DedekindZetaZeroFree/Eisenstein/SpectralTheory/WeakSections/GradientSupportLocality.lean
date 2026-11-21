module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.SupportAndMultiplication
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology
set_option maxHeartbeats 1500000
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs KPContSectorLineL2Isometry
open KPContLocalNorm KPContSectorSmoothFramesSupport
open KPContActualCotangentCountableShrinking KPContCotangentActualGenuineTwistIsotropy
open KPContSectorPhaseComponentCharts
open KPContActualSectorCoordinateNullEquivalence KPContActualSectorFormWeakLocalization
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}



private theorem sectionFields_apply_actual (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ ((isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((isotropyChart a).kind.representative • labeledA (isotropyChart a).places x.val) := rfl
  rw [sectionFields, hcoe]
  simp [isotropyChart, KPContCotangentActualOverlap.ChartKind.representative]
private theorem lp_locallyIntegrable {n : ℕ} (B : LocalBall n) (u : BallL2 B) :
    LocallyIntegrableOn u B.carrier (volume.restrict B.carrier) := by
  apply (locallyIntegrableOn_iff (μ := volume.restrict B.carrier)
    (f := (fun x => u x)) (s := B.carrier) B.toOpens.isOpen.isLocallyClosed).2
  intro K hK hKc
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKc.measure_ne_top
  change Integrable _ ((volume.restrict B.carrier).restrict K)
  rw [Measure.restrict_restrict hKc.measurableSet, Set.inter_eq_left.mpr hK]
  exact ((Lp.memLp u).mono_measure (Measure.restrict_mono hK le_rfl)).integrable (by norm_num)
private theorem weakDerivative_zero {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u d : BallL2 B) (hu : u =ᵐ[volume.restrict B.carrier] (fun _ => 0))
    (hd : IsWeakDerivative B α u d) : ∀ᵐ x ∂volume.restrict B.carrier, d x = 0 := by
  have hi := lp_locallyIntegrable B d
  have hz : ∀ᵐ x ∂volume.restrict B.carrier, x ∈ B.carrier → d x = 0 := by
    apply B.toOpens.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hi
    intro φ hφ hφc hφs
    have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    have hsupp : tsupport (fun x => (φ x : ℂ)) = tsupport φ := by
      unfold tsupport; congr 1; ext x; simp
    let ψ : TestFunction B.toOpens ℂ ⊤ := ⟨fun x => (φ x : ℂ), hcast,
      by change IsCompact _; rw [hsupp]; exact hφc, hsupp ▸ hφs⟩
    have he : ∫ x in B.carrier, d x * ψ x = 0 := by
      apply mul_left_cancel₀ (pow_ne_zero α.degree (by norm_num : (-1 : ℂ) ≠ 0))
      rw [mul_zero, ← hd ψ]
      have h0 : (fun x => u x * coordinateDerivative α (fun y => ψ y) x) =ᵐ[volume.restrict B.carrier] (fun _ => 0) := by
        filter_upwards [hu] with x hx; rw [hx, zero_mul]
      rw [integral_congr_ae h0, integral_zero]
    simpa only [show (fun x => ψ x) = (fun x => (φ x : ℂ)) from rfl, Complex.real_smul, mul_comm] using he
  filter_upwards [hz, ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hx hxB
  exact hx hxB




end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end
