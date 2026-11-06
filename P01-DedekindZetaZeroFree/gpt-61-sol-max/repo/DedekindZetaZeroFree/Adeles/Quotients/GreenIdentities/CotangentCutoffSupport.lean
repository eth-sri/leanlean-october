module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.InteriorZeroExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualGlobalGreen

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualSectorTestDifferentialDescent
open KPContActualSectorFiniteSupportPartition
open KPContActualSectorSmoothTestModules
open KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem contDiff_labeledA :
    ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : M F => (CotangentLogCoframe.A (d F)) x) :=
    (CotangentLogCoframe.A (d F)).contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : KPArch.Space (d F) => fun k : Fin (KPCuspLogShape.dimension F) =>
        z ((placeEquiv F ζ hζ).symm k)) := by
    apply contDiff_pi.mpr
    intro k
    exact contDiff_apply ℝ KPArch.H3 ((placeEquiv F ζ hζ).symm k)
  exact h2.comp h1

def multiplierCutoff (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : IsSmoothMultiplier F ζ hζ U η) :
    RealSmoothCutoff F ζ hζ U R P H where
  val := η
  smooth := fun a =>
    ⟨fun x : M F =>
        η (Quotient.mk _
          (labeledA (placeEquiv F ζ hζ) x, (H.atlas U).representative a.component)),
      ((hη ((H.atlas U).representative a.component)).comp contDiff_labeledA).contDiffOn,
      fun _ => rfl⟩

theorem cotangentMultiply_support (η : RealSmoothCutoff F ζ hζ U R P H)
    (W : T_U F ζ hζ U R P H) :
    cotangentSupport ((cotangentMultiply η W).val) ⊆ tsupport η.val := by
  refine closure_minimal ?_ (isClosed_tsupport η.val)
  rintro x ⟨a, y, rfl, hy⟩
  have hlift : cutoffLift η a y ≠ 0 := by
    intro h
    exact hy (by rw [show coefficient (cotangentMultiply η W).val a y =
      cutoffLift η a y • coefficient W.val a y from rfl, h, zero_smul])
  have hval : η.val (q a y.val) ≠ 0 := by
    simpa [cutoffLift] using hlift
  exact subset_tsupport η.val hval

end DedekindZetaZeroFree.KPContActualGlobalGreen

namespace DedekindZetaZeroFree.KPContActualGlobalGreen

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentChartRestriction
open KPContActualCotangentPieceHilbertSum
open KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem q_coordinates (a : ShrunkChart F ζ hζ U R P H) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, q, coordinates]
  rw [hi]

theorem base_covered (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ShrunkChart F ζ hζ U R P H) (y : omega a), q a y.val = x := by
  obtain ⟨A⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hx : x ∈ ⋃ n, (A.chart n).baseDomain := by rw [A.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := hn
  exact ⟨A.chart n, coordinates (A.chart n) y, by rw [q_coordinates]; exact hy⟩

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent

open KPContActualSectorTestEmbeddings

theorem liftExtension_cutoff_tsupport (a : ShrunkChart F ζ hζ U R P H)
    (η : RealSmoothCutoff F ζ hζ U R P H)
    (L : KPCuspGenuineMonodromy.SymmetricSpace F → ℝ)
    (hL : tsupport L ⊆ a.domain)
    (hLq : ∀ x : omega a, L (labeledA (placeEquiv F ζ hζ) x.val) = η.val (q a x.val))
    (T : T_U F ζ hζ U R P H) :
    tsupport (liftExtension a (coefficient (cotangentMultiply η T).val a)) ⊆ omega a := by
  have hsub : Function.support (liftExtension a (coefficient (cotangentMultiply η T).val a))
      ⊆ labeledA (placeEquiv F ζ hζ) ⁻¹' tsupport L := by
    intro y hy
    have hyomega : y ∈ omega a := by
      by_contra h
      exact hy (by rw [liftExtension, dif_neg h])
    have hcoeff : coefficient (cotangentMultiply η T).val a ⟨y, hyomega⟩ ≠ 0 := by
      simpa [liftExtension, dif_pos hyomega] using hy
    have hη : η.val (q a y) ≠ 0 := by
      intro h
      apply hcoeff
      rw [show coefficient (cotangentMultiply η T).val a ⟨y, hyomega⟩
        = cutoffLift η a ⟨y, hyomega⟩ • coefficient T.val a ⟨y, hyomega⟩ from rfl]
      rw [show cutoffLift η a ⟨y, hyomega⟩ = ((η.val (q a y) : ℝ) : ℂ) from rfl, h]
      simp
    have hLq' := hLq ⟨y, hyomega⟩
    simp only [Subtype.coe_mk] at hLq'
    exact subset_tsupport L (Function.mem_support.mpr (by rw [hLq']; exact hη))
  refine (closure_minimal hsub ?_).trans ?_
  · exact (isClosed_tsupport L).preimage continuous_labeledA_actual
  · intro x hx
    exact hL hx

end DedekindZetaZeroFree.KPContActualGlobalGreen

end
