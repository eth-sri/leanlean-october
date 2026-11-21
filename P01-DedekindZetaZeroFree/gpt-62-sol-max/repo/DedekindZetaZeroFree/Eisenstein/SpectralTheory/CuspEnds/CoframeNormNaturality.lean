module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.FriedrichsLaplacian

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.DifferentialCoframe

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCuspCoframeNaturality

open CotangentLogCoframe (differential_norm_isometry)

 def rationalCoordinates (F : Type) [Field F] [NumberField F]
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F))
    (σ : KPCuspArithmetic.PGL2 F) (x : HyperbolicChart.Space (KPContCotangentActualOverlap.d F)) :=
  KPContCotangentActualOverlap.labeledAInv places
    (σ • KPContCotangentActualOverlap.labeledA places x)

private theorem rational_smooth_metric (F : Type) [Field F] [NumberField F]
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F))
    (σ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (rationalCoordinates F places σ) ∧
      ∀ x v w, HyperbolicChart.metric (KPContCotangentActualOverlap.d F)
        (rationalCoordinates F places σ x) (fderiv ℝ (rationalCoordinates F places σ) x v)
        (fderiv ℝ (rationalCoordinates F places σ) x w) =
        HyperbolicChart.metric (KPContCotangentActualOverlap.d F) x v w := by
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  let n := KPContCotangentActualOverlap.d F
  let A := CotangentLogCoframe.A n
  let g := fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F (places k)).embedding B
  have he : rationalCoordinates F places σ = fun x => A.symm (KPArch.productAction n g (A x)) := by
    funext x
    rw [← hB]
    unfold rationalCoordinates KPContCotangentActualOverlap.labeledAInv
    rw [show Matrix.ProjGenLinGroup.mk B • KPContCotangentActualOverlap.labeledA places x =
      KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk B)
        (KPContCotangentActualOverlap.labeledA places x) from rfl, KPCuspSiegel.action_mk]
    congr 1
    funext k
    simp [KPCuspSiegel.glAction, KPArch.productAction, KPContCotangentActualOverlap.labeledA, g, A]
    rfl
  rw [he]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => A.symm (KPArch.productAction n g (A x))) :=
    A.symm.contDiff.comp (((KPArch.productAction_contDiff n g).of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp A.contDiff)
  refine ⟨hs, ?_⟩
  have hquad : ∀ x v, HyperbolicChart.metric n (A.symm (KPArch.productAction n g (A x)))
      (fderiv ℝ (fun x => A.symm (KPArch.productAction n g (A x))) x v)
      (fderiv ℝ (fun x => A.symm (KPArch.productAction n g (A x))) x v) =
      HyperbolicChart.metric n x v v := by
    intro x v
    have hder := A.symm.hasFDerivAt.comp x
      (((KPArch.productAction_contDiff n g).differentiable (by simp) (A x)).hasFDerivAt.comp x
        A.hasFDerivAt)
    change HasFDerivAt (fun x => A.symm (KPArch.productAction n g (A x))) _ x at hder
    rw [← CotangentLogCoframe.metric_A, hder.fderiv]
    change KPArch.metric n (A (A.symm (KPArch.productAction n g (A x))))
      (A ((A.symm.toContinuousLinearMap.comp
        ((fderiv ℝ (KPArch.productAction n g) (A x)).comp A.toContinuousLinearMap)) v)) = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    exact (KPArch.metric_invariant n g (A x) (A v)).trans (CotangentLogCoframe.metric_A n x v)
  have hpolar : ∀ x u w, HyperbolicChart.metric n x (u+w) (u+w) =
      HyperbolicChart.metric n x u u + 2 * HyperbolicChart.metric n x u w +
        HyperbolicChart.metric n x w w := by
    intro x u w
    simp only [← CotangentLogCoframe.inner_C, map_add, inner_add_left, inner_add_right,
      real_inner_comm (CotangentLogCoframe.C n x w) (CotangentLogCoframe.C n x u)]
    ring
  intro x v w
  have hp := hquad x (v+w)
  rw [map_add, hpolar, hpolar, hquad x v, hquad x w] at hp
  linarith

open KPContActualCotangentCountableShrinking KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches KPContCotangentActualGenuineTwistIsotropy
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem pairing_at_arch (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    (∑ j : Fin (d F), ∑ k : Fin 3,
      ‖HyperbolicChart.differential (d F)
        (fun x => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) x))
        (labeledAInv (placeEquiv F ζ hζ) y) j k‖ ^ 2) =
    (∑ j : Fin (d F), KPContActualSectorFriedrichsSynthesis.placePair (D_U f) (D_U f) j
      ((H.atlas U).components ⟨i, Quotient.mk _ y⟩)).re := by
  obtain ⟨a, hi, hcenter, hy⟩ := KPContActualCotangentCountableShrinking.Construction.shrink_exists (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i y
  let x := labeledAInv (placeEquiv F ζ hζ) y
  have hA : labeledA (placeEquiv F ζ hζ) x = y := by
    funext k
    simp [x, labeledA, labeledAInv]
  have hx : x ∈ omega a := by
    change labeledA (placeEquiv F ζ hζ) x ∈ a.domain
    rw [hA]; exact hy
  have hq : q a x = (H.atlas U).components ⟨i, Quotient.mk _ y⟩ := by
    rw [(H.atlas U).components_formula]
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x)) = _
    rw [hA, hi]
  have hopen : IsOpen (omega a) := by
    apply a.domain_open.preimage
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  have hsec : sectionFields (scalarSections f) = f.val :=
    (Classical.choose_spec (scalar_gluing f)).1.2.2
  have hgerm : liftExtension a (f.val a) =ᶠ[𝓝 x]
      (fun z => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) z)) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [liftExtension, dite_eq_left hz, ← hsec]
    simp only [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative,
      map_one, Units.val_one, one_mul, one_smul]
    rw [hi]
  have hcoeff : ∀ j k, coefficient (D_U f).val a ⟨x, hx⟩ (j,k) =
      HyperbolicChart.differential (d F)
        (fun z => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) z)) x j k := by
    intro j k
    change (CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a (f.val a)) x)) (j,k) = _
    rw [CotangentLogCoframe.j_apply]
    fin_cases k <;> simp only [HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, hgerm.fderiv_eq]
  rw [← hq]
  simp only [KPContActualSectorFriedrichsSynthesis.placePair_chart F ζ hζ U R P H
    (D_U f) (D_U f) _ a ⟨x,hx⟩, hcoeff, inner_self_eq_norm_sq_to_K]
  simp [x, ← Complex.ofReal_pow]

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

set_option linter.unusedVariables false in

theorem actual_cusp_coframe_placePair
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (c : KPMsFixedHaarDisintegration.CuspIndex (H.atlas U))
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    (∑ i : Fin (KPContCotangentActualOverlap.d F), ∑ k : Fin 3,
      ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F)
        (fun x => ((KPContActualSectorSmoothTestModules.scalarSections f) c.1).val
          (((H.atlas U).cuspAtlas c.1).representative c.2 •
            KPContCotangentActualOverlap.labeledA
              (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x))
        (KPContCotangentActualOverlap.labeledAInv
          (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
          (KPCuspCharts.toArch F (p, t))) i k‖ ^ 2) =
    (∑ i : Fin (KPContCotangentActualOverlap.d F),
      KPContActualSectorFriedrichsSynthesis.placePair
        (KPContActualSectorTestDifferentialDescent.D_U f)
        (KPContActualSectorTestDifferentialDescent.D_U f) i
        ((H.atlas U).components ⟨c.1, Quotient.mk _
          (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ U R P H c.1 c.2 (p, t))⟩)).re := by
  let places := placeEquiv F ζ hζ
  let σ := ((H.atlas U).cuspAtlas c.1).representative c.2
  let z := KPCuspCharts.toArch F (p,t)
  let x := labeledAInv places z
  let ψ := rationalCoordinates F places σ
  let g : M F → ℂ := fun x => (scalarSections f c.1).val (labeledA places x)
  have hA : ∀ y : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA places (labeledAInv places y) = y := by
    intro y
    funext k
    simp [labeledA, labeledAInv]
  have he : (fun x => (scalarSections f c.1).val (σ • labeledA places x)) = g ∘ ψ := by
    funext y
    change (scalarSections f c.1).val (σ • labeledA places y) =
      (scalarSections f c.1).val (labeledA places (labeledAInv places (σ • labeledA places y)))
    rw [hA]
  have hsm := rational_smooth_metric F places σ
  have hg : DifferentiableAt ℝ g (ψ x) := by
    have hsg : ContDiff ℝ (⊤ : ℕ∞) (scalarSections f c.1).val :=
      (Classical.choose_spec (scalar_gluing f)).1.1 c.1
    have hla : ContDiff ℝ (⊤ : ℕ∞) (labeledA places) := by
      apply contDiff_pi.mpr
      intro k
      exact (ContinuousLinearMap.proj (places.symm k) : KPArch.Space (d F) →L[ℝ] KPArch.H3).contDiff.comp
        (CotangentLogCoframe.A (d F)).contDiff
    exact (hsg.comp hla).differentiable (by simp) |>.differentiableAt
  have hn := differential_norm_isometry (d F) ψ x
    (hsm.1.differentiable (by simp) |>.differentiableAt) (hsm.2 x) g hg
  change (∑ i, ∑ k, ‖HyperbolicChart.differential (d F)
    (fun x => (scalarSections f c.1).val (σ • labeledA places x)) x i k‖ ^ 2) = _
  rw [he, hn]
  have hx : ψ x = labeledAInv places (σ • z) := by
    change labeledAInv places (σ • labeledA places (labeledAInv places z)) = _
    rw [hA]
  rw [hx]
  exact pairing_at_arch f c.1 (σ • z)

end DedekindZetaZeroFree.KPContCuspCoframeNaturality

end
