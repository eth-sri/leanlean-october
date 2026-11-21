module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.PlaceProjection
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.GlobalGreenIdentity
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.SmoothTestDensity
public import DedekindZetaZeroFree.Analysis.OperatorTheory.Resolvents.ShiftedPencilHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorFriedrichsSynthesis

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem placePair_descends (W Z : T_U F ζ hζ U R P H) (i : Fin (d F)) :
    ∃! p : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ,
      Measurable p ∧ ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
        p (q a x.val) = ∑ k : Fin 3,
          inner ℂ (coefficient W.val a x (i, k)) (coefficient Z.val a x (i, k)) := by
  let v := KPContActualCotangentPlaceProjection.project i W.val
  let w := KPContActualCotangentPlaceProjection.project i Z.val
  have heq : ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
      inner ℂ (coefficient v a x) (coefficient w a x) = ∑ k : Fin 3,
        inner ℂ (coefficient W.val a x (i, k)) (coefficient Z.val a x (i, k)) := by
    intro a x
    simp only [v, w, PiLp.inner_apply, Fintype.sum_prod_type,
      KPContActualCotangentPlaceProjection.coefficient_project]
    simp
  obtain ⟨p, hp, huniq⟩ := pairing_descends v w
  refine ⟨p, ⟨hp.1, fun a x => (hp.2 a x).trans (heq a x)⟩, ?_⟩
  intro p' hp'
  apply huniq p'
  exact ⟨hp'.1, fun a x => (hp'.2 a x).trans (heq a x).symm⟩

def placePair (W Z : T_U F ζ hζ U R P H) (i : Fin (d F)) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ :=
  Classical.choose (placePair_descends W Z i)

private theorem exists_actual_lift (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  let C := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hB := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H C
  have hx : x ∈ ⋃ n, KPContActualCotangentBorelRefinement.basePiece C n := by
    rw [hB.covers]
    exact Set.mem_univ x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := Set.mem_range.mp (hB.base_subset n hn)
  refine ⟨C.chart n, KPContActualCotangentPieceHilbertSum.coordinates (C.chart n) y, ?_⟩
  have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k
    simp [labeledA, labeledAInv]
  simpa only [q, KPContActualCotangentCountableShrinking.ShrunkChart.toBase,
    KPContActualCotangentPieceHilbertSum.coordinates, Subtype.coe_mk, hi] using hy



variable (F ζ hζ)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (U R) (hR : R.adelicHaar = μG) (P H)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

def scalarInjective : Function.Injective
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) :=
  (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization).iota_injective

def cotangentInjective : Function.Injective
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) :=
  (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization).j_injective

def A_U : KPContSectorClosedLpSubspace.H F ζ hζ R U →ₗ.[ℂ]
    KPContActualSectorCotangentL2.V F ζ hζ U R P H :=
  KPTestOperator.descend (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (scalarInjective F ζ hζ U R P H μG hμG hR realization)
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (D_U (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))

def scalarDense : DenseRange
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) :=
  (kp_cont_actual_sector_test_density F ζ hζ μG hμG U R hR P H realization).2.2.1

def cotangentDense : DenseRange
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) :=
  (kp_cont_actual_sector_test_density F ζ hζ μG hμG U R hR P H realization).2.2.2

def green : ∀ (f : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    inner ℂ (j (D_U f)) (j W) = inner ℂ (iota f) (iota (δ_U W)) :=
  kp_cont_actual_sector_global_green F ζ hζ μG hμG U R hR P H realization

def B_U : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  KPTestFriedrichs.resolvent (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (scalarInjective F ζ hζ U R P H μG hμG hR realization)
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (cotangentInjective F ζ hζ U R P H μG hμG hR realization)
    D_U δ_U (cotangentDense F ζ hζ U R P H μG hμG hR realization)
    (green F ζ hζ U R P H μG hμG hR realization)

def Δ_U : KPContSectorClosedLpSubspace.H F ζ hζ R U →ₗ.[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  KPTestFriedrichs.laplacian (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (scalarInjective F ζ hζ U R P H μG hμG hR realization)
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (cotangentInjective F ζ hζ U R P H μG hμG hR realization)
    D_U δ_U (scalarDense F ζ hζ U R P H μG hμG hR realization)
    (cotangentDense F ζ hζ U R P H μG hμG hR realization)
    (green F ζ hζ U R P H μG hμG hR realization)

run_cmd Lean.Elab.Command.liftCoreM do
  Lean.executeReservedNameAction
    ``DedekindZetaZeroFree.KPContActualSectorFriedrichsSynthesis.Δ_U.congr_simp
  unless (← Lean.getEnv).contains
      ``DedekindZetaZeroFree.KPContActualSectorFriedrichsSynthesis.Δ_U.congr_simp do
    throwError "The original Δ_U simplifier congruence theorem was not generated"

local notation "A" => A_U F ζ hζ U R P H μG hμG hR realization
local notation "B" => B_U F ζ hζ U R P H μG hμG hR realization
local notation "Δ" => Δ_U F ζ hζ U R P H μG hμG hR realization

abbrev formDomain := (A).closure.domain

abbrev energy (u : formDomain F ζ hζ U R P H μG hμG hR realization) : ℝ :=
  closedGradientEnergy A u

theorem test_mem_formDomain (f : S_U F ζ hζ U R P H) : iota f ∈ (A).closure.domain := by
  apply (A).le_closure.1
  exact LinearMap.mem_range_self iota f

def formTest (f : S_U F ζ hζ U R P H) : formDomain F ζ hζ U R P H μG hμG hR realization :=
  ⟨iota f, test_mem_formDomain F ζ hζ U R P H μG hμG hR realization f⟩

theorem placePair_chart (W Z : T_U F ζ hζ U R P H) (i : Fin (d F))
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    placePair W Z i (q a x.val) = ∑ k : Fin 3,
      inner ℂ (coefficient W.val a x (i, k)) (coefficient Z.val a x (i, k)) := by
  exact (Classical.choose_spec (placePair_descends W Z i)).1.2 a x



structure Properties : Prop where
  gradient_dense : Dense ((A).domain : Set (KPContSectorClosedLpSubspace.H F ζ hζ R U))
  gradient_closable : (A).IsClosable
  form_hilbert : CompleteSpace (ClosedGradientSpace A)
  form_core : ∀ u : (A).closure.domain, ∃ s : ℕ → S_U F ζ hζ U R P H,
    Filter.Tendsto (fun n => iota (s n)) Filter.atTop
      (nhds (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)) ∧
    Filter.Tendsto (fun n => j (D_U (s n))) Filter.atTop (nhds ((A).closure u)) ∧
    Filter.Tendsto (fun n => ‖j (D_U (s n))‖ ^ 2) Filter.atTop
      (nhds (closedGradientEnergy A u))
  laplacian_dense : Dense ((Δ).domain : Set (KPContSectorClosedLpSubspace.H F ζ hζ R U))
  laplacian_closed : (Δ).IsClosed
  laplacian_selfadjoint : IsSelfAdjoint Δ
  laplacian_nonnegative : ∀ u : (Δ).domain,
    0 ≤ (inner ℂ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ((Δ) u)).re
  genuine_inverse : KPResolventPencil.GenuineInverse Δ (-1) B
  variational : ClosedGradientVariationalAssociation A Δ
  test_mem_laplacian : ∀ f : S_U F ζ hζ U R P H, iota f ∈ (Δ).domain
  test_laplacian : ∀ f : S_U F ζ hζ U R P H,
    (Δ) ⟨iota f, test_mem_laplacian f⟩ = iota (δ_U (D_U f))

end DedekindZetaZeroFree.KPContActualSectorFriedrichsSynthesis

namespace DedekindZetaZeroFree

private theorem genuineInverse_of_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E →ₗ.[ℂ] E) (B : E →L[ℂ] E)
    (hl : ∀ f : E, ∃ hf : B f ∈ L.domain, B f + L ⟨B f, hf⟩ = f)
    (hr : ∀ u : L.domain, B ((u : E) + L u) = (u : E)) :
    KPResolventPencil.GenuineInverse L (-1) B := by
  refine ⟨fun f => (hl f).choose, ?_, ?_⟩
  · intro f
    simpa only [neg_smul, one_smul, sub_neg_eq_add] using
      (add_comm (L ⟨B f, _⟩) (B f)).trans (hl f).choose_spec
  · intro u
    simpa only [neg_smul, one_smul, sub_neg_eq_add] using
      (congrArg B (add_comm (L u) (u : E))).trans (hr u)

set_option maxHeartbeats 2000000

theorem kp_cont_actual_sector_friedrichs_synthesis
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorFriedrichsSynthesis.Properties F ζ hζ U R P H μG hμG hR realization := by
  let ι := KPContActualSectorTestEmbeddings.iota (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (H := H)
  let j := KPContActualSectorTestEmbeddings.j (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (H := H)
  let D := KPContActualSectorTestDifferentialDescent.D_U (F := F) (ζ := ζ)
    (hζ := hζ) (U := U) (H := H)
  let δ := KPContActualSectorTestDifferentialDescent.δ_U (F := F) (ζ := ζ)
    (hζ := hζ) (U := U) (H := H)
  let hι := KPContActualSectorFriedrichsSynthesis.scalarInjective
    F ζ hζ U R P H μG hμG hR realization
  let hj := KPContActualSectorFriedrichsSynthesis.cotangentInjective
    F ζ hζ U R P H μG hμG hR realization
  let hs := KPContActualSectorFriedrichsSynthesis.scalarDense
    F ζ hζ U R P H μG hμG hR realization
  let ht := KPContActualSectorFriedrichsSynthesis.cotangentDense
    F ζ hζ U R P H μG hμG hR realization
  let hg := KPContActualSectorFriedrichsSynthesis.green
    F ζ hζ U R P H μG hμG hR realization
  let A := KPTestOperator.descend (S := KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (T := KPContActualSectorSmoothTestModules.T_U F ζ hζ U R P H) ι hι j D
  let B := KPTestFriedrichs.resolvent (S := KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (T := KPContActualSectorSmoothTestModules.T_U F ζ hζ U R P H) ι hι j hj D δ ht hg
  let Δ := KPTestFriedrichs.laplacian (S := KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (T := KPContActualSectorSmoothTestModules.T_U F ζ hζ U R P H) ι hι j hj D δ hs ht hg
  obtain ⟨ha, hc, _, _, hcomplete, _, _, hcore, _, _, hself, hclosed,
    hnonneg, hvar, htest, _, _, _, hbdense, hleft, hright⟩ :=
    KPTestFriedrichs.hilbert_laplacian (S := KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (T := KPContActualSectorSmoothTestModules.T_U F ζ hζ U R P H) ι hι j hj D δ hs ht hg
  have hrange : Set.range B = (Δ.domain : Set _) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨f, rfl⟩
      exact (hleft f).choose
    · intro u hu
      exact ⟨u + Δ ⟨u, hu⟩, hright ⟨u, hu⟩⟩
  have htestmem : ∀ f, ι f ∈ Δ.domain := fun f =>
    (htest ⟨ι f, LinearMap.mem_range_self ι f⟩).choose
  refine {
    gradient_dense := ha
    gradient_closable := hc
    form_hilbert := hcomplete
    form_core := ?_
    laplacian_dense := hrange ▸ hbdense
    laplacian_closed := hclosed
    laplacian_selfadjoint := hself
    laplacian_nonnegative := hnonneg
    genuine_inverse := genuineInverse_of_sum Δ B hleft hright
    variational := hvar
    test_mem_laplacian := htestmem
    test_laplacian := ?_ }
  · intro u
    obtain ⟨s, h1, h2, h3⟩ := hcore u
    refine ⟨fun n => KPTestOperator.representative ι hι (s n), ?_, ?_, ?_⟩
    · change Filter.Tendsto (fun n => ι (KPTestOperator.representative ι hι (s n))) _ _
      convert h1 using 1
      funext n
      exact KPTestOperator.image_representative ι hι (s n)
    · change Filter.Tendsto (fun n => A (s n)) _ _
      exact h2
    · change Filter.Tendsto (fun n => ‖A (s n)‖ ^ 2) _ _
      exact h3
  · intro f
    have heq := (htest ⟨ι f, LinearMap.mem_range_self ι f⟩).choose_spec
    change Δ ⟨ι f, htestmem f⟩ = ι (δ (D f))
    change Δ ⟨ι f, _⟩ = ι (δ (D (KPTestOperator.representative ι hι ⟨ι f, _⟩))) at heq
    rw [KPTestOperator.representative_image] at heq
    exact heq

end DedekindZetaZeroFree

end
