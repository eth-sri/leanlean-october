module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.EquivariantBorelGluing

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentPieceAeTransport

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing KPContActualCotangentMeasurableFamilies
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def coordinatePiece (cover : CountableCover F ζ hζ U R P H) (n : ℕ) :
    Set (omega (cover.chart n)) :=
  (fun y => q (cover.chart n) y.val) ⁻¹' basePiece cover n

structure Properties (cover : CountableCover F ζ hζ U R P H) : Prop where
  intrinsic : ∀ (f g : PieceSequence cover),
    (∀ n : ℕ, f.val n =ᵐ[(chartMeasure (cover.chart n)).restrict
      (coordinatePiece cover n)] g.val n) →
    AeEquivalent (G cover f) (G cover g)

 def coordHomeomorph : M F ≃ₜ KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := labeledA (placeEquiv F ζ hζ)
  invFun := labeledAInv (placeEquiv F ζ hζ)
  left_inv x := by simp [labeledAInv, labeledA]
  right_inv x := by funext k; simp [labeledAInv, labeledA]
  continuous_toFun := by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  continuous_invFun := by
    apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
    exact continuous_pi fun k => continuous_apply _

 def coordinateMeasure : Measure (M F) :=
  Measure.map (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))

private theorem lifted_formula (a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentOverlapNullEquivalence.liftedMeasure a =
      ((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ENNReal)) •
        (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) := by apply @DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence.OverlapMeasureNonsingularity.lifted_formula <;> assumption

private theorem lifted_absolutelyContinuous (a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentOverlapNullEquivalence.liftedMeasure a ≪
        (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) ∧
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) ≪
        KPContCotangentOverlapNullEquivalence.liftedMeasure a := by apply @DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence.OverlapMeasureNonsingularity.lifted_equivalent <;> assumption

private theorem rational_preserving (g : KPCuspArithmetic.PGL2 F) :
    MeasurePreserving (fun x => labeledAInv (placeEquiv F ζ hζ)
      (g • labeledA (placeEquiv F ζ hζ) x))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)) := by apply @DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence.OverlapMeasureNonsingularity.rational_preserving <;> assumption

private alias cast_fields := DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence.OverlapMeasureNonsingularity.cast_fields

private alias target_chart_fields := DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence.OverlapMeasureNonsingularity.target_chart_fields

private theorem arrow_psi_formula {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) :
    e.arrow.psi = fun x => labeledAInv (placeEquiv F ζ hζ)
      ((e.arrow.gamma : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x) := by
  obtain ⟨hb1, hb2⟩ := target_chart_fields a b e.component_eq
  funext x
  show labeledAInv (targetChart a b e.component_eq).places
      (((targetChart a b e.component_eq).kind.representative⁻¹ *
        e.arrow.gamma *
        (isotropyChart a).kind.representative) •
        labeledA (isotropyChart a).places x) = _
  rw [hb1, hb2, show (isotropyChart a).kind.representative = 1 from rfl,
    show (isotropyChart a).places = placeEquiv F ζ hζ from rfl]
  simp

private theorem psi_quasiMeasurePreserving {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) :
    Measure.QuasiMeasurePreserving e.arrow.psi
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)) := by
  rw [arrow_psi_formula e]
  exact (rational_preserving (F := F) (ζ := ζ) (hζ := hζ)
    (e.arrow.gamma : KPCuspArithmetic.PGL2 F)).quasiMeasurePreserving

private theorem labeledA_labeledAInv (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (z : KPCuspGenuineMonodromy.SymmetricSpace F) : labeledA p (labeledAInv p z) = z := by
  funext k
  simp [labeledAInv, labeledA]

alias AlmostEverywherePieceTransport.labeledA_labeledAInv := labeledA_labeledAInv

 def Qfun (i : Fin (H.atlas U).componentCount) :
    M F → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  fun x => KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)
    (KPCuspSiegel.projection F (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i)
      (labeledA (placeEquiv F ζ hζ) x))

private theorem q_eq_Qfun (a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentOverlapRationalBranches.q a = Qfun (F := F) (ζ := ζ) (hζ := hζ) (U := U)
      (R := R) (P := P) (H := H) a.component := rfl

private theorem branch_quotient_compatibility {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (x : M F) (hx : x ∈ e.arrow.domain) :
    KPContCotangentOverlapRationalBranches.q b (e.arrow.psi x)
      = KPContCotangentOverlapRationalBranches.q a x := by
  have hq : KPContCotangentOverlapRationalBranches.q b
      = KPContCotangentOverlapRationalBranches.q a := by
    simpa only [q_eq_Qfun] using congrArg (Qfun (F := F) (ζ := ζ) (hζ := hζ) (U := U)
      (R := R) (P := P) (H := H)) e.component_eq.symm
  rw [hq]
  have hpsi : e.arrow.psi x = labeledAInv (placeEquiv F ζ hζ)
      ((e.arrow.gamma : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x) := by
    rw [arrow_psi_formula e]
  rw [hpsi, KPContCotangentOverlapRationalBranches.q,
    KPContCotangentOverlapRationalBranches.q,
    labeledA_labeledAInv (placeEquiv F ζ hζ) _]
  congr 1
  exact Quotient.sound (show e.arrow.gamma •
      labeledA (placeEquiv F ζ hζ) x ∈
      MulAction.orbit (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
        (labeledA (placeEquiv F ζ hζ) x) from ⟨e.arrow.gamma, rfl⟩)

private theorem null_transfer {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (T : Set (M F)) (hT : T ⊆ omega b)
    (hT0 : (KPContCotangentOverlapNullEquivalence.liftedMeasure b).restrict (omega b) T = 0) :
    (KPContCotangentOverlapNullEquivalence.liftedMeasure a).restrict (omega a)
      (e.arrow.psi ⁻¹' T ∩ omega a) = 0 := by
  have hcoord : coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ) T = 0 := by
    have h2 := (lifted_absolutelyContinuous b).2 (by
      rw [← Measure.restrict_eq_self _ hT]; exact hT0)
    rwa [Measure.restrict_eq_self _ hT] at h2
  have h2 : (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a)
      (e.arrow.psi ⁻¹' T ∩ omega a) = 0 := by
    rw [Measure.restrict_eq_self _ (Set.inter_subset_right
       )]
    exact measure_mono_null Set.inter_subset_left ((psi_quasiMeasurePreserving e).preimage_null hcoord)
  rw [Measure.restrict_eq_self _ (Set.inter_subset_right
     )]
  exact (lifted_absolutelyContinuous a).1 h2

private alias continuous_labeledA_placeEquiv := DedekindZetaZeroFree.KPContActualCotangentExactMeasurableGluing.continuous_labeledA_placeEquiv

private theorem measurable_omega (a : ShrunkChart F ζ hζ U R P H) :
    MeasurableSet (omega a) :=
  a.domain_open.measurableSet.preimage continuous_labeledA_placeEquiv.measurable

alias AlmostEverywherePieceTransport.measurable_omega := measurable_omega

private alias measurable_q := DedekindZetaZeroFree.KPContActualCotangentExactMeasurableGluing.EquivariantBorelGluing.measurable_q

alias AlmostEverywherePieceTransport.measurable_q := measurable_q

private theorem T_proof_irrel {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (h h' : x ∈ ψ.domain) : T ψ x h = T ψ x h' := by
  simp

private theorem every_arrow_ae
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (cover : CountableCover F ζ hζ U R P H) (f : PieceSequence cover) (n : ℕ)
    (r : omega (cover.chart n) → E F)
    (hr : r =ᵐ[(chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)] f.val n)
    (a : ShrunkChart F ζ hζ U R P H) (ψ : ActualBranch a (cover.chart n)) :
    ∀ᵐ x ∂((chartMeasure a).restrict
      {x : omega a | x.val ∈ ψ.arrow.domain ∧ q a x.val ∈ basePiece cover n}),
      ∀ hx : x.val ∈ ψ.arrow.domain,
        coefficient (G cover f) a x =
          (T ψ.arrow x.val hx).symm (r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩) := by
  classical
  set N : Set (omega (cover.chart n)) := {y | r y ≠ f.val n y} with hNdef
  set Tset : Set (M F) := Subtype.val '' (N ∩ coordinatePiece cover n) with hTdef
  have hTnull : (KPContCotangentOverlapNullEquivalence.liftedMeasure (cover.chart n)).restrict
      (omega (cover.chart n)) Tset = 0 := by
    have h1 : (chartMeasure (cover.chart n)) (N ∩ coordinatePiece cover n) = 0 := by
      rw [← Measure.restrict_eq_self _ (Set.inter_subset_right
         )]
      exact (measure_mono_null Set.inter_subset_left (by
        rw [← MeasureTheory.ae_iff]; exact hr))
    have h2 : (chartMeasure (cover.chart n)) (N ∩ coordinatePiece cover n) =
        (KPContCotangentOverlapNullEquivalence.liftedMeasure (cover.chart n)).restrict
          (omega (cover.chart n)) Tset := by
      rw [chartMeasure,
        (MeasurableEmbedding.subtype_coe (measurable_omega (cover.chart n))).comap_apply]
    rw [← h2]; exact h1
  have hcomap : (chartMeasure a) (Subtype.val ⁻¹' (ψ.arrow.psi ⁻¹' Tset ∩ omega a)) = 0 := by
    rw [chartMeasure, (MeasurableEmbedding.subtype_coe (measurable_omega a)).comap_apply]
    have himg : (Subtype.val : omega a → M F) '' (Subtype.val ⁻¹' (ψ.arrow.psi ⁻¹' Tset ∩ omega a))
        = ψ.arrow.psi ⁻¹' Tset ∩ omega a := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy; exact ⟨⟨y, hy.2⟩, hy, rfl⟩
    rw [himg]; exact (null_transfer ψ Tset (by
      rintro _ ⟨y, -, rfl⟩; exact y.property) hTnull)
  have hSmeas : MeasurableSet
      {x : omega a | x.val ∈ ψ.arrow.domain ∧ q a x.val ∈ basePiece cover n} :=
    (ψ.arrow.isOpen_domain.measurableSet.preimage measurable_subtype_coe).inter
      (((kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).base_measurable n).preimage ((measurable_q a).comp measurable_subtype_coe))
  rw [MeasureTheory.ae_restrict_iff' hSmeas, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hcomap
  intro x hx
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
  rw [not_imp] at hx
  obtain ⟨hxS, hxQ⟩ := hx
  obtain ⟨hd, hq⟩ := hxS
  refine ⟨?_, x.property⟩
  refine ⟨⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩, ⟨?_, ?_⟩, rfl⟩
  · have hneq : r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩
        ≠ f.val n ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ := by
      intro heq
      push Not at hxQ
      obtain ⟨hx, hne⟩ := hxQ
      have h1 : coefficient (G cover f) a x =
          (T ψ.arrow x.val hd).symm (f.val n ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩) := by
        rw [show coefficient (G cover f) a x =
            coefficient (G cover f) a ⟨x.val, ψ.source_shrinking hd⟩ from
          congrArg (coefficient (G cover f) a) (Subtype.ext rfl)]
        exact ((kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ μG hμG U R hR P H cover).every_arrow f a n ψ x.val hd hq)
      have hTx := T_proof_irrel ψ.arrow x.val hx hd
      have heq' : r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ =
          f.val n ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ := by
        rw [show (⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ : omega (cover.chart n)) =
            ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩ from Subtype.ext rfl]
        exact heq
      exact hne (by
        rw [h1, ← hTx, show r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩ =
          r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ from
            congrArg r (Subtype.ext rfl), heq'])
    exact hneq
  · have hq' :=
      branch_quotient_compatibility ψ x.val hd
    change q (cover.chart n) (ψ.arrow.psi x.val) ∈ basePiece cover n
    rw [hq']; exact hq

private theorem all_charts_ae
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (cover : CountableCover F ζ hζ U R P H) (f g : PieceSequence cover)
    (hfg : ∀ n : ℕ, f.val n =ᵐ[(chartMeasure (cover.chart n)).restrict
      (coordinatePiece cover n)] g.val n)
    (a : ShrunkChart F ζ hζ U R P H) :
    coefficient (G cover f) a =ᵐ[chartMeasure a] coefficient (G cover g) a := by
  classical
  have hglue := kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ μG hμG U R hR P H cover
  have hAmeas : MeasurableSet
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} := by
    have heq : {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} =
        (fun x => (coefficient (G cover f) a x, coefficient (G cover g) a x)) ⁻¹'
          (Set.diagonal (E F))ᶜ := by
      ext x; simp [Set.mem_diagonal]
    rw [heq]
    exact isClosed_diagonal.isOpen_compl.measurableSet.preimage
      (Measurable.prod
        (hglue.chart_measurable f a) (hglue.chart_measurable g a))
  have hcell : ∀ p : ℕ × ℕ, (chartMeasure a).restrict
      {x : omega a | x.val ∈ cell cover a p.1 p.2}
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} = 0 := by
    rintro ⟨n, k⟩
    cases hb : (enumeration cover a n).branch k with
    | none =>
      have hempty : {x : omega a | x.val ∈ cell cover a n k} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        have h := cell_subset_domain cover a n k hx
        rw [hb] at h
        exact h
      rw [hempty, Measure.restrict_empty]
      simp
    | some e =>
      have hSe : MeasurableSet
          {x : omega a | x.val ∈ e.arrow.domain ∧ q a x.val ∈ basePiece cover n} :=
        (e.arrow.isOpen_domain.measurableSet.preimage measurable_subtype_coe).inter
          (((kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).base_measurable n).preimage ((measurable_q a).comp measurable_subtype_coe))
      have hSsub : {x : omega a | x.val ∈ cell cover a n k} ⊆
          {x : omega a | x.val ∈ e.arrow.domain ∧ q a x.val ∈ basePiece cover n} :=
        fun x hx => ⟨by
          have h := cell_subset_domain cover a n k hx
          rw [hb] at h
          exact h, hx.1⟩
      rw [← MeasureTheory.ae_iff]
      refine ae_restrict_of_ae_restrict_of_subset hSsub ?_
      refine (MeasureTheory.ae_restrict_iff' hSe).mpr ?_
      refine ((MeasureTheory.ae_restrict_iff' hSe).mp (every_arrow_ae μG hμG hR cover f n (g.val n) ((hfg n).symm) a e)).mono ?_
      intro x hx hxSe
      obtain ⟨hxd, hq⟩ := hxSe
      rw [hx ⟨hxd, hq⟩ hxd]
      exact ((congrArg (coefficient (G cover g) a) (Subtype.ext rfl)).symm.trans (hglue.every_arrow g a n e x.val hxd hq)).symm
  change ∀ᵐ x ∂chartMeasure a, coefficient (G cover f) a x = coefficient (G cover g) a x
  rw [MeasureTheory.ae_iff]
  have hcov : (⋃ p : ℕ × ℕ, {x : omega a | x.val ∈ cell cover a p.1 p.2}) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (by
      rw [(partition_properties cover).covers a]; exact x.property)
    exact Set.mem_iUnion.mpr ⟨p, hp⟩
  have hle : (chartMeasure a)
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} ≤
      ∑' p : ℕ × ℕ, (chartMeasure a).restrict {x : omega a | x.val ∈ cell cover a p.1 p.2}
        {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} := by
    calc _
        = (chartMeasure a) ({x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} ∩
            ⋃ p : ℕ × ℕ, {x : omega a | x.val ∈ cell cover a p.1 p.2}) := by
          rw [hcov, Set.inter_univ]
      _ ≤ ∑' p : ℕ × ℕ, (chartMeasure a)
            ({x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} ∩
              {x : omega a | x.val ∈ cell cover a p.1 p.2}) := by
          rw [Set.inter_iUnion]
          exact measure_iUnion_le _
      _ = ∑' p : ℕ × ℕ, (chartMeasure a).restrict {x : omega a | x.val ∈ cell cover a p.1 p.2}
            {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} := by
          refine tsum_congr fun p => ?_
          rw [Measure.restrict_apply hAmeas]
  refine le_antisymm (hle.trans_eq ?_) (by simp)
  simp [hcell]

end DedekindZetaZeroFree.KPContActualCotangentPieceAeTransport

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cotangent_piece_ae_transport
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentPieceAeTransport.Properties cover := by
  refine ⟨?_⟩
  · intro f g hfg
    exact (KPContActualCotangentMeasurableFamilies.aeEquivalent_iff_all_charts
      (KPContActualCotangentExactMeasurableGluing.G cover f)
      (KPContActualCotangentExactMeasurableGluing.G cover g)).mpr
      (fun a => KPContActualCotangentPieceAeTransport.all_charts_ae μG hμG hR cover f g hfg a)

end DedekindZetaZeroFree

end
