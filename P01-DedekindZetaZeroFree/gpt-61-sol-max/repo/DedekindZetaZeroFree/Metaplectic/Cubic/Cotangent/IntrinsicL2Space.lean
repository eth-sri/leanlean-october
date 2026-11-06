module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.ChartZeroExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCotangentL2

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral
open KPContActualCotangentChartRestriction
open KPContActualCotangentChartZeroExtension
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def chosenCover : CountableCover F ζ hζ U R P H :=
  Classical.choice (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2

abbrev V := IntrinsicHilbert (chosenCover F ζ hζ U R P H)

abbrev muU := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U


local notation:max "current_V" => V F ζ hζ U R P H

abbrev intrinsicClass : current_V ≃ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) :=
  KPContActualCotangentIntrinsicHilbertIntegral.intrinsicClass (chosenCover F ζ hζ U R P H)


local notation:max "current_SquareFiniteFamily" => SquareFiniteFamily (U := U) (H := H)

def ofFamily : current_SquareFiniteFamily →ₗ[ℂ] current_V :=
  (intrinsicClass F ζ hζ U R P H).symm.toLinearMap.comp toAeQuotient


local notation:max "current_ofFamily" => ofFamily F ζ hζ U R P H

theorem ofFamily_surjective : Function.Surjective (current_ofFamily) := by
  exact (intrinsicClass F ζ hζ U R P H).symm.surjective.comp toAeQuotient_surjective

theorem ofFamily_eq_iff (r s : current_SquareFiniteFamily) :
    current_ofFamily r = current_ofFamily s ↔
      AeEquivalent r.val s.val := by
  change (intrinsicClass F ζ hζ U R P H).symm (toAeQuotient r) =
    (intrinsicClass F ζ hζ U R P H).symm (toAeQuotient s) ↔ _
  rw [(intrinsicClass F ζ hζ U R P H).symm.injective.eq_iff]
  exact toAeQuotient_eq_iff r s


local notation:max "current_ShrunkChart" => ShrunkChart F ζ hζ U R P H

def restriction (a : current_ShrunkChart) :
    current_V →L[ℂ] EuclideanQ a :=
  resEuclidean (chosenCover F ζ hζ U R P H) a

def zeroExtension (a : current_ShrunkChart) :
    EuclideanQ a →ₗᵢ[ℂ] current_V :=
  (ext (chosenCover F ζ hζ U R P H) a).comp (reindexQ a).symm.toLinearIsometry


local notation:max "current_restriction" => restriction F ζ hζ U R P H

structure Properties : Prop where

  intrinsic : KPContActualCotangentIntrinsicHilbertIntegral.Properties
    (chosenCover F ζ hζ U R P H)
  family_surjective : Function.Surjective (current_ofFamily)
  family_equality : ∀ r s : current_SquareFiniteFamily,
    current_ofFamily r = current_ofFamily s ↔ AeEquivalent r.val s.val
  all_chart_equality : ∀ r s : current_SquareFiniteFamily,
    current_ofFamily r = current_ofFamily s ↔
      ∀ a : current_ShrunkChart,
        ∀ᵐ x ∂chartMeasure a, coefficient r.val a x = coefficient s.val a x

  inner_integral : ∀ (v w : current_V)
      (r s : current_SquareFiniteFamily),
    current_ofFamily r = v → current_ofFamily s = w →
      inner ℂ v w = ∫ x, pair r.val s.val x ∂muU F ζ hζ U R P
  norm_integral : ∀ (v : current_V)
      (r : current_SquareFiniteFamily),
    current_ofFamily r = v →
      ‖v‖ ^ 2 = ∫ x, (normSquare r.val x : ℝ) ∂muU F ζ hζ U R P

  chart_pushforward : ∀ a : current_ShrunkChart,
    Measure.map a.toBase a.liftedMeasure = (muU F ζ hζ U R P).restrict a.baseDomain
  chart_normalization : ∀ a : current_ShrunkChart,
    a.liftedMeasure =
      ((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)) •
        Measure.comap (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F)
          ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain)
  restriction_closed : ∀ a : current_ShrunkChart,
    IsClosed (EuclideanQ a : Set (Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure))
  restriction_contraction : ∀ (a : current_ShrunkChart) (v : current_V),
    ‖restriction F ζ hζ U R P H a v‖ ≤ ‖v‖
  restriction_represented : ∀ (a : current_ShrunkChart)
      (v : current_V) (r : current_SquareFiniteFamily),
    current_ofFamily r = v →
      (fun y => (current_restriction a v :
        Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure) y) =ᵐ[a.liftedMeasure]
          (fun y => coefficientReindex (F := F) (localCoefficient a r.val y))
  restriction_inner : ∀ (a : current_ShrunkChart)
      (v w : current_V) (r s : current_SquareFiniteFamily),
    current_ofFamily r = v → current_ofFamily s = w →
      inner ℂ (current_restriction a v) (current_restriction a w) =
        ∫ x in a.baseDomain, pair r.val s.val x ∂muU F ζ hζ U R P
  restriction_norm : ∀ (a : current_ShrunkChart)
      (v : current_V) (r : current_SquareFiniteFamily),
    current_ofFamily r = v →
      ‖restriction F ζ hζ U R P H a v‖ ^ 2 =
        ∫ x in a.baseDomain, (normSquare r.val x : ℝ) ∂muU F ζ hζ U R P
  restriction_extension : ∀ (a : current_ShrunkChart) (f : EuclideanQ a),
    current_restriction a (zeroExtension F ζ hζ U R P H a f) = f
  extension_restriction : ∀ (a : current_ShrunkChart) (v : current_V),
    zeroExtension F ζ hζ U R P H a (current_restriction a v) =
      cutoff (chosenCover F ζ hζ U R P H) a v
  extension_adjoint : ∀ (a : current_ShrunkChart)
      (f : EuclideanQ a) (v : current_V),
    inner ℂ (zeroExtension F ζ hζ U R P H a f) v =
      inner ℂ f (current_restriction a v)
  extension_local_integral : ∀ (a : current_ShrunkChart)
      (f : EuclideanQ a) (v : current_V)
      (g : a.domain → EuclideanSpace ℂ (Fin (3 * d F)))
      (r : current_SquareFiniteFamily),
    MemLp g 2 a.liftedMeasure →
    g =ᵐ[a.liftedMeasure] (f : Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure) →
    current_ofFamily r = v →
      inner ℂ (zeroExtension F ζ hζ U R P H a f) v =
        ∫ y, inner ℂ (g y) (coefficientReindex (F := F) (localCoefficient a r.val y))
          ∂a.liftedMeasure

  measurable_extension : ∀ (a : current_ShrunkChart) (g : a.domain → E F)
      (hg : Measurable g) (he : PointwiseEquivariant a g) (hLp : MemLp g 2 a.liftedMeasure),
    ∃ v : current_V,
      v = current_ofFamily (extendedSquareFamily a g hg he hLp) ∧
      (fun y => (current_restriction a v :
        Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure) y) =ᵐ[a.liftedMeasure]
          (fun y => coefficientReindex (F := F) (g y)) ∧
      (∀ (b : current_ShrunkChart) (x : omega b),
        KPContCotangentOverlapRationalBranches.q b x.val ∉ a.baseDomain →
          extendedFields a g b x = 0)

  compact_continuous_extension : ∀ (a : current_ShrunkChart)
      (f : omega a → E F) (K : Set (M F)),
    IsCompact K → K ⊆ omega a → tsupport f ⊆ Subtype.val ⁻¹' K → Continuous f →
    PointwiseEquivariant a (liftField a f) →
      MemLp (liftField a f) 2 a.liftedMeasure ∧
      ∃ (qf : Q a) (r : current_SquareFiniteFamily),
        liftField a f =ᵐ[a.liftedMeasure] (qf : Lp (E F) 2 a.liftedMeasure) ∧
        current_ofFamily r =
          zeroExtension F ζ hζ U R P H a (reindexQ a qf) ∧
        (∀ b x, coefficient r.val b x = extendedFields a (liftField a f) b x) ∧
        tsupport (normSquare r.val) ⊆ KPContCotangentOverlapRationalBranches.q a '' K ∧
        (∀ b : current_ShrunkChart, Continuous (coefficient r.val b))

  transitions_unitary : ∀ (i : Fin (H.atlas U).componentCount)
      (a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i)
      (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v w : E F),
    inner ℂ (T ψ x hx v) (T ψ x hx w) = inner ℂ v w

  isotropy_fixed : ∀ (a : current_ShrunkChart) (x : M F)
      (hx : x ∈ (isotropyChart a).omega) (v : E F),
    v ∈ Fixed a x hx ↔ ∀ γ : Gamma a,
      (gammaMulAction a).smul γ x = x → T (isotropyArrow a γ) x hx v = v
  zero_isotropy_retained : ∀ (a : current_ShrunkChart) (x : M F)
      (hx : x ∈ (isotropyChart a).omega) (ε : rootsOfUnity 3 F),
    KPCuspGenuineMonodromy.central F ζ hζ ε ∈ U.toOpenSubgroup →
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) ≠ 1 → Fixed a x hx = ⊥

end DedekindZetaZeroFree.KPContActualSectorCotangentL2

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_cotangent_l2
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorCotangentL2.Properties F ζ hζ U R P H := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hI := kp_cont_actual_cotangent_intrinsic_hilbert_integral
    F ζ hζ μG hμG U R hR P H cover
  open KPContActualSectorCotangentL2 KPContActualCotangentChartRestriction
    KPContActualCotangentChartZeroExtension KPContActualCotangentIntrinsicHilbertIntegral
    KPContActualCotangentMeasurableFamilies KPContCotangentActualGenuineTwistIsotropy in
    refine
      { intrinsic := hI
        family_surjective := ofFamily_surjective F ζ hζ U R P H
        family_equality := ofFamily_eq_iff F ζ hζ U R P H
        all_chart_equality := ?_
        inner_integral := ?_
        norm_integral := ?_
        chart_pushforward := ?_
        chart_normalization := ?_
        restriction_closed := ?_
        restriction_contraction := ?_
        restriction_represented := ?_
        restriction_inner := ?_
        restriction_norm := ?_
        restriction_extension := ?_
        extension_restriction := ?_
        extension_adjoint := ?_
        extension_local_integral := ?_
        measurable_extension := ?_
        compact_continuous_extension := ?_
        transitions_unitary := ?_
        isotropy_fixed := ?_
        zero_isotropy_retained := ?_ }
  · intro r s
    exact (KPContActualSectorCotangentL2.ofFamily_eq_iff F ζ hζ U R P H r s).trans
      (KPContActualCotangentMeasurableFamilies.aeEquivalent_iff_all_charts r.val s.val)
  · intro v w r s hr hs
    exact hI.inner_integral v w r s hr hs
  · intro v r hr
    exact hI.norm_integral v r hr
  · intro a
    exact (KPContActualCotangentCountableShrinking.every_shrunkChart_properties
      F ζ hζ U R P H a).exact_pushforward
  · intro a
    exact KPContActualCotangentChartRestriction.original_normalization a
  · intro a
    exact KPMeasurableLocalL2.Q_isClosed
      (KPContActualCotangentChartRestriction.euclideanData a)
      (KPContActualCotangentChartRestriction.euclideanFullPiece a)
  · intro a v
    change ‖KPContActualCotangentChartRestriction.resEuclidean cover a v‖ ≤ ‖v‖
    rw [KPContActualCotangentChartRestriction.resEuclidean_norm]
    exact KPContActualCotangentChartRestriction.res_norm_le cover a v
  · intro a v r hr
    exact KPContActualCotangentChartRestriction.resEuclidean_represented cover a v r hr
  · intro a v w r s hr hs
    change inner ℂ
      (KPContActualCotangentChartRestriction.reindexQ a
        (KPContActualCotangentChartRestriction.res cover a v))
      (KPContActualCotangentChartRestriction.reindexQ a
        (KPContActualCotangentChartRestriction.res cover a w)) = _
    exact (LinearIsometryEquiv.inner_map_map (KPContActualCotangentChartRestriction.reindexQ a)
      (KPContActualCotangentChartRestriction.res cover a v)
      (KPContActualCotangentChartRestriction.res cover a w)).trans
        (KPContActualCotangentChartRestriction.res_inner_eq_integral cover a v w r s hr hs)
  · intro a v r hr
    change ‖KPContActualCotangentChartRestriction.resEuclidean cover a v‖ ^ 2 = _
    rw [KPContActualCotangentChartRestriction.resEuclidean_norm]
    exact KPContActualCotangentChartRestriction.res_norm_sq_eq_integral cover a v r hr
  · intro a f
    change KPContActualCotangentChartRestriction.reindexQ a
      (KPContActualCotangentChartRestriction.res cover a
        (KPContActualCotangentChartZeroExtension.ext cover a
          ((KPContActualCotangentChartRestriction.reindexQ a).symm f))) = f
    rw [KPContActualCotangentChartZeroExtension.res_ext, LinearIsometryEquiv.apply_symm_apply]
  · intro a v
    change KPContActualCotangentChartZeroExtension.ext cover a
      ((KPContActualCotangentChartRestriction.reindexQ a).symm
        (KPContActualCotangentChartRestriction.reindexQ a
          (KPContActualCotangentChartRestriction.res cover a v))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact KPContActualCotangentChartZeroExtension.ext_res cover a v
  · intro a f v
    change inner ℂ (KPContActualCotangentChartZeroExtension.ext cover a
      ((KPContActualCotangentChartRestriction.reindexQ a).symm f)) v =
      inner ℂ f (KPContActualCotangentChartRestriction.reindexQ a
        (KPContActualCotangentChartRestriction.res cover a v))
    rw [KPContActualCotangentChartZeroExtension.ext_inner]
    exact (LinearIsometryEquiv.inner_map_eq_flip
      (KPContActualCotangentChartRestriction.reindexQ a).symm f
      (KPContActualCotangentChartRestriction.res cover a v))
  · intro a f v g r hg hgf hr
    have hAdj : inner ℂ (KPContActualSectorCotangentL2.zeroExtension F ζ hζ U R P H a f) v =
        inner ℂ f (KPContActualSectorCotangentL2.restriction F ζ hζ U R P H a v) := by
      change inner ℂ (KPContActualCotangentChartZeroExtension.ext cover a
        ((KPContActualCotangentChartRestriction.reindexQ a).symm f)) v =
        inner ℂ f (KPContActualCotangentChartRestriction.reindexQ a
          (KPContActualCotangentChartRestriction.res cover a v))
      rw [KPContActualCotangentChartZeroExtension.ext_inner]
      exact (LinearIsometryEquiv.inner_map_eq_flip
        (KPContActualCotangentChartRestriction.reindexQ a).symm f
        (KPContActualCotangentChartRestriction.res cover a v))
    rw [hAdj]
    refine (KPMeasurableLocalL2.Q_inner_eq_integral
      (KPContActualCotangentChartRestriction.euclideanData a)
      (KPContActualCotangentChartRestriction.euclideanFullPiece a)
      f (KPContActualSectorCotangentL2.restriction F ζ hζ U R P H a v)).trans ?_
    apply integral_congr_ae
    filter_upwards [hgf,
      KPContActualCotangentChartRestriction.resEuclidean_represented cover a v r hr]
      with y hy hz
    exact congrArg₂ (inner ℂ) hy.symm hz
  · intro a g hg he hLp
    let r := KPContActualCotangentChartZeroExtension.extendedSquareFamily a g hg he hLp
    refine ⟨KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r, rfl, ?_, ?_⟩
    · have hres := KPContActualCotangentChartRestriction.resEuclidean_represented
        cover a (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r) r rfl
      filter_upwards [hres] with y hy
      exact hy.trans (congrArg (KPContActualCotangentChartRestriction.coefficientReindex (F := F))
        (KPContActualCotangentChartZeroExtension.extendedFields_source a g hg he y))
    · exact KPContActualCotangentChartZeroExtension.extendedFields_zero_off a g
  · intro a f K hK hKa hfK hc he
    refine ⟨KPContActualCotangentChartZeroExtension.compact_continuous_memLp
      a f K hK hKa hfK hc, ?_⟩
    obtain ⟨qf, r, hqf, hr, hcoef, hsupp, hcont⟩ :=
      KPContActualCotangentChartZeroExtension.compact_continuous_extension
        cover a f K hK hKa hfK hc he
    refine ⟨qf, r, hqf, ?_, hcoef, hsupp, hcont⟩
    change KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r =
      KPContActualCotangentChartZeroExtension.ext cover a
        ((KPContActualCotangentChartRestriction.reindexQ a).symm
          (KPContActualCotangentChartRestriction.reindexQ a qf))
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact hr
  · intro i a b ψ x hx v w
    exact KPContCotangentActualGenuineTwistIsotropy.T_inner ψ x hx v w
  · intro a x hx v
    exact KPContCotangentActualGenuineTwistIsotropy.mem_Fixed_iff a x hx v
  · intro a x hx ε hε hχ
    exact KPContCotangentActualGenuineTwistIsotropy.Fixed_eq_bot_of_central_phase a ε hε hχ x hx

end DedekindZetaZeroFree

end
