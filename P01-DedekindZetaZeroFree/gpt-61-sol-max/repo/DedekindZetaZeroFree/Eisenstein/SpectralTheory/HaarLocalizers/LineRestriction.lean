module

public import Mathlib

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section


noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev X_U := @_root_.DedekindZetaZeroFree.KPFiniteCuspAtlas.rawXU
abbrev H_U := KPContSectorClosedLpSubspace.H F ζ hζ R U
abbrev muU := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

 abbrev instTopologicalSpaceL2LineLocal  :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceL2LineLocal

 abbrev instAddCommMonoidL2LineLocal  :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidL2LineLocal

 abbrev instTopologicalSpaceHULocal  :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHULocal

variable (K : Set (X_U F ζ hζ U))

private theorem componentNorm_nonneg (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (b : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :
    0 ≤ componentNorm F ζ hζ U R P H s i b := by
  refine Quotient.inductionOn b (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  exact norm_nonneg _


local notation:max "current_sectionNorm" => sectionNorm F ζ hζ U R P H

 theorem sectionNorm_nonneg (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) : 0 ≤ current_sectionNorm s b := by
  simp only [sectionNorm]
  exact componentNorm_nonneg F ζ hζ U R P H s _ _


 alias sectionNorm_add_le := _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.sectionNorm_add_le

 alias sectionNorm_smul := _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.sectionNorm_smul


local notation:max "current_squaredNorm" => squaredNorm F ζ hζ U R P H

 theorem sectionNorm_zero_of_squaredNorm_ae
    {ν : Measure (X_U F ζ hζ U)} {s : Sections F ζ hζ U R P H}
    (h : current_squaredNorm s =ᵐ[ν] 0) :
    current_sectionNorm s =ᵐ[ν] 0 := by
  filter_upwards [h] with b hb
  simp only [Pi.zero_apply] at hb
  have hb' : current_sectionNorm s b ^ 2 ≤ 0 := by
    rw [squaredNorm, ENNReal.ofReal_eq_zero] at hb
    exact hb
  have hzero  :=
    le_antisymm hb' (sq_nonneg _)
  exact sq_eq_zero_iff.mp hzero

private alias sectionNorm_zero := _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.sectionNorm_zero

 alias squaredNorm_zero := _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.squaredNorm_zero


local notation:max "current_muU" => muU F ζ hζ U

def nullOnK : Submodule ℂ (BorelL2Sections F ζ hζ U R P H) where
  carrier := {s | current_squaredNorm s.val =ᵐ[
    (current_muU R P).restrict K] 0}
  zero_mem' := by
    change current_squaredNorm (0 : BorelL2Sections F ζ hζ U R P H).val =ᵐ[
      (current_muU R P).restrict K] 0
    rw [show (0 : BorelL2Sections F ζ hζ U R P H).val =
      (0 : Sections F ζ hζ U R P H) from rfl, squaredNorm_zero]
  add_mem' := by
    intro s t hs ht
    change current_squaredNorm (s + t).val =ᵐ[
      (current_muU R P).restrict K] 0
    rw [show (s + t).val = s.val + t.val from rfl]
    have hs' : current_squaredNorm s.val =ᵐ[
        (current_muU R P).restrict K] 0 := hs
    have ht' : current_squaredNorm t.val =ᵐ[
        (current_muU R P).restrict K] 0 := ht
    filter_upwards [sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H hs',
      sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H ht'] with b hbs hbt
    simp only [Pi.zero_apply] at hbs hbt
    have h1 : current_sectionNorm (s.val + t.val) b ≤
        current_sectionNorm s.val b + current_sectionNorm t.val b :=
      sectionNorm_add_le F ζ hζ U R P H s.val t.val b
    rw [hbs, hbt, add_zero] at h1
    have h2  :=
      sectionNorm_nonneg F ζ hζ U R P H (s.val + t.val) b
    have h3  := le_antisymm h1 h2
    simp [squaredNorm, h3]
  smul_mem' := by
    intro c s hs
    change current_squaredNorm (c • s).val =ᵐ[
      (current_muU R P).restrict K] 0
    rw [show (c • s).val = c • s.val from rfl]
    have hs' : current_squaredNorm s.val =ᵐ[
        (current_muU R P).restrict K] 0 := hs
    filter_upwards [sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H hs'] with b hb
    simp only [Pi.zero_apply] at hb
    have hsm := congrFun (sectionNorm_smul F ζ hζ U R P H c s.val) b
    simp [squaredNorm, hsm, hb]

local instance : HasQuotient (BorelL2Sections F ζ hζ U R P H)
    (Submodule ℂ (BorelL2Sections F ζ hζ U R P H)) :=
  @Submodule.hasQuotient ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance


local notation:max "current_nullOnK" => nullOnK F ζ hζ U R P H

abbrev H_K := (BorelL2Sections F ζ hζ U R P H) ⧸ current_nullOnK K


local notation:max "current_H_K" => H_K F ζ hζ U R P H

def mkK : BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] current_H_K K :=
  @Submodule.mkQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (current_nullOnK K)

 def maskCoeff (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) :
    KPFiniteCuspAtlas.SymmetricSpace F → ℂ :=
  fun x => K.indicator (fun _ => (s.val i).val x)
    ((H.atlas U).components ⟨i, Quotient.mk _ x⟩)

 theorem maskCoeff_scalarFiber (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    maskCoeff F ζ hζ U R P H K s i x ∈
      KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [maskCoeff, Set.indicator_of_mem hx]; exact (s.val i).property.1 x
  · rw [maskCoeff, Set.indicator_of_notMem hx]
    exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).zero_mem

 theorem maskCoeff_equivariant (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    maskCoeff F ζ hζ U R P H K s i ((γ : KPCuspArithmetic.PGL2 F) • x) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) *
        maskCoeff F ζ hζ U R P H K s i x := by
  have hq : (H.atlas U).components ⟨i, Quotient.mk _
        ((γ : KPCuspArithmetic.PGL2 F) • x)⟩ =
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩ := by
    have hq2 : (Quotient.mk _ ((γ : KPCuspArithmetic.PGL2 F) • x) :
        KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U
          ((H.atlas U).representative i))) = Quotient.mk _ x :=
      (Quotient.sound (MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, inv_smul_smul γ x⟩))).symm
    rw [hq2]
  rw [maskCoeff, maskCoeff, hq]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, (s.val i).property.2 γ x]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

private theorem measurable_maskCoeff (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) (i : Fin (H.atlas U).componentCount) :
    Measurable (maskCoeff F ζ hζ U R P H K s i) := by
  have hcont : Continuous (fun x : KPFiniteCuspAtlas.SymmetricSpace F =>
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩) :=
    (H.atlas U).components.continuous.comp
      (continuous_sigmaMk.comp (KPCuspSiegel.continuous_projection F _))
  have hset : MeasurableSet {x : KPFiniteCuspAtlas.SymmetricSpace F |
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K} := hK.preimage hcont.measurable
  have hfun : maskCoeff F ζ hζ U R P H K s i = fun x =>
      if (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K then (s.val i).val x else 0 := by
    rfl
  rw [hfun]
  exact Measurable.ite hset (s.property.1 i) measurable_const

 def maskSections (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    Sections F ζ hζ U R P H :=
  fun i => ⟨maskCoeff F ζ hζ U R P H K s i,
    ⟨maskCoeff_scalarFiber F ζ hζ U R P H K s i,
      maskCoeff_equivariant F ζ hζ U R P H K s i⟩⟩


local notation:max "current_maskSections" => maskSections F ζ hζ U R P H

private theorem sectionNorm_maskSections_le (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    current_sectionNorm (current_maskSections K hK s) b ≤
      current_sectionNorm s.val b := by
  rw [((Homeomorph.apply_symm_apply (H.atlas U).components b).symm)]
  obtain ⟨i, q⟩ := (H.atlas U).components.symm b
  simp only [sectionNorm]
  rw [Homeomorph.symm_apply_apply]
  refine Quotient.inductionOn q (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · simp_all [DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers.maskSections, DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers.maskCoeff, Set.indicator_of_mem] <;> aesop
  · simp_all [DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers.maskSections, DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers.maskCoeff, Set.indicator_of_notMem] <;> aesop

private theorem normIntegral_maskSections_lt_top (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) :
    normIntegral F ζ hζ U R P H (current_maskSections K hK s) < ⊤ := by
  refine lt_of_le_of_lt ?_ s.property.2
  simp only [normIntegral, squaredNorm]
  refine lintegral_mono (fun b => ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀
    (sectionNorm_nonneg F ζ hζ U R P H (current_maskSections K hK s) b)
    (sectionNorm_maskSections_le F ζ hζ U R P H K hK s b) 2

 theorem maskSections_mem (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) :
    current_maskSections K hK s ∈ BorelL2Sections F ζ hζ U R P H :=
  ⟨fun i => measurable_maskCoeff F ζ hζ U R P H K hK s i,
    normIntegral_maskSections_lt_top F ζ hζ U R P H K hK s⟩

 theorem maskSections_add (hK : MeasurableSet K)
    (s t : BorelL2Sections F ζ hζ U R P H) :
    current_maskSections K hK (s + t) =
      current_maskSections K hK s + current_maskSections K hK t := by
  funext i
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Pi.add_apply, maskSections, maskCoeff]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx]
    simp

 theorem maskSections_smul (hK : MeasurableSet K) (c : ℂ)
    (s : BorelL2Sections F ζ hζ U R P H) :
    current_maskSections K hK (c • s) =
      c • current_maskSections K hK s := by
  funext i
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_smul, Pi.smul_apply, maskSections, maskCoeff, smul_eq_mul]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

def mask (hK : MeasurableSet K) :
    BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] BorelL2Sections F ζ hζ U R P H where
  toFun s := ⟨maskSections F ζ hζ U R P H K hK s,
    maskSections_mem F ζ hζ U R P H K hK s⟩
  map_add' := by
    intro s t
    exact Subtype.ext (maskSections_add F ζ hζ U R P H K hK s t)
  map_smul' := by
    intro c s
    exact Subtype.ext (maskSections_smul F ζ hζ U R P H K hK c s)


local notation:max "current_mask" => mask F ζ hζ U R P H

theorem mask_val_apply (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    ((current_mask K hK s).val i).val x =
      K.indicator (fun _ => (s.val i).val x)
        ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) := rfl

theorem sectionNorm_mask_components (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    current_sectionNorm (current_mask K hK s).val
        ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) =
      K.indicator (current_sectionNorm s.val)
        ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) := by
  rw [sectionNorm_component F ζ hζ U R P H (current_mask K hK s).val i x]
  by_cases h : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem h, mask_val_apply, Set.indicator_of_mem h,
      sectionNorm_component F ζ hζ U R P H s.val i x]
  · rw [Set.indicator_of_notMem h, mask_val_apply, Set.indicator_of_notMem h]
    simp

theorem squaredNorm_mask (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    current_squaredNorm (current_mask K hK s).val =
      K.indicator (current_squaredNorm s.val) := by
  funext b
  rw [((Homeomorph.apply_symm_apply (H.atlas U).components b).symm)]
  obtain ⟨i, q⟩ := (H.atlas U).components.symm b
  refine Quotient.inductionOn q (fun x => ?_)
  simp only [squaredNorm]
  rw [sectionNorm_mask_components]
  by_cases h : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

 theorem mask_mem_nullSections (hK : MeasurableSet K)
    {s : BorelL2Sections F ζ hζ U R P H} (hs : s ∈ current_nullOnK K) :
    current_mask K hK s ∈ nullSections F ζ hζ U R P H := by
  change current_squaredNorm (current_mask K hK s).val =ᵐ[
    current_muU R P] 0
  rw [squaredNorm_mask F ζ hζ U R P H K hK s]
  have hs' : current_squaredNorm s.val =ᵐ[
      (current_muU R P).restrict K] 0 := hs
  have hmem : ∀ᵐ b ∂(current_muU R P), b ∈ K →
      current_squaredNorm s.val b = 0 := by
    rw [← ae_restrict_iff' hK]
    filter_upwards [hs'] with b hb
    exact hb
  filter_upwards [hmem] with b hb
  by_cases hx : b ∈ K
  · rw [Set.indicator_of_mem hx]; exact hb hx
  · rw [Set.indicator_of_notMem hx]; rfl

 def zeroExtensionLinearMap (hK : MeasurableSet K) :
    BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  (mk F ζ hζ U R P H).comp (current_mask K hK)

def zeroExtension (hK : MeasurableSet K) :
    current_H_K K →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  @Submodule.liftQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (current_nullOnK K)
    ℂ (L2Line F ζ hζ U R P H) inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (zeroExtensionLinearMap F ζ hζ U R P H K hK) (by
      intro s hs
      rw [LinearMap.mem_ker]
      change (mk F ζ hζ U R P H) ((current_mask K hK) s) = 0
      rw [show (0 : L2Line F ζ hζ U R P H) = mk F ζ hζ U R P H 0 from
        (map_zero (mk F ζ hζ U R P H)).symm]
      rw [mk_eq_mk_iff]
      rw [show ((current_mask K hK) s).val -
          (0 : BorelL2Sections F ζ hζ U R P H).val =
          ((current_mask K hK) s).val from sub_zero _]
      apply mask_mem_nullSections <;> assumption)

private theorem zeroExtension_mkK (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    zeroExtension F ζ hζ U R P H K hK (mkK F ζ hζ U R P H K s) =
      mk F ζ hζ U R P H (current_mask K hK s) := rfl

 theorem nullSections_le_nullOnK :
    nullSections F ζ hζ U R P H ≤ current_nullOnK K := by
  intro s hs
  change current_squaredNorm s.val =ᵐ[(current_muU R P).restrict K] 0
  exact ae_restrict_of_ae hs

 def lineRestrictionLin :
    L2Line F ζ hζ U R P H →ₗ[ℂ] current_H_K K :=
  @Submodule.mapQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)
    ℂ (BorelL2Sections F ζ hζ U R P H) inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (current_nullOnK K) (LinearMap.id) (by
      intro s hs
      rw [Submodule.mem_comap]
      apply nullSections_le_nullOnK <;> assumption)

private theorem lineRestrictionLin_mk (s : BorelL2Sections F ζ hζ U R P H) :
    lineRestrictionLin F ζ hζ U R P H K (mk F ζ hζ U R P H s) =
      mkK F ζ hζ U R P H K s := by
  rfl

theorem zeroExtension_injective (hK : MeasurableSet K) :
    Function.Injective (zeroExtension F ζ hζ U R P H K hK) := by
  intro u v huv
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  obtain ⟨t, ht⟩ := Quotient.exists_rep v
  change mkK F ζ hζ U R P H K s = u at hs
  change mkK F ζ hζ U R P H K t = v at ht
  rw [← hs, ← ht] at huv ⊢
  rw [zeroExtension_mkK, zeroExtension_mkK] at huv
  have h2 : current_squaredNorm
      ((current_mask K hK (s - t)).val) =ᵐ[current_muU R P] 0 := by
    have h0 := (mk_eq_mk_iff F ζ hζ U R P H (current_mask K hK s)
      (current_mask K hK t)).mp huv
    have hsub : (current_mask K hK s - current_mask K hK t) = current_mask K hK (s - t) :=
      (map_sub (current_mask K hK) s t).symm
    rw [← Submodule.coe_sub, hsub] at h0
    exact h0
  have h3 : K.indicator (current_squaredNorm (s - t).val) =ᵐ[current_muU R P] 0 := by
    rw [← squaredNorm_mask F ζ hζ U R P H K hK (s - t)]
    exact h2
  have h4 : current_squaredNorm (s - t).val =ᵐ[(current_muU R P).restrict K] 0 := by
    change ∀ᵐ b ∂(current_muU R P).restrict K,
      current_squaredNorm (s - t).val b = 0
    rw [ae_restrict_iff' hK]
    filter_upwards [h3] with b hb
    intro hbK
    rwa [Set.indicator_of_mem hbK] at hb
  change Submodule.Quotient.mk s = Submodule.Quotient.mk t
  rw [Submodule.Quotient.eq]
  exact h4

 def hullK : Set (X_U F ζ hζ U) := toMeasurable (current_muU R P) K

 theorem measurableSet_hullK : MeasurableSet (hullK F ζ hζ U R P K) :=
  measurableSet_toMeasurable _ _

private theorem restrict_hullK :
    (current_muU R P).restrict (hullK F ζ hζ U R P K) =
      (current_muU R P).restrict K := by
  haveI : SigmaFinite (current_muU R P) :=
    KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_sigmaFinite F ζ hζ R P U
  haveI : SFinite (current_muU R P) := inferInstance
  exact Measure.restrict_toMeasurable_of_sFinite K

 theorem nullOnK_hullK :
    current_nullOnK K = current_nullOnK (hullK F ζ hζ U R P K) := by
  refine Submodule.ext fun s => ?_
  change (current_squaredNorm s.val =ᵐ[(current_muU R P).restrict K] 0) ↔
    (current_squaredNorm s.val =ᵐ[
      (current_muU R P).restrict (hullK F ζ hζ U R P K)] 0)
  rw [restrict_hullK]

 def extToHull :
    current_H_K K ≃ₗ[ℂ] current_H_K (hullK F ζ hζ U R P K) :=
  @Submodule.quotEquivOfEq ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance
    (current_nullOnK K)
    (current_nullOnK (hullK F ζ hζ U R P K)) (nullOnK_hullK F ζ hζ U R P H K)

 def normMap : current_H_K K →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  (zeroExtension F ζ hζ U R P H (hullK F ζ hζ U R P K)
      (measurableSet_hullK F ζ hζ U R P K)).comp
    (extToHull F ζ hζ U R P H K).toLinearMap

 theorem normMap_injective : Function.Injective (normMap F ζ hζ U R P H K) :=
  (zeroExtension_injective F ζ hζ U R P H (hullK F ζ hζ U R P K)
    (measurableSet_hullK F ζ hζ U R P K)).comp (extToHull F ζ hζ U R P H K).injective

instance instNormedAddCommGroupHK :
    NormedAddCommGroup (current_H_K K) :=
  NormedAddCommGroup.induced _ _ (normMap F ζ hζ U R P H K).toAddMonoidHom
    (normMap_injective F ζ hζ U R P H K)

instance instNormedSpaceHK : NormedSpace ℂ (current_H_K K) :=
  NormedSpace.induced ℂ _ _ (normMap F ζ hζ U R P H K)




 abbrev instTopologicalSpaceHKLocal  :=
  (inferInstance : NormedAddCommGroup (current_H_K K)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHKLocal

 abbrev instAddCommMonoidHKLocal  :=
  (inferInstance : NormedAddCommGroup (current_H_K K)).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidHKLocal

section RestrictedNorm
variable (hK : MeasurableSet K)

theorem norm_mkK_sq (s : BorelL2Sections F ζ hζ U R P H) :
    ‖mkK F ζ hζ U R P H K s‖ ^ 2 =
      (∫⁻ b in K, squaredNorm F ζ hζ U R P H s.val b ∂muU F ζ hζ U R P).toReal := by
  have hnorm : ‖mkK F ζ hζ U R P H K s‖ =
      ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H (hullK F ζ hζ U R P K)
        (measurableSet_hullK F ζ hζ U R P K) s)‖ := by
    rfl
  rw [hnorm, norm_sq]
  congr 1
  rw [normIntegral, squaredNorm_mask,
    lintegral_indicator (measurableSet_hullK F ζ hζ U R P K), restrict_hullK]

theorem zeroExtension_norm (u : H_K F ζ hζ U R P H K) :
    ‖zeroExtension F ζ hζ U R P H K hK u‖ = ‖u‖ := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  change mkK F ζ hζ U R P H K s = u at hs
  rw [← hs]
  have hZ : ‖zeroExtension F ζ hζ U R P H K hK (mkK F ζ hζ U R P H K s)‖ =
      ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖ := rfl
  have h2 : ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖ ^ 2 =
      ‖mkK F ζ hζ U R P H K s‖ ^ 2 := by
    rw [norm_sq, norm_mkK_sq]
    congr 1
    rw [normIntegral, squaredNorm_mask, lintegral_indicator hK]
  rw [hZ]
  calc ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖
      = Real.sqrt (‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖mkK F ζ hζ U R P H K s‖ ^ 2) := by rw [h2]
    _ = ‖mkK F ζ hζ U R P H K s‖ := Real.sqrt_sq (norm_nonneg _)

theorem mkK_eq_iff (s t : BorelL2Sections F ζ hζ U R P H) :
    mkK F ζ hζ U R P H K s = mkK F ζ hζ U R P H K t ↔
      squaredNorm F ζ hζ U R P H (s.val - t.val) =ᵐ[
        (muU F ζ hζ U R P).restrict K] 0 := by
  change Submodule.Quotient.mk s = Submodule.Quotient.mk t ↔ _
  rw [Submodule.Quotient.eq]
  rfl

 theorem lineRestrictionLin_norm_le (u : L2Line F ζ hζ U R P H) :
    ‖lineRestrictionLin F ζ hζ U R P H K u‖ ≤ ‖u‖ := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  change mk F ζ hζ U R P H s = u at hs
  rw [← hs, lineRestrictionLin_mk]
  have h2 : ‖mkK F ζ hζ U R P H K s‖ ^ 2 ≤ ‖mk F ζ hζ U R P H s‖ ^ 2 := by
    rw [norm_mkK_sq, norm_sq]
    refine ENNReal.toReal_mono (ne_of_lt s.property.2) ?_
    rw [normIntegral]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc ‖mkK F ζ hζ U R P H K s‖
      = Real.sqrt (‖mkK F ζ hζ U R P H K s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖mk F ζ hζ U R P H s‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖mk F ζ hζ U R P H s‖ := Real.sqrt_sq (norm_nonneg _)

def lineRestriction (hK : MeasurableSet K) : L2Line F ζ hζ U R P H →L[ℂ] H_K F ζ hζ U R P H K :=
  (lineRestrictionLin F ζ hζ U R P H K).mkContinuous 1 fun u => by
    rw [one_mul]
    apply lineRestrictionLin_norm_le

theorem lineRestriction_mk (s : BorelL2Sections F ζ hζ U R P H) :
    lineRestriction F ζ hζ U R P H K hK (mk F ζ hζ U R P H s) =
      mkK F ζ hζ U R P H K s := by
  rw [lineRestriction, LinearMap.mkContinuous_apply]
  apply lineRestrictionLin_mk

def res_K : H_U F ζ hζ U R →L[ℂ] H_K F ζ hζ U R P H K where
  toFun u := lineRestriction F ζ hζ U R P H K hK
    (sectorLineIsometry F ζ hζ U R P H u)
  map_add' := by
    intro u v
    rw [map_add, map_add]
  map_smul' := by
    intro c u
    simp only [map_smul, RingHom.id_apply]
  cont := by
    have hcont : Continuous fun u : H_U F ζ hζ U R =>
        lineRestriction F ζ hζ U R P H K hK
          (sectorLineIsometry F ζ hζ U R P H u) :=
      (lineRestriction F ζ hζ U R P H K hK).cont.comp
        (sectorLineIsometry F ζ hζ U R P H).continuous
    exact hcont

end RestrictedNorm

abbrev Chart := KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U)

def actualWeight (C : Chart F ζ hζ U R P H) (x : KPCoreChartLocalizers.E C.n)  :=
  ((H.disintegration U).componentWeight C.component).toReal * C.weight x

variable (hK : IsCompact K)

structure Localizers (hK : IsCompact K) where
  count : ℕ
  empty_case : K = ∅ → count = 0
  chart : Fin count → Chart F ζ hζ U R P H
  open_image : ∀ i, IsOpen ((chart i).O F ζ hζ H.totallyComplex U)
  quotient_chart : ∀ i, Quotient ((chart i).relation F ζ hζ H.totallyComplex U) ≃ₜ
    ((chart i).O F ζ hζ H.totallyComplex U)
  quotient_chart_formula : ∀ i (x : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n)
      (chart i).radius),
    (quotient_chart i (Quotient.mk _ x)).val =
      (chart i).toBase F ζ hζ H.totallyComplex U x.val
  orbit_relation : ∀ i (x y : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n)
      (chart i).radius),
    ((chart i).relation F ζ hζ H.totallyComplex U).r x y ↔
      ∃ g : (chart i).G F ζ hζ H.totallyComplex U, (chart i).orthogonal g x.val = y.val

  line_orbit_relation : ∀ i
      (x y : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n) (chart i).radius)
      (a b : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U),
    ((chart i).lineRelation F ζ hζ H.totallyComplex U).r (x,a) (y,b) ↔
      ∃ g : (chart i).G F ζ hζ H.totallyComplex U,
        (chart i).orthogonal g x.val = y.val ∧
        (b : ℂ) = ((chart i).rho F ζ hζ H.totallyComplex U g : ℂ) * (a : ℂ)
  line_chart_surjective : ∀ i
      (l : KPCoreChartLocalizers.Line F ζ hζ H.totallyComplex U (H.atlas U)),
    KPCoreChartLocalizers.lineBase F ζ hζ H.totallyComplex U (H.atlas U) l ∈
      (chart i).O F ζ hζ H.totallyComplex U →
      ∃ (x : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n) (chart i).radius)
        (a : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U),
        (chart i).toLine F ζ hζ H.totallyComplex U x.val a = l
  invariant_ball : ∀ i (g : (chart i).G F ζ hζ H.totallyComplex U),
    (chart i).orthogonal g '' Metric.ball 0 (chart i).radius = Metric.ball 0 (chart i).radius
  unitary_character : ∀ i (g : (chart i).G F ζ hζ H.totallyComplex U),
    ‖((chart i).rho F ζ hζ H.totallyComplex U g : ℂ)‖ = 1

  chart_measure : ∀ i, Measure.map ((chart i).toBase F ζ hζ H.totallyComplex U)
    ((Fintype.card ((chart i).G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
      (volume.restrict (Metric.ball 0 (chart i).radius)).withDensity
        (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H (chart i) x))) =
    (current_muU R P).restrict ((chart i).O F ζ hζ H.totallyComplex U)
  lower : Fin count → ℝ
  upper : Fin count → ℝ
  positive_lower : ∀ i, 0 < lower i

  density_bounds : ∀ i x, x ∈ closure (Metric.ball (0 : KPCoreChartLocalizers.E
      (chart i).n) (chart i).radius) →
    lower i ≤ actualWeight F ζ hζ U R P H (chart i) x ∧
      actualWeight F ζ hζ U R P H (chart i) x ≤ upper i
  phi : Fin count → X_U F ζ hζ U → ℝ
  nonnegative_phi : ∀ i x, 0 ≤ phi i x
  compact_phi : ∀ i, HasCompactSupport (phi i)
  support_phi : ∀ i, tsupport (phi i) ⊆ (chart i).O F ζ hζ H.totallyComplex U
  smooth_phi : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
    phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
      (KPCuspSiegel.projection F _ z)))
  neighborhood : Set (X_U F ζ hζ U)
  open_neighborhood : IsOpen neighborhood
  covers_compact : K ⊆ neighborhood
  partition : ∀ x ∈ neighborhood, ∑ i, phi i x = 1
  cutoff : ∀ i, KPCoreChartLocalizers.E (chart i).n → ℝ
  cutoff_formula : ∀ i, cutoff i = (Metric.ball 0 (chart i).radius).indicator
    (fun x => phi i ((chart i).toBase F ζ hζ H.totallyComplex U x))
  smooth_cutoff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (cutoff i)
  compact_cutoff : ∀ i, HasCompactSupport (cutoff i)
  support_cutoff : ∀ i, tsupport (cutoff i) ⊆ Metric.ball 0 (chart i).radius
  invariant_cutoff : ∀ i (g : (chart i).G F ζ hζ H.totallyComplex U) x,
    cutoff i ((chart i).orthogonal g x) = cutoff i x
  derivativeBound : Fin count → ℕ → ℝ
  nonnegative_derivativeBound : ∀ i k, 0 ≤ derivativeBound i k
  derivative_bounds : ∀ i k x, x ∈ tsupport (cutoff i) →
    ‖iteratedFDeriv ℝ k (cutoff i) x‖ ≤ derivativeBound i k
  ellipticity : Fin count → ℝ
  metricUpper : Fin count → ℝ
  positive_ellipticity : ∀ i, 0 < ellipticity i

  metric_bounds : ∀ i x, x ∈ tsupport (cutoff i) → ∀ ξ : KPCoreChartLocalizers.E (chart i).n,
    ellipticity i * ‖ξ‖ ^ 2 ≤
      ∑ j, ∑ k, (chart i).energyMatrix F ζ hζ H.totallyComplex U x j k * ξ j * ξ k ∧
    (∑ j, ∑ k, (chart i).energyMatrix F ζ hζ H.totallyComplex U x j k * ξ j * ξ k) ≤
      metricUpper i * ‖ξ‖ ^ 2
  T : ∀ i, H_U F ζ hζ U R →L[ℂ]
    Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a))

  T_formula : ∀ i (u : H_U F ζ hζ U R) (s : BorelL2Sections F ζ hζ U R P H),
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
    T i u =ᵐ[volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a)]
      (fun x => (cutoff i x : ℂ) * (s.val (chart i).component).val ((chart i).coordinates x))
  Rmap : ∀ i, Lp ℂ 2
    (volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a)) →L[ℂ]
      current_H_K K

  R_formula : ∀ i f, ∃ t : BorelL2Sections F ζ hζ U R P H,
    Rmap i f = mkK F ζ hζ U R P H K t ∧
    (∀ᵐ x ∂volume.restrict (Metric.ball 0 (chart i).radius),
      (chart i).toBase F ζ hζ H.totallyComplex U x ∈ K →
      (t.val (chart i).component).val ((chart i).coordinates x) =
        ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
          ((chart i).average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
    (∀ᵐ b ∂(current_muU R P).restrict K,
      b ∉ (chart i).O F ζ hζ H.totallyComplex U → current_squaredNorm t.val b = 0)
  reconstruction : res_K F ζ hζ U R P H K hK.measurableSet =
    ∑ i, (Rmap i).comp (T i)
  smooth_test_image : ∀ i (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H),
    ∃ g : KPCoreChartLocalizers.E (chart i).n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ interior (KPCoreChartLocalizers.cube (chart i).n (chart i).a) ∧
      T i (KPContActualSectorTestEmbeddings.iota f) =ᵐ[
        volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a)] g

end DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers

end
