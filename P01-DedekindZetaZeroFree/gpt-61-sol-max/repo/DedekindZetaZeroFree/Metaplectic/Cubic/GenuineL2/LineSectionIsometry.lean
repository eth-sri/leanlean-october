module

public import Mathlib

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.EquivariantBorelRepresentatives
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineNormDisintegration

@[expose] public section


noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContSectorLineL2Isometry

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorFixedPushforwardSupport KPContSectorSmoothFramesSupport
open KPContSectorPhaseComponentCharts
open KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

section
variable (s : Sections F ζ hζ U R P H)
include s
def scalarRepresentative    :=
  (J F ζ hζ U).symm ((H.atlas U).scalar_realization.symm s)

theorem scalarRepresentative_mk  
    (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) :
    (scalarRepresentative F ζ hζ U R P H s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x,c)) =
        ((H.atlas U).scalar_realization.symm s).val (x,c) := rfl

theorem scalarRepresentative_eq_symm   :
    scalarRepresentative F ζ hζ U R P H s = (S F ζ hζ U R P H).symm s := rfl


section
variable {F ζ hζ U R P H}
private noncomputable abbrev context_scalarRepresentative := scalarRepresentative F ζ hζ U R P H
end


local notation:max "current_componentHomeomorph" => componentHomeomorph F ζ hζ U R P H

private lemma recovery_phase  
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U) (x : SymmetricSpace F) :
    (scalarRepresentative F ζ hζ U R P H s).val
      (current_componentHomeomorph ⟨i, Quotient.mk _ (m,x)⟩) =
      (phaseCoefficient F ζ hζ U R P H s i m x : ℂ) := by
  have heq : S F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  simpa only [heq] using phase_component_restriction F ζ hζ U R P H
    (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) i m x

theorem borel_iff   :
    (∀ i, Measurable (s i).val) ↔
      Measurable (scalarRepresentative F ζ hζ U R P H s).val := by
  constructor
  · intro hs
    let D := Fin (H.atlas U).componentCount × (PhaseSheets F ζ hζ U × SymmetricSpace F)
    let π : D → CoveredSpherical F ζ hζ U := fun p =>
      current_componentHomeomorph ⟨p.1, Quotient.mk _ p.2⟩
    have hπ : Continuous π := by
      apply continuous_prod_of_discrete_left.mpr
      intro i
      have hq : Continuous (fun p : PhaseSheets F ζ hζ U × SymmetricSpace F =>
          (Quotient.mk _ p : PhaseComponent F ζ hζ U R P H i)) := continuous_quotient_mk'
      exact (current_componentHomeomorph).continuous.comp
        (continuous_sigmaMk.comp hq)
    have hsurj : Function.Surjective π := by
      intro v
      obtain ⟨⟨i,w⟩, hw⟩ := (current_componentHomeomorph).surjective v
      obtain ⟨p, rfl⟩ := Quotient.exists_rep w
      exact ⟨(i,p), hw⟩
    letI : MeasurableSpace (PhaseSheets F ζ hζ U) := borel _
    letI : BorelSpace (PhaseSheets F ζ hζ U) := ⟨rfl⟩
    have hmeas : Measurable ((_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val ∘ π) := by
      apply measurable_from_prod_countable_right
      intro i
      apply measurable_from_prod_countable_right
      intro m
      refine Quotient.inductionOn m ?_
      intro ε
      have heq : (fun x : SymmetricSpace F =>
        (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val (π (i, (Quotient.mk _ ε, x)))) =
          fun x => (chi F ζ hζ ε : ℂ) * (s i).val x := by
        funext x
        rw [recovery_phase]
        apply phaseCoefficient_class
      change Measurable (fun x : SymmetricSpace F =>
        (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val (π (i, (Quotient.mk _ ε, x))))
      rw [heq]
      exact measurable_const.mul (hs i)
    rw [measurable_iff_comap_le]
    have hmap := hπ.map_eq_borel hsurj
    rw [← BorelSpace.measurable_eq (α := CoveredSpherical F ζ hζ U)] at hmap
    rw [← hmap, ← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
    exact hmeas.comap_le
  · intro hf i
    have heq : (fun x : SymmetricSpace F => (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x, (H.atlas U).representative i))) = (s i).val := by
      funext x
      have h := congrArg (fun t : Sections F ζ hζ U R P H => (t i).val x)
        ((S F ζ hζ U R P H).apply_symm_apply s)
      rw [S_apply] at h
      exact h
    rw [← heq]
    exact hf.comp ((continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)).measurable)

theorem continuous_iff   :
    (∀ i, Continuous (s i).val) ↔
      Continuous (scalarRepresentative F ζ hζ U R P H s).val := by
  constructor
  · intro hs
    have hg : Continuous ((_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val ∘
        current_componentHomeomorph) := by
      apply continuous_sigma
      intro i
      apply isQuotientMap_quotient_mk'.continuous_iff.mpr
      apply continuous_prod_of_discrete_left.mpr
      intro m
      refine Quotient.inductionOn m ?_
      intro ε
      have heq : (fun x : SymmetricSpace F =>
          (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val
            (current_componentHomeomorph ⟨i, Quotient.mk _ (Quotient.mk _ ε,x)⟩)) =
          fun x => (chi F ζ hζ ε : ℂ) * (s i).val x := by
        funext x
        rw [recovery_phase]
        apply phaseCoefficient_class
      change Continuous (fun x : SymmetricSpace F =>
          (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val
            (current_componentHomeomorph ⟨i, Quotient.mk _ (Quotient.mk _ ε,x)⟩))
      rw [heq]
      apply continuous_const.mul <;> aesop
    have h := hg.comp (current_componentHomeomorph).symm.continuous
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using h
  · intro hf i
    have heq : (fun x : SymmetricSpace F => (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x, (H.atlas U).representative i))) = (s i).val := by
      funext x
      have h := congrArg (fun t : Sections F ζ hζ U R P H => (t i).val x)
        ((S F ζ hζ U R P H).apply_symm_apply s)
      rw [S_apply] at h
      exact h
    rw [← heq]
    exact hf.comp (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const))

def squaredNorm   :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞ :=
  fun b => ENNReal.ofReal (sectionNorm F ζ hζ U R P H s b ^ 2)

def normIntegral    :=
  ∫⁻ b, squaredNorm F ζ hζ U R P H s b ∂sphericalMeasure F ζ hζ R P U
end



local notation:max "current_Sections" => Sections F ζ hζ U R P H


local notation:max "current_sectionNorm" => sectionNorm F ζ hζ U R P H

 theorem sectionNorm_zero :
    current_sectionNorm (0 : current_Sections) = 0 := by
  funext b
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 ?_
  intro x
  simp [componentNorm]


local notation:max "current_squaredNorm" => squaredNorm F ζ hζ U R P H

 theorem squaredNorm_zero :
    current_squaredNorm (0 : current_Sections) = 0 := by
  funext b
  simp only [squaredNorm, sectionNorm_zero]
  simp

private theorem componentNorm_add_le (s t : current_Sections)
    (i : Fin (H.atlas U).componentCount)
    (y : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :
    componentNorm F ζ hζ U R P H (s + t) i y ≤
      componentNorm F ζ hζ U R P H s i y + componentNorm F ζ hζ U R P H t i y := by
  refine Quotient.inductionOn y ?_
  intro x
  simp only [componentNorm, Quotient.lift_mk]
  calc ‖((s + t) i).val x‖ = ‖(s i).val x + (t i).val x‖ := rfl
    _ ≤ ‖(s i).val x‖ + ‖(t i).val x‖ := norm_add_le _ _

 theorem sectionNorm_nonneg (s : current_Sections)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    0 ≤ current_sectionNorm s b := by
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 ?_
  intro x
  simp only [componentNorm, Quotient.lift_mk]
  exact norm_nonneg _

 theorem sectionNorm_add_le (s t : current_Sections) :
    current_sectionNorm (s + t) ≤
      current_sectionNorm s + current_sectionNorm t := by
  intro b
  simp only [sectionNorm]
  exact componentNorm_add_le F ζ hζ U R P H s t _ _

 theorem sectionNorm_smul (c : ℂ) (s : current_Sections) :
    current_sectionNorm (c • s) =
      fun b => ‖c‖ * current_sectionNorm s b := by
  funext b
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 ?_
  intro x
  simp only [componentNorm, Quotient.lift_mk]
  rw [show ((c • s) ((H.atlas U).components.symm b).fst).val x =
      c * (s ((H.atlas U).components.symm b).fst).val x from rfl, norm_mul]


section
variable {F ζ hζ U R P H}
private noncomputable abbrev context_sectionNorm := sectionNorm F ζ hζ U R P H
end

 theorem squaredNorm_add_le (s t : current_Sections)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    current_squaredNorm (s + t) b ≤
      (2 : ℝ≥0∞) * current_squaredNorm s b +
        (2 : ℝ≥0∞) * current_squaredNorm t b := by
  
  
  have hc := sectionNorm_nonneg F ζ hζ U R P H (s + t) b
  have hle : _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm (s + t) b ≤
      _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm s b + _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm t b :=
    sectionNorm_add_le F ζ hζ U R P H s t b
  have hmain : (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm (s + t) b) ^ 2 ≤
      2 * _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm s b ^ 2 + 2 * _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm t b ^ 2 := by
    calc (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm (s + t) b) ^ 2
        ≤ (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm s b + _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm t b) ^ 2 :=
          pow_le_pow_left₀ hc hle 2
      _ ≤ 2 * (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm s b ^ 2 + _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm t b ^ 2) :=
          add_sq_le
      _ = _ := by ring
  simp only [squaredNorm]
  calc ENNReal.ofReal (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm (s + t) b ^ 2)
      ≤ ENNReal.ofReal (2 * _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm s b ^ 2 +
          2 * _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm t b ^ 2) := ENNReal.ofReal_le_ofReal hmain
    _ = (2 : ℝ≥0∞) * ENNReal.ofReal (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm s b ^ 2) +
          (2 : ℝ≥0∞) * ENNReal.ofReal (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm t b ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := (2:ℝ)) (by norm_num),
          ENNReal.ofReal_mul (p := (2:ℝ)) (by norm_num)]
        norm_num

 theorem squaredNorm_smul (c : ℂ) (s : current_Sections)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    current_squaredNorm (c • s) b =
      ENNReal.ofReal (‖c‖ ^ 2) * current_squaredNorm s b := by
  
  simp only [squaredNorm]
  rw [(congrFun (sectionNorm_smul F ζ hζ U R P H c s) b)]
  rw [mul_pow, ENNReal.ofReal_mul (by positivity)]


local notation:max "current_S" => S F ζ hζ U R P H

 theorem squaredNorm_measurable_aux (s : current_Sections)
    (hs : ∀ i, Measurable (s i).val) :
    Measurable (current_squaredNorm s) := by
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s)
      ((borel_iff F ζ hζ U R P H s).mp hs)).borel
  have heq : current_S (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) = s :=
    (current_S).apply_symm_apply s
  change Measurable (fun b => ENNReal.ofReal
    (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_sectionNorm (current_S
      (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s)) b ^ 2)) at hn
  rw [heq] at hn
  exact hn


local notation:max "current_normIntegral" => normIntegral F ζ hζ U R P H

def BorelL2Sections : Submodule ℂ (current_Sections) where
  carrier := {s | (∀ i, Measurable (s i).val) ∧ current_normIntegral s < ⊤}
  zero_mem' := ⟨fun _ => measurable_zero, by
    rw [normIntegral, squaredNorm_zero]; simp⟩
  add_mem' := by
    intro s t hs ht
    refine ⟨fun i => (hs.1 i).add (ht.1 i), ?_⟩
    have hle : current_normIntegral (s + t) ≤
        (2 : ℝ≥0∞) * current_normIntegral s +
          (2 : ℝ≥0∞) * current_normIntegral t := by
      simp only [normIntegral]
      calc ∫⁻ b, current_squaredNorm (s + t) b ∂sphericalMeasure F ζ hζ R P U
          ≤ ∫⁻ b, ((2 : ℝ≥0∞) * current_squaredNorm s b +
              (2 : ℝ≥0∞) * current_squaredNorm t b)
              ∂sphericalMeasure F ζ hζ R P U :=
            lintegral_mono (fun b => squaredNorm_add_le F ζ hζ U R P H s t b)
        _ = (2 : ℝ≥0∞) * ∫⁻ b, current_squaredNorm s b
              ∂sphericalMeasure F ζ hζ R P U +
            (2 : ℝ≥0∞) * ∫⁻ b, current_squaredNorm t b
              ∂sphericalMeasure F ζ hζ R P U := by
            rw [lintegral_add_left ((squaredNorm_measurable_aux F ζ hζ U R P H s hs.1).const_mul 2),
              lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num),
              lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
    refine lt_of_le_of_lt hle ?_
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.mul_lt_top (by norm_num) hs.2, ENNReal.mul_lt_top (by norm_num) ht.2⟩
  smul_mem' := by
    intro c s hs
    refine ⟨fun i => (hs.1 i).const_smul c, ?_⟩
    have heq : current_normIntegral (c • s) =
        ENNReal.ofReal (‖c‖ ^ 2) * current_normIntegral s := by
      simp only [normIntegral]
      rw [← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ 2)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro b
      apply squaredNorm_smul
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.2

def BorelL2Scalars : Submodule ℂ (GenuineCoveredScalars F ζ hζ U) where
  carrier := {f | Measurable f.val ∧ MemLp f.val 2 (coveredMeasure F ζ hζ R U)}
  zero_mem' := ⟨measurable_zero, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    exact ⟨hf.1.const_smul c, hf.2.const_smul c⟩


local notation:max "current_scalarRepresentative" => scalarRepresentative F ζ hζ U R P H

theorem finite_integral_iff (s : current_Sections)
    (hs : ∀ i, Measurable (s i).val) :
    current_normIntegral s < ⊤ ↔
      MemLp (current_scalarRepresentative s).val 2
        (coveredMeasure F ζ hζ R U) := by
  have hf  :=
    (borel_iff F ζ hζ U R P H s).mp hs
  have hbridge : current_normIntegral s =
      ∫⁻ v, ENNReal.ofReal
        (‖(_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val v‖ ^ 2)
        ∂coveredMeasure F ζ hζ R U := by
    have hq  :=
      (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
    rw [normIntegral, ← map_q_coveredMeasure F ζ hζ R P U,
      lintegral_map (squaredNorm_measurable_aux F ζ hζ U R P H s hs) hq]
    apply lintegral_congr
    intro v
    have heq : current_S (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) = s :=
      (current_S).apply_symm_apply s
    have hsn  :=
      sectionNorm_pullback F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) v
    simp only [squaredNorm]
    conv_lhs => rw [← heq]
    rw [hsn]
  have hIntEq : (∫⁻ v, ENNReal.ofReal
        (‖(_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val v‖ ^ 2)
        ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ v, ‖(_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s).val v‖ₑ ^
        (2 : ℝ≥0∞).toReal ∂coveredMeasure F ζ hζ R U := by
    apply lintegral_congr
    (intros; norm_num)
  rw [hbridge, memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf.aestronglyMeasurable, hIntEq]


local notation:max "current_BorelL2Sections" => BorelL2Sections F ζ hζ U R P H

def borelS : BorelL2Scalars F ζ hζ U R ≃ₗ[ℂ] current_BorelL2Sections where
  toFun f := by
    have hmeas : ∀ i, Measurable ((current_S f.val) i).val := by
      intro i
      have hc : Measurable (fun x : SymmetricSpace F =>
          Quotient.mk (coveredRelation F ζ hζ U) (x, (H.atlas U).representative i)) :=
        (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)).measurable
      have heq : (current_S f.val i).val =
          fun x => f.val.val (Quotient.mk (coveredRelation F ζ hζ U)
            (x, (H.atlas U).representative i)) := by
        funext x; rw [S_apply]
      rw [heq]; exact f.property.1.comp hc
    refine ⟨S F ζ hζ U R P H f.val, hmeas, ?_⟩
    refine (finite_integral_iff F ζ hζ U R P H (current_S f.val) hmeas).mpr ?_
    rw [scalarRepresentative_eq_symm F ζ hζ U R P H (current_S f.val),
      (current_S).symm_apply_apply f.val]
    exact f.property.2
  invFun s := ⟨scalarRepresentative F ζ hζ U R P H s.val,
    (borel_iff F ζ hζ U R P H s.val).mp s.property.1,
    (finite_integral_iff F ζ hζ U R P H s.val s.property.1).mp s.property.2⟩
  left_inv := by
    intro f
    apply Subtype.ext
    show current_scalarRepresentative (current_S f.val) =
      f.val
    rw [scalarRepresentative_eq_symm F ζ hζ U R P H (current_S f.val),
      (current_S).symm_apply_apply f.val]
  right_inv := by
    intro s
    apply Subtype.ext
    show current_S (current_scalarRepresentative s.val) =
      s.val
    rw [scalarRepresentative_eq_symm F ζ hζ U R P H s.val,
      (current_S).apply_symm_apply s.val]
  map_add' := by
    intro f g
    apply Subtype.ext
    simp [map_add]
  map_smul' := by
    intro c f
    apply Subtype.ext
    simp [map_smul]


local notation:max "current_sphericalMeasure" => sphericalMeasure F ζ hζ

def nullSections : Submodule ℂ (current_BorelL2Sections) where
  carrier := {s | current_squaredNorm s.val =ᵐ[
    current_sphericalMeasure R P U] 0}
  zero_mem' := by
    change current_squaredNorm ((0 : current_BorelL2Sections).val)
      =ᵐ[current_sphericalMeasure R P U] 0
    rw [show (0 : current_BorelL2Sections).val =
      (0 : current_Sections) from rfl, squaredNorm_zero]
  add_mem' := by
    intro s t hs ht
    change current_squaredNorm (s.val + t.val) =ᵐ[current_sphericalMeasure R P U] 0
    have hs' : current_squaredNorm s.val =ᵐ[current_sphericalMeasure R P U] 0 := hs
    have ht' : current_squaredNorm t.val =ᵐ[current_sphericalMeasure R P U] 0 := ht
    have hle : current_squaredNorm (s.val + t.val) ≤ᵐ[current_sphericalMeasure R P U]
        fun b => (2 : ℝ≥0∞) * current_squaredNorm s.val b +
          (2 : ℝ≥0∞) * current_squaredNorm t.val b :=
      Filter.Eventually.of_forall (fun b => squaredNorm_add_le F ζ hζ U R P H s.val t.val b)
    have hzero : (fun b => (2 : ℝ≥0∞) * current_squaredNorm s.val b +
          (2 : ℝ≥0∞) * current_squaredNorm t.val b)
        =ᵐ[current_sphericalMeasure R P U] 0 := by
      filter_upwards [hs', ht'] with b hb hbt
      simp [hb, hbt]
    exact (hle.trans_eq hzero).antisymm
      (Filter.Eventually.of_forall
        (fun b => (zero_le : (0 : ℝ≥0∞) ≤ current_squaredNorm (s.val + t.val) b)))
  smul_mem' := by
    intro c s hs
    change current_squaredNorm (c • s.val) =ᵐ[current_sphericalMeasure R P U] 0
    have hs' : current_squaredNorm s.val =ᵐ[current_sphericalMeasure R P U] 0 := hs
    filter_upwards [hs'] with b hb
    rw [squaredNorm_smul F ζ hζ U R P H c s.val b, hb]
    simp

local instance : HasQuotient (current_BorelL2Sections)
    (Submodule ℂ (current_BorelL2Sections)) :=
  @Submodule.hasQuotient ℂ (current_BorelL2Sections)
    inferInstance inferInstance inferInstance

abbrev L2Line := ↥(current_BorelL2Sections) ⧸ nullSections F ζ hζ U R P H


local notation:max "current_L2Line" => L2Line F ζ hζ U R P H

def mk : current_BorelL2Sections →ₗ[ℂ] current_L2Line :=
  @Submodule.mkQ ℂ (current_BorelL2Sections)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)


local notation:max "current_mk" => mk F ζ hζ U R P H

theorem mk_eq_mk_iff (s t : current_BorelL2Sections) :
    current_mk s = current_mk t ↔
      current_squaredNorm (s.val - t.val) =ᵐ[
        current_sphericalMeasure R P U] 0 := by
  change Submodule.Quotient.mk s = Submodule.Quotient.mk t ↔
    s - t ∈ nullSections F ζ hζ U R P H
  apply Submodule.Quotient.eq

theorem null_iff_scalar_ae_eq (s t : current_BorelL2Sections) :
    current_squaredNorm (s.val - t.val) =ᵐ[
        current_sphericalMeasure R P U] 0 ↔
      (current_scalarRepresentative s.val).val =ᵐ[
        coveredMeasure F ζ hζ R U]
          (current_scalarRepresentative t.val).val := by
  have hmeas := squaredNorm_measurable_aux F ζ hζ U R P H
    (s.val - t.val) (s - t).property.1
  have hq  :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have hdesc : (current_squaredNorm (s.val - t.val) =ᵐ[
      current_sphericalMeasure R P U] 0) ↔
      ∀ᵐ v ∂coveredMeasure F ζ hζ R U,
        current_squaredNorm (s.val - t.val) (q F ζ hζ U v) = 0 := by
    rw [← map_q_coveredMeasure F ζ hζ R P U]
    exact ae_map_iff hq.aemeasurable (measurableSet_eq_fun hmeas measurable_const)
  rw [hdesc]
  have hpoint (v : CoveredSpherical F ζ hζ U) :
      current_squaredNorm (s.val - t.val) (q F ζ hζ U v) = 0 ↔
      (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val).val v =
        (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative t.val).val v := by
    have heq : current_S
        (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative (s.val - t.val)) = s.val - t.val :=
      (current_S).apply_symm_apply _
    have hnorm := sectionNorm_pullback F ζ hζ U R P H
      (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative (s.val - t.val)) v
    rw [heq] at hnorm
    have hsub : _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative (s.val - t.val) =
        _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val -
          _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative t.val := by
      simp only [scalarRepresentative_eq_symm, map_sub]
    rw [squaredNorm, hnorm, hsub]
    change ENNReal.ofReal
      (‖(_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val).val v -
        (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative t.val).val v‖ ^ 2) = 0 ↔ _
    rw [ENNReal.ofReal_eq_zero]
    constructor
    · intro hh
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
        (le_antisymm hh (sq_nonneg _))))
    · intro hh
      simp [hh]
  exact Filter.eventually_congr (Filter.Eventually.of_forall hpoint)

def representative_memLp (s : current_BorelL2Sections)  :=
  (finite_integral_iff F ζ hζ U R P H s.val s.property.1).mp s.property.2


local notation:max "current_representative_memLp" => representative_memLp F ζ hζ U R P H

def toSector : current_BorelL2Sections →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U where
  toFun s := ⟨(current_representative_memLp s).toLp
    (current_scalarRepresentative s.val).val, by
      rw [KPContSectorClosedLpSubspace.mem_H_iff]
      intro ε
      have hcoef : ((current_representative_memLp s).toLp
          (current_scalarRepresentative s.val).val :
            CoveredSpherical F ζ hζ U → ℂ) =ᵐ[coveredMeasure F ζ hζ R U]
          (current_scalarRepresentative s.val).val :=
        MemLp.coeFn_toLp _
      have h1  :=
        (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).quasiMeasurePreserving.ae_eq_comp
          hcoef
      have h2 : (current_scalarRepresentative s.val).val ∘ z F ζ hζ U ε =ᵐ[
          coveredMeasure F ζ hζ R U]
          (chi F ζ hζ ε : ℂ) • (current_scalarRepresentative s.val).val :=
        Filter.Eventually.of_forall (fun v => by
          rw [Pi.smul_apply, smul_eq_mul]
          exact (current_scalarRepresentative s.val).property ε v)
      have h3 : (chi F ζ hζ ε : ℂ) • (current_scalarRepresentative s.val).val =ᵐ[
          coveredMeasure F ζ hζ R U]
          (chi F ζ hζ ε : ℂ) • ((current_representative_memLp s).toLp
            (current_scalarRepresentative s.val).val :
              CoveredSpherical F ζ hζ U → ℂ) :=
        (hcoef.const_smul (chi F ζ hζ ε : ℂ)).symm
      exact h1.trans (h2.trans h3)⟩
  map_add' := by
    intro s t
    apply Subtype.ext
    simp only [Submodule.coe_add]
    have hsadd : current_scalarRepresentative (s + t) =
        current_scalarRepresentative s + current_scalarRepresentative t := by
      simp only [scalarRepresentative, map_add]
    have hfg : (current_scalarRepresentative (s + t)).val =
        (current_scalarRepresentative s).val +
          (current_scalarRepresentative t).val := by
      rw [hsadd, Submodule.coe_add]
    have hA : (current_representative_memLp (s + t)).toLp
        (current_scalarRepresentative (s + t)).val =
        ((current_representative_memLp s).add
          (current_representative_memLp t)).toLp
          ((current_scalarRepresentative s).val +
            (current_scalarRepresentative t).val) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun v => congrFun hfg v))
    rw [hA, MemLp.toLp_add]
  map_smul' := by
    intro c s
    apply Subtype.ext
    simp only [Submodule.coe_smul]
    have hsmul : current_scalarRepresentative (c • s) =
        c • current_scalarRepresentative s := by
      simp only [scalarRepresentative, map_smul]
    have hfg : (current_scalarRepresentative (c • s)).val =
        c • (current_scalarRepresentative s).val := by
      rw [hsmul, Submodule.coe_smul]
    have hA : (current_representative_memLp (c • s)).toLp
        (current_scalarRepresentative (c • s)).val =
        ((current_representative_memLp s).const_smul c).toLp
          (c • (current_scalarRepresentative s).val) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun v => congrFun hfg v))
    rw [hA]
    apply MemLp.toLp_const_smul

def quotientToSector : current_L2Line →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  @Submodule.liftQ ℂ (current_BorelL2Sections)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)
    ℂ (KPContSectorClosedLpSubspace.H F ζ hζ R U)
    inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (toSector F ζ hζ U R P H) (by
      intro s hs
      change toSector F ζ hζ U R P H s = 0
      rw [← map_zero (toSector F ζ hζ U R P H)]
      apply Subtype.ext
      have hnull : current_squaredNorm (s.val - (0 : current_Sections)) =ᵐ[
          current_sphericalMeasure R P U] 0 := by
        change current_squaredNorm s.val =ᵐ[current_sphericalMeasure R P U] 0 at hs
        simpa using hs
      have hae := (null_iff_scalar_ae_eq F ζ hζ U R P H s 0).mp hnull
      exact (current_representative_memLp s).toLp_congr
        (current_representative_memLp 0) hae)

set_option maxHeartbeats 1000000 in

theorem quotientToSector_bijective : Function.Bijective (quotientToSector F ζ hζ U R P H) := by
  constructor
  · intro x y hxy
    obtain ⟨s, hs⟩ := Quotient.exists_rep x
    obtain ⟨t, ht⟩ := Quotient.exists_rep y
    change current_mk s = x at hs
    change current_mk t = y at ht
    rw [← hs, ← ht] at hxy ⊢
    apply (mk_eq_mk_iff F ζ hζ U R P H s t).mpr
    apply (null_iff_scalar_ae_eq F ζ hζ U R P H s t).mpr
    apply ((current_representative_memLp s).toLp_eq_toLp_iff
      (current_representative_memLp t)).mp
    exact congrArg Subtype.val hxy
  · intro u
    obtain ⟨g, hg, hgLp, hgu, f, hf, hfLp, hfg, hfu, hfeq, _⟩ :=
      KPContSectorExactBorelRepresentatives.exists_exact_borel_representative F ζ hζ R U u
    let f₀ : GenuineCoveredScalars F ζ hζ U := ⟨f, hfeq⟩
    let f₁ : BorelL2Scalars F ζ hζ U R := ⟨f₀, hf, hfLp⟩
    let s := borelS F ζ hζ U R P H f₁
    refine ⟨mk F ζ hζ U R P H s, ?_⟩
    apply Subtype.ext
    change (current_representative_memLp s).toLp
      (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val).val = _
    have heq : _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val = f₀ := by
      change (current_S).symm (current_S f₀) = f₀
      exact (current_S).symm_apply_apply f₀
    have hae : (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val).val =ᵐ[
        coveredMeasure F ζ hζ R U] f := by rw [heq]
    exact ((current_representative_memLp s).toLp_congr hfLp hae).trans hfu

def lineToSector : current_L2Line ≃ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  LinearEquiv.ofBijective (quotientToSector F ζ hζ U R P H)
    (quotientToSector_bijective F ζ hζ U R P H)


local notation:max "current_lineToSector" => lineToSector F ζ hζ U R P H

instance instNormedAddCommGroupL2Line : NormedAddCommGroup (current_L2Line) :=
  NormedAddCommGroup.induced _ _ (current_lineToSector).toAddMonoidHom
    (current_lineToSector).injective

instance instNormedSpaceL2Line : NormedSpace ℂ (current_L2Line) :=
  NormedSpace.induced ℂ _ _ (current_lineToSector).toLinearMap

def sectorLineIsometry : KPContSectorClosedLpSubspace.H F ζ hζ R U ≃ₗᵢ[ℂ]
    current_L2Line where
  __ := (current_lineToSector).symm
  norm_map' := by
    intro u
    change ‖lineToSector F ζ hζ U R P H ((current_lineToSector).symm u)‖ = ‖u‖
    rw [LinearEquiv.apply_symm_apply]




instance instInnerProductSpaceL2Line : InnerProductSpace ℂ (current_L2Line) :=
  InnerProductSpace.induced (current_lineToSector)

section
variable (s : BorelL2Sections F ζ hζ U R P H)
include s
theorem norm_sq   :
    ‖mk F ζ hζ U R P H s‖ ^ 2 = (normIntegral F ζ hζ U R P H s.val).toReal := by
  have hf := (borel_iff F ζ hζ U R P H s.val).mp s.property.1
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val) hf).lp_norm
      (representative_memLp F ζ hζ U R P H s)
  have heq : S F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val) = s.val :=
    (S F ζ hζ U R P H).apply_symm_apply s.val
  change ‖(representative_memLp F ζ hζ U R P H s).toLp
    (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s.val).val‖ ^ 2 = _
  simpa only [KPContSectorFixedLineNormIntegrals.lineNorm, heq, normIntegral, squaredNorm] using hn

theorem ofReal_norm_sq   :
    ENNReal.ofReal (‖mk F ζ hζ U R P H s‖ ^ 2) = normIntegral F ζ hζ U R P H s.val := by
  rw [norm_sq, ENNReal.ofReal_toReal (ne_of_lt s.property.2)]

theorem sectorLineIsometry_symm_mk   :
    ((sectorLineIsometry F ζ hζ U R P H).symm (mk F ζ hζ U R P H s) :
      KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
    (representative_memLp F ζ hζ U R P H s).toLp
      (scalarRepresentative F ζ hζ U R P H s.val).val := rfl
end


theorem sectorLineIsometry_toSector (f : BorelL2Scalars F ζ hζ U R) :
    sectorLineIsometry F ζ hζ U R P H
      (toSector F ζ hζ U R P H (borelS F ζ hζ U R P H f)) =
        current_mk (borelS F ζ hζ U R P H f) := by
  change (current_lineToSector).symm
    (current_lineToSector (current_mk (borelS F ζ hζ U R P H f))) = _
  exact (current_lineToSector).symm_apply_apply _

def scalarEmbedding  :=
  (toSector F ζ hζ U R P H).comp (borelS F ζ hζ U R P H).toLinearMap

theorem scalarEmbedding_coe (f : BorelL2Scalars F ζ hζ U R) :
    (scalarEmbedding F ζ hζ U R P H f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
      f.property.2.toLp f.val.val := by
  have heq : _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative (borelS F ζ hζ U R P H f).val = f.val :=
    (current_S).symm_apply_apply f.val
  have hae : (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative (borelS F ζ hζ U R P H f).val).val =ᵐ[
      coveredMeasure F ζ hζ R U] f.val.val := by rw [heq]
  exact (current_representative_memLp (borelS F ζ hζ U R P H f)).toLp_congr
    f.property.2 hae

theorem sectorLineIsometry_representative
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (f : BorelL2Scalars F ζ hζ U R)
    (hf : f.property.2.toLp f.val.val =
      (u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)) :
    sectorLineIsometry F ζ hζ U R P H u =
      current_mk (borelS F ζ hζ U R P H f) := by
  have heq  :=
    Subtype.ext ((scalarEmbedding_coe F ζ hζ U R P H f).trans hf)
  rw [← heq]
  apply sectorLineIsometry_toSector

def ContinuousL2Scalars : Submodule ℂ (BorelL2Scalars F ζ hζ U R) where
  carrier := {f | Continuous f.val.val}
  zero_mem' := continuous_const
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    exact hf.const_smul c

def ContinuousL2Sections : Submodule ℂ (current_BorelL2Sections) where
  carrier := {s | ∀ i, Continuous (s.val i).val}
  zero_mem' := fun _ => continuous_const
  add_mem' := by
    intro s t hs ht i
    exact (hs i).add (ht i)
  smul_mem' := by
    intro c s hs i
    exact (hs i).const_smul c

def continuousScalarEmbedding  :=
  (scalarEmbedding F ζ hζ U R P H).comp (ContinuousL2Scalars F ζ hζ U R).subtype

def continuousSectionEmbedding : ContinuousL2Sections F ζ hζ U R P H →ₗ[ℂ]
    current_L2Line :=
  (current_mk).comp (ContinuousL2Sections F ζ hζ U R P H).subtype

theorem continuousScalarEmbedding_injective :
    Function.Injective (continuousScalarEmbedding F ζ hζ U R P H) := by
  letI := (levelSupport F ζ hζ R P
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  intro f g hfg
  have hlp := congrArg (fun u : KPContSectorClosedLpSubspace.H F ζ hζ R U => u.val) hfg
  change (scalarEmbedding F ζ hζ U R P H f.val).val =
    (scalarEmbedding F ζ hζ U R P H g.val).val at hlp
  rw [scalarEmbedding_coe, scalarEmbedding_coe] at hlp
  have hae := (f.val.property.2.toLp_eq_toLp_iff g.val.property.2).mp hlp
  have heq := (f.property.ae_eq_iff_eq (coveredMeasure F ζ hζ R U) g.property).mp hae
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext heq

theorem continuousSectionEmbedding_injective :
    Function.Injective (continuousSectionEmbedding F ζ hζ U R P H) := by
  letI := (levelSupport F ζ hζ R P
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  intro s t hst
  have hae := (null_iff_scalar_ae_eq F ζ hζ U R P H s.val t.val).mp
    ((mk_eq_mk_iff F ζ hζ U R P H s.val t.val).mp hst)
  have hs := (continuous_iff F ζ hζ U R P H s.val.val).mp s.property
  have ht := (continuous_iff F ζ hζ U R P H t.val.val).mp t.property
  have heq := (hs.ae_eq_iff_eq (coveredMeasure F ζ hζ R U) ht).mp hae
  have hsct  := Subtype.ext heq
  have hval : s.val.val = t.val.val := (current_S).symm.injective hsct
  exact Subtype.ext (Subtype.ext hval)

def SmoothCompactL2Scalars : Submodule ℂ (BorelL2Scalars F ζ hζ U R) where
  carrier := {f | IsSmoothCovered F ζ hζ U f.val ∧ HasCompactSupport f.val.val}
  zero_mem' := ⟨by
      show IsSmoothCovered F ζ hζ U (0 : GenuineCoveredScalars F ζ hζ U)
      intro c
      have h : (fun x : SymmetricSpace F => (J F ζ hζ U 0).val (x, c))
          = fun _ => (0 : ℂ) := by
        funext x; simp
      rw [h]; exact contDiff_const,
    by
      show HasCompactSupport (0 : CoveredSpherical F ζ hζ U → ℂ)
      rw [hasCompactSupport_iff_eventuallyEq]⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · show IsSmoothCovered F ζ hζ U (f.val + g.val)
      intro c
      have h : (fun x : SymmetricSpace F => (J F ζ hζ U (f.val + g.val)).val (x, c))
          = fun x => (J F ζ hζ U f.val).val (x, c) + (J F ζ hζ U g.val).val (x, c) := by
        funext x; simp [map_add]
      rw [h]; exact (hf.1 c).add (hg.1 c)
    · exact hf.2.add hg.2
  smul_mem' := by
    intro a f hf
    refine ⟨?_, ?_⟩
    · show IsSmoothCovered F ζ hζ U (a • f.val)
      intro c
      have h : (fun x : SymmetricSpace F => (J F ζ hζ U (a • f.val)).val (x, c))
          = fun x => a • (J F ζ hζ U f.val).val (x, c) := by
        funext x; simp [map_smul]
      rw [h]; exact (hf.1 c).const_smul a
    · have heq : (a • f).val.val = fun x => a * f.val.val x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rw [heq]; exact hf.2.comp_left (g := fun z => a * z) (by simp)

def smoothCompactScalarEmbedding  :=
  (scalarEmbedding F ζ hζ U R P H).comp (SmoothCompactL2Scalars F ζ hζ U R).subtype

theorem smoothCompactScalarEmbedding_injective :
    Function.Injective (smoothCompactScalarEmbedding F ζ hζ U R P H) := by
  intro f g hfg
  have hcont : ∀ h : SmoothCompactL2Scalars F ζ hζ U R, Continuous h.val.val.val := by
    intro h
    have hs := (smooth_iff F ζ hζ U R P H h.val.val).mp h.property.1
    have hc := (continuous_iff F ζ hζ U R P H (current_S h.val.val)).mp
      (fun i => (hs i).continuous)
    simpa only [scalarRepresentative_eq_symm, LinearEquiv.symm_apply_apply] using hc
  let f₀ : ContinuousL2Scalars F ζ hζ U R := ⟨f.val, hcont f⟩
  let g₀ : ContinuousL2Scalars F ζ hζ U R := ⟨g.val, hcont g⟩
  have heq : continuousScalarEmbedding F ζ hζ U R P H f₀ =
      continuousScalarEmbedding F ζ hζ U R P H g₀ := hfg
  have hval := congrArg (fun h : ContinuousL2Scalars F ζ hζ U R => h.val)
    (continuousScalarEmbedding_injective F ζ hζ U R P H heq)
  exact Subtype.ext hval

def SmoothCompactL2Sections : Submodule ℂ (current_BorelL2Sections) where
  carrier := {s | IsSmoothSections F ζ hζ U R P H s.val ∧
    HasCompactSupport (current_sectionNorm s.val)}
  zero_mem' := ⟨by
      show IsSmoothSections F ζ hζ U R P H (0 : current_Sections)
      intro i
      have h : ((0 : current_Sections) i).val = fun _ => (0 : ℂ) := by
        funext x; simp
      rw [h]; exact contDiff_const,
    by
      show HasCompactSupport (current_sectionNorm (0 : current_Sections))
      rw [sectionNorm_zero, hasCompactSupport_iff_eventuallyEq]⟩
  add_mem' := by
    intro s t hs ht
    refine ⟨?_, ?_⟩
    · show IsSmoothSections F ζ hζ U R P H (s.val + t.val)
      intro i
      have h : ((s.val + t.val) i).val = fun x => (s.val i).val x + (t.val i).val x := by
        funext x; simp
      rw [h]; exact (hs.1 i).add (ht.1 i)
    · refine (hs.2.add ht.2).mono (fun b hb => ?_)
      intro h0
      exact hb (le_antisymm (h0 ▸ sectionNorm_add_le F ζ hζ U R P H s.val t.val b)
        (sectionNorm_nonneg F ζ hζ U R P H (s.val + t.val) b))
  smul_mem' := by
    intro c s hs
    refine ⟨?_, ?_⟩
    · show IsSmoothSections F ζ hζ U R P H (c • s.val)
      intro i
      have h : ((c • s.val) i).val = fun x => c • (s.val i).val x := by
        funext x; simp
      rw [h]; exact (hs.1 i).const_smul c
    · change HasCompactSupport (current_sectionNorm (c • s.val))
      have heq : current_sectionNorm (c • s.val) =
          (fun _ => ‖c‖) * current_sectionNorm s.val := by
        rw [sectionNorm_smul]
        funext b; rfl
      rw [heq]
      exact HasCompactSupport.mul_left (f := fun _ => ‖c‖)
        (f' := current_sectionNorm s.val) hs.2

def smoothCompactSectionEmbedding : SmoothCompactL2Sections F ζ hζ U R P H →ₗ[ℂ]
    current_L2Line :=
  (current_mk).comp (SmoothCompactL2Sections F ζ hζ U R P H).subtype

theorem smoothCompactSectionEmbedding_injective :
    Function.Injective (smoothCompactSectionEmbedding F ζ hζ U R P H) := by
  intro s t hst
  let s₀ : ContinuousL2Sections F ζ hζ U R P H :=
    ⟨s.val, fun i => (s.property.1 i).continuous⟩
  let t₀ : ContinuousL2Sections F ζ hζ U R P H :=
    ⟨t.val, fun i => (t.property.1 i).continuous⟩
  have heq : continuousSectionEmbedding F ζ hζ U R P H s₀ =
      continuousSectionEmbedding F ζ hζ U R P H t₀ := hst
  have hval := congrArg Subtype.val
    (continuousSectionEmbedding_injective F ζ hζ U R P H heq)
  exact Subtype.ext hval

alias squaredNorm_measurable := _root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.squaredNorm_measurable_aux

theorem squaredNorm_pullback (s : current_Sections)
    (v : CoveredSpherical F ζ hζ U) :
    current_squaredNorm s (q F ζ hζ U v) =
      ENNReal.ofReal (‖(current_scalarRepresentative s).val v‖ ^ 2) := by
  have heq : current_S (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) = s :=
    (current_S).apply_symm_apply s
  unfold squaredNorm
  rw [← heq, sectionNorm_pullback, heq]

theorem base_restriction (s : current_Sections)
    (hs : ∀ i, Measurable (s i).val)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
    Measurable (fun b : E => current_squaredNorm s b.val) ∧
    Measurable (fun v : (q F ζ hζ U) ⁻¹' E =>
      (current_scalarRepresentative s).val v.val) ∧
    (∫⁻ b in E, current_squaredNorm s b ∂sphericalMeasure F ζ hζ R P U) =
      ∫⁻ v in (q F ζ hζ U) ⁻¹' E,
        ENNReal.ofReal (‖(current_scalarRepresentative s).val v‖ ^ 2)
          ∂coveredMeasure F ζ hζ R U := by
  have hf := (borel_iff F ζ hζ U R P H s).mp hs
  refine ⟨(squaredNorm_measurable F ζ hζ U R P H s hs).comp measurable_subtype_coe,
    hf.comp measurable_subtype_coe, ?_⟩
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) hf).restricted_pushforward E hE
  have heq : current_S (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) = s :=
    (current_S).apply_symm_apply s
  simpa only [KPContSectorFixedLineNormIntegrals.lineNorm, heq, squaredNorm] using hn.symm





















instance instMeasurableSpaceCoveredChartDomain
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x) :
    MeasurableSpace (KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O) :=
  borel _

instance instBorelSpaceCoveredChartDomain
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x) :
    BorelSpace (KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O) :=
  ⟨rfl⟩

theorem orbifold_restriction (s : current_Sections)
    (hs : ∀ i, Measurable (s i).val)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x) :
    Measurable (fun v : KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O =>
      (current_scalarRepresentative s).val
        (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O v).val) ∧
    (∀ (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) (y : O.neighborhood),
      (current_scalarRepresentative s).val
        (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
          (Quotient.mk _ (m,y))).val =
        (phaseCoefficient F ζ hζ U R P H s i m y.val : ℂ)) ∧
    (∀ (ε : rootsOfUnity 3 F) (y : O.neighborhood),
      current_squaredNorm s
        (q F ζ hζ U (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
          (Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε,y))).val) =
        ENNReal.ofReal (‖(s i).val y.val‖ ^ 2)) := by
  have hf := (borel_iff F ζ hζ U R P H s).mp hs
  have heq : current_S (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) = s :=
    (current_S).apply_symm_apply s
  refine ⟨hf.comp (measurable_subtype_coe.comp
    (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O).measurable), ?_, ?_⟩
  · intro m y
    simpa only [heq] using orbifold_restriction_commutes F ζ hζ U R P H
      (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) i x O m y
  · intro ε y
    rw [squaredNorm_pullback,
      KPContSectorPhaseComponentCharts.coveredChart_mk, scalarRepresentative_mk]
    have hc : ((H.atlas U).scalar_realization.symm s).val
        (y.val, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) =
        (chi F ζ hζ ε : ℂ) * (s i).val y.val := by
      simpa only [scalarRepresentative_mk, heq] using phase_lift_formula
        F ζ hζ U R P H (_root_.DedekindZetaZeroFree.KPContSectorLineL2Isometry.context_scalarRepresentative s) i ε y.val
    rw [hc, norm_mul, chi_coe, chi_norm, one_mul]

structure RealizationIdentities : Prop where
  borel : ∀ s : current_Sections,
    (∀ i, Measurable (s i).val) ↔ Measurable (current_scalarRepresentative s).val
  reconstruction : ∀ (s : current_Sections)
      (x : SymmetricSpace F) (c : FiniteCover F ζ hζ),
    (current_scalarRepresentative s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x,c)) =
        ((H.atlas U).scalar_realization.symm s).val (x,c)
  null_relation : ∀ s t : current_BorelL2Sections,
    current_mk s = current_mk t ↔
      current_squaredNorm (s.val - t.val) =ᵐ[current_sphericalMeasure R P U] 0
  norm_formula : ∀ s : current_BorelL2Sections,
    ‖mk F ζ hζ U R P H s‖ ^ 2 = (current_normIntegral s.val).toReal
  extended_norm_formula : ∀ s : current_BorelL2Sections,
    ENNReal.ofReal (‖mk F ζ hζ U R P H s‖ ^ 2) = current_normIntegral s.val
  forward : ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (f : BorelL2Scalars F ζ hζ U R),
    f.property.2.toLp f.val.val = (u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) →
      sectorLineIsometry F ζ hζ U R P H u = current_mk (borelS F ζ hζ U R P H f)
  inverse : ∀ s : current_BorelL2Sections,
    ((sectorLineIsometry F ζ hζ U R P H).symm (current_mk s) :
      KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
        (current_representative_memLp s).toLp
          (current_scalarRepresentative s.val).val
  continuous_scalars : Function.Injective (continuousScalarEmbedding F ζ hζ U R P H)
  continuous_sections : Function.Injective (continuousSectionEmbedding F ζ hζ U R P H)
  smooth_compact_scalars : Function.Injective (smoothCompactScalarEmbedding F ζ hζ U R P H)
  smooth_compact_sections : Function.Injective (smoothCompactSectionEmbedding F ζ hζ U R P H)
  restricted_norm : ∀ (s : current_Sections), (∀ i, Measurable (s i).val) →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
      (∫⁻ b in E, current_squaredNorm s b ∂sphericalMeasure F ζ hζ R P U) =
        ∫⁻ v in (q F ζ hζ U) ⁻¹' E,
          ENNReal.ofReal (‖(current_scalarRepresentative s).val v‖ ^ 2)
            ∂coveredMeasure F ζ hζ R U
  restricted_borel : ∀ (s : current_Sections), (∀ i, Measurable (s i).val) →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
      Measurable (fun b : E => current_squaredNorm s b.val) ∧
      Measurable (fun v : (q F ζ hζ U) ⁻¹' E =>
        (current_scalarRepresentative s).val v.val)
  chart_borel : ∀ (s : current_Sections), (∀ i, Measurable (s i).val) →
    ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x),
      Measurable (fun v : KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O =>
        (current_scalarRepresentative s).val
          (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O v).val)
  chart_norm : ∀ (s : current_Sections)
      (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
      (ε : rootsOfUnity 3 F) (y : O.neighborhood),
    current_squaredNorm s
      (q F ζ hζ U (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
        (Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε,y))).val) =
        ENNReal.ofReal (‖(s i).val y.val‖ ^ 2)

end DedekindZetaZeroFree.KPContSectorLineL2Isometry

namespace DedekindZetaZeroFree

theorem kp_cont_sector_line_l2_isometry
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContSectorLineL2Isometry.RealizationIdentities F ζ hζ U R P H := {
    borel := KPContSectorLineL2Isometry.borel_iff F ζ hζ U R P H
    reconstruction := KPContSectorLineL2Isometry.scalarRepresentative_mk F ζ hζ U R P H
    null_relation := KPContSectorLineL2Isometry.mk_eq_mk_iff F ζ hζ U R P H
    norm_formula := KPContSectorLineL2Isometry.norm_sq F ζ hζ U R P H
    extended_norm_formula := KPContSectorLineL2Isometry.ofReal_norm_sq F ζ hζ U R P H
    forward := KPContSectorLineL2Isometry.sectorLineIsometry_representative F ζ hζ U R P H
    inverse := KPContSectorLineL2Isometry.sectorLineIsometry_symm_mk F ζ hζ U R P H
    continuous_scalars := KPContSectorLineL2Isometry.continuousScalarEmbedding_injective F ζ hζ U R P H
    continuous_sections := KPContSectorLineL2Isometry.continuousSectionEmbedding_injective F ζ hζ U R P H
    smooth_compact_scalars := KPContSectorLineL2Isometry.smoothCompactScalarEmbedding_injective F ζ hζ U R P H
    smooth_compact_sections := KPContSectorLineL2Isometry.smoothCompactSectionEmbedding_injective F ζ hζ U R P H
    restricted_norm := fun s hs E hE =>
      (KPContSectorLineL2Isometry.base_restriction F ζ hζ U R P H s hs E hE).2.2
    restricted_borel := fun s hs E hE =>
      ⟨(KPContSectorLineL2Isometry.base_restriction F ζ hζ U R P H s hs E hE).1,
        (KPContSectorLineL2Isometry.base_restriction F ζ hζ U R P H s hs E hE).2.1⟩
    chart_borel := fun s hs i x O =>
      (KPContSectorLineL2Isometry.orbifold_restriction F ζ hζ U R P H s hs i x O).1
    chart_norm := by
      intro s i x O ε y
      rw [KPContSectorLineL2Isometry.squaredNorm_pullback,
        KPContSectorPhaseComponentCharts.coveredChart_mk]
      have hp := KPContSectorSmoothFramesSupport.phase_lift_formula F ζ hζ U R P H
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s) i ε y.val
      have heq : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
          (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s) = s :=
        (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply s
      rw [hp, heq, norm_mul, KPContSectorCoveredQuotientVocabulary.chi_coe,
        KPContSectorCoveredQuotientVocabulary.chi_norm, one_mul]
  }

end DedekindZetaZeroFree

end
