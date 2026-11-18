module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesLog
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Measure Set Filter
open scoped NNReal Topology

/-- The literal radial weight is finite on compact subsets of positive radius. -/
instance bellmanRadialWeight_finiteOnCompacts (β : ℝ) :
    IsFiniteMeasureOnCompacts (bellmanRadialWeight β) := by
  apply bellman_withDensity_finiteOnCompacts
  apply Continuous.rpow_const continuous_subtype_val
  intro s
  exact Or.inl s.property.ne'

/-- The literal radial weight is sigma finite. -/
instance bellmanRadialWeight_sigmaFinite (β : ℝ) : SigmaFinite (bellmanRadialWeight β) := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance

/-- Positive radial Lebesgue measure gives positive mass to every nonempty open radial set. -/
instance bellmanPositiveTimeVolume_isOpenPosMeasure :
    IsOpenPosMeasure bellmanPositiveTimeVolume := by
  constructor
  intro U hU hUne
  have he : Topology.IsOpenEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
    isOpen_Ioi.isOpenEmbedding_subtypeVal
  have ho : IsOpen (Subtype.val '' U : Set ℝ) := he.isOpen_iff_image_isOpen.mp hU
  rw [bellmanPositiveTimeVolume, he.measurableEmbedding.comap_apply,
    Measure.restrict_apply ho.measurableSet]
  have hs : (Subtype.val '' U : Set ℝ) ⊆ Ioi (0 : ℝ) := by
    rintro s ⟨t, _, rfl⟩
    exact t.property
  rw [inter_eq_left.mpr hs]
  exact (ho.measure_pos volume (hUne.image Subtype.val)).ne'

/-- The source radial measure is positive on every nonempty open radial set. -/
instance bellmanRadialWeight_isOpenPosMeasure (β : ℝ) :
    IsOpenPosMeasure (bellmanRadialWeight β) := by
  have hm : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (3 - β))) := by fun_prop
  have hn : ∀ᵐ s ∂bellmanPositiveTimeVolume,
      ENNReal.ofReal (s.val ^ (3 - β)) ≠ 0 :=
    ae_of_all _ fun s => (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos s.property _)).ne'
  have hac := withDensity_absolutelyContinuous' hm.aemeasurable hn
  constructor
  intro U hU hUne hz
  exact (hU.measure_pos bellmanPositiveTimeVolume hUne).ne'
    (hac hz)


/-- The first-coordinate marginal with the second coordinate restricted to B. -/
def bellmanFirstSlice (ρ : Measure (ℝ × ℝ)) (B : Set ℝ) : Measure ℝ :=
  Measure.map Prod.fst (ρ.restrict (univ ×ˢ B))

/-- The angular section obtained by restricting log radius to the unit interval. -/
def bellmanUnitSection (ρ : Measure (ℝ × ℝ)) : Measure ℝ :=
  Measure.map Prod.snd (ρ.restrict (Ioc (0 : ℝ) 1 ×ˢ univ))

/-- The first slice evaluates a rectangle of the original measure. -/
theorem bellmanFirstSlice_apply (ρ : Measure (ℝ × ℝ)) {A B : Set ℝ}
    (hA : MeasurableSet A) :
    bellmanFirstSlice ρ B A = ρ (A ×ˢ B) := by
  rw [bellmanFirstSlice, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext q
  simp

/-- The unit section evaluates the unit-radius rectangle of the original measure. -/
theorem bellmanUnitSection_apply (ρ : Measure (ℝ × ℝ)) {B : Set ℝ}
    (hB : MeasurableSet B) :
    bellmanUnitSection ρ B = ρ (Ioc (0 : ℝ) 1 ×ˢ B) := by
  rw [bellmanUnitSection, Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext q
  simp
  tauto

/-- A compact angular slice has finite mass on compact radial sets. -/
theorem bellmanFirstSlice_finiteOnCompacts (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ] {B : Set ℝ} (hB : IsCompact B) :
    IsFiniteMeasureOnCompacts (bellmanFirstSlice ρ B) where
  lt_top_of_isCompact A hA := by
    rw [bellmanFirstSlice_apply ρ hA.measurableSet]
    exact (hA.prod hB).measure_lt_top

/-- The unit-radius angular section is locally finite. -/
theorem bellmanUnitSection_finiteOnCompacts (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ] : IsFiniteMeasureOnCompacts (bellmanUnitSection ρ) where
  lt_top_of_isCompact B hB := by
    rw [bellmanUnitSection_apply ρ hB.measurableSet]
    exact lt_of_le_of_lt (measure_mono (prod_mono Ioc_subset_Icc_self Subset.rfl))
      (isCompact_Icc.prod hB).measure_lt_top

/-- Translating only the first coordinate commutes with restricting the angular coordinate. -/
theorem bellmanFirstSlice_invariant (ρ : Measure (ℝ × ℝ))
    (hρ : ∀ a : ℝ, Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2)) ρ = ρ)
    {B : Set ℝ} (hB : MeasurableSet B) : IsAddLeftInvariant (bellmanFirstSlice ρ B) := by
  constructor
  intro a
  let τ : ℝ × ℝ → ℝ × ℝ := fun q => (a + q.1, q.2)
  have ht : Measurable τ := by fun_prop
  have hpre : τ ⁻¹' (univ ×ˢ B) = univ ×ˢ B := by
    ext q
    simp [τ]
  have hm : Measure.map τ (ρ.restrict (univ ×ˢ B)) = ρ.restrict (univ ×ˢ B) := by
    calc
      _ = (Measure.map τ ρ).restrict (univ ×ˢ B) := by
        rw [Measure.restrict_map ht (MeasurableSet.univ.prod hB), hpre]
      _ = _ := by rw [hρ a]
  change Measure.map (fun x : ℝ => a + x)
    (Measure.map Prod.fst (ρ.restrict (univ ×ˢ B))) = _
  rw [Measure.map_map (by fun_prop) measurable_fst]
  calc
    _ = Measure.map Prod.fst (Measure.map τ (ρ.restrict (univ ×ˢ B))) := by
      rw [Measure.map_map measurable_fst ht]
      rfl
    _ = _ := by rw [hm]; rfl

/-- Haar uniqueness determines every rectangle with compact angular side. -/
theorem bellman_translation_rectangle (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ]
    (hρ : ∀ a : ℝ, Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2)) ρ = ρ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : IsCompact B) :
    ρ (A ×ˢ B) = volume A * bellmanUnitSection ρ B := by
  let ν := bellmanFirstSlice ρ B
  let : IsFiniteMeasureOnCompacts ν := bellmanFirstSlice_finiteOnCompacts ρ hB
  let : IsAddLeftInvariant ν := bellmanFirstSlice_invariant ρ hρ hB.measurableSet
  have he :=
    isAddLeftInvariant_eq_smul ν volume
  have hc : addHaarScalarFactor ν volume = bellmanUnitSection ρ B := by
    have h := congrArg (fun m : Measure ℝ => m (Ioc 0 1)) he
    rw [Measure.smul_apply, Real.volume_Ioc] at h
    norm_num at h
    rw [bellmanUnitSection_apply ρ hB.measurableSet]
    exact (bellmanFirstSlice_apply ρ measurableSet_Ioc).symm.trans h
      |>.symm
  rw [← bellmanFirstSlice_apply ρ hA]
  change ν A = _
  rw [he, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, mul_comm]


/-- Closed bounded intervals form finite spanning sets for a locally finite real measure. -/
theorem bellman_finiteSpanning_closedIntervals (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] :
    Nonempty (μ.FiniteSpanningSetsIn {S | ∃ a b : ℝ, a ≤ b ∧ Icc a b = S}) := by
  refine ⟨{
    set := fun n => Icc (-(n : ℝ)) (n : ℝ)
    set_mem := fun n => ⟨_, _, neg_le_self (Nat.cast_nonneg n), rfl⟩
    finite := fun _ => isCompact_Icc.measure_lt_top
    spanning := ?_ }⟩
  ext x
  simp
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact ⟨n, by linarith only [neg_abs_le x, hn], by linarith only [le_abs_self x, hn]⟩

/-- Radial translation invariance forces a product with the unit-radius angular section. -/
theorem bellman_translation_factorization (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ]
    (hρ : ∀ a : ℝ, Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2)) ρ = ρ) :
    ρ = (volume : Measure ℝ).prod (bellmanUnitSection ρ) := by
  let F := bellmanUnitSection ρ
  let : IsFiniteMeasureOnCompacts F := bellmanUnitSection_finiteOnCompacts ρ
  let C : Set (Set ℝ) := {S | ∃ a b : ℝ, a ≤ b ∧ Icc a b = S}
  have hgen :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Icc ℝ)).symm
  have hpi : IsPiSystem C := isPiSystem_Icc id id
  obtain ⟨hvol⟩ := bellman_finiteSpanning_closedIntervals (volume : Measure ℝ)
  obtain ⟨hF⟩ := bellman_finiteSpanning_closedIntervals F
  apply Eq.symm
  apply Measure.prod_eq_generateFrom hgen hgen hpi hpi hvol hF
  rintro A ⟨a, b, hab, rfl⟩ B ⟨c, d, hcd, rfl⟩
  exact bellman_translation_rectangle ρ hρ measurableSet_Icc isCompact_Icc


/-- The actual reweighted log-coordinate measure remains finite on compact sets. -/
theorem bellmanLogAngularMeasure_finiteOnCompacts (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularPullback μ) :=
    bellmanAngularPullback_finiteOnCompacts μ hμ
  have hw : Continuous (fun w : BellmanPositiveTime × ℝ => w.1.val ^ (β - 4)) := by
    apply Continuous.rpow_const
    · fun_prop
    · intro w
      exact Or.inl w.1.property.ne'
  let : IsFiniteMeasureOnCompacts
      ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β)) :=
    bellman_withDensity_finiteOnCompacts (bellmanAngularPullback μ) _ hw
  exact bellman_map_homeomorph_finiteOnCompacts bellmanLogAngularHomeomorph _

/-- Homogeneity alone produces a literal angular measure after passing to log radius. -/
theorem bellmanLogAngularMeasure_factorization (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      (volume : Measure ℝ).prod (bellmanUnitSection (bellmanLogAngularMeasure β μ)) := by
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  exact bellman_translation_factorization _ hd.logAngularMeasure_invariant


/-- The multiplicatively invariant reference radial measure is literally ds/s. -/
def bellmanRadialHaar : Measure BellmanPositiveTime :=
  bellmanPositiveTimeVolume.withDensity (fun s => ENNReal.ofReal s.val⁻¹)

/-- The reference measure is finite on compact subsets of the positive radial carrier. -/
instance bellmanRadialHaar_finiteOnCompacts : IsFiniteMeasureOnCompacts bellmanRadialHaar := by
  apply bellman_withDensity_finiteOnCompacts
  exact continuous_subtype_val.inv₀ (fun s => s.property.ne')

/-- The reference radial measure is sigma finite. -/
instance bellmanRadialHaar_sigmaFinite : SigmaFinite bellmanRadialHaar := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance

/-- The actual ds/s measure is invariant under every positive radial scaling. -/
theorem map_bellmanRadialHaar_radialScale (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanRadialScale r hr) bellmanRadialHaar = bellmanRadialHaar := by
  have hf : Measurable (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
    fun_prop
  rw [bellmanRadialHaar, bellman_map_withDensity _ _ _ hf,
    map_bellmanPositiveTimeVolume_radialScale, withDensity_smul_measure]
  have he : (fun s : BellmanPositiveTime =>
      ENNReal.ofReal ((bellmanRadialScale r hr).symm s).val⁻¹) =
      ENNReal.ofReal r • (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
    funext s
    change ENNReal.ofReal (r⁻¹ * s.val)⁻¹ = ENNReal.ofReal r * ENNReal.ofReal s.val⁻¹
    rw [mul_inv_rev, inv_inv, ← ENNReal.ofReal_mul hr.le, mul_comm]
  rw [he, withDensity_smul _ hf, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  simp [inv_mul_cancel₀ hr.ne']

/-- The ds/s measure in log radius. -/
def bellmanLogRadialHaar : Measure ℝ :=
  Measure.map bellmanLogRadiusHomeomorph bellmanRadialHaar

/-- The reference log-radius measure is finite on compact sets. -/
instance bellmanLogRadialHaar_finiteOnCompacts :
    IsFiniteMeasureOnCompacts bellmanLogRadialHaar where
  lt_top_of_isCompact K hK := by
    rw [bellmanLogRadialHaar, Measure.map_apply bellmanLogRadiusHomeomorph.measurable
      hK.measurableSet]
    have he : bellmanLogRadiusHomeomorph ⁻¹' K = bellmanLogRadiusHomeomorph.symm '' K := by
      ext q
      constructor
      · intro hq
        exact ⟨bellmanLogRadiusHomeomorph q, hq,
          bellmanLogRadiusHomeomorph.symm_apply_apply q⟩
      · rintro ⟨z, hz, rfl⟩
        change bellmanLogRadiusHomeomorph (bellmanLogRadiusHomeomorph.symm z) ∈ K
        rw [bellmanLogRadiusHomeomorph.apply_symm_apply]
        exact hz
    rw [he]
    exact (hK.image bellmanLogRadiusHomeomorph.symm.continuous).measure_lt_top

/-- Positive radial scaling gives actual translation invariance in log radius. -/
instance bellmanLogRadialHaar_addInvariant : IsAddLeftInvariant bellmanLogRadialHaar := by
  constructor
  intro a
  rw [bellmanLogRadialHaar,
    Measure.map_map (by fun_prop) bellmanLogRadiusHomeomorph.measurable]
  have he : (fun x : ℝ => a + x) ∘ bellmanLogRadiusHomeomorph =
      bellmanLogRadiusHomeomorph ∘ bellmanRadialScale (Real.exp a) (Real.exp_pos a) := by
    funext s
    change a + Real.log s.val = Real.log (Real.exp a * s.val)
    rw [Real.log_mul (Real.exp_ne_zero a) s.property.ne', Real.log_exp]
  rw [he, ← Measure.map_map bellmanLogRadiusHomeomorph.measurable
    (bellmanRadialScale (Real.exp a) (Real.exp_pos a)).measurable,
    map_bellmanRadialHaar_radialScale]

/-- The reference radial measure is nonzero. -/
theorem bellmanRadialHaar_ne_zero : bellmanRadialHaar ≠ 0 := by
  intro h
  have hac : bellmanPositiveTimeVolume ≪ bellmanRadialHaar :=
    withDensity_absolutelyContinuous' (by fun_prop) (ae_of_all _ fun s =>
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr s.property)).ne')
  have hz : bellmanPositiveTimeVolume = 0 := by
    rw [h] at hac
    exact absolutelyContinuous_zero_iff.mp hac
  have hu := bellmanPositiveTimeVolume_univ
  rw [hz] at hu
  change 0 = ⊤ at hu
  exact ENNReal.zero_ne_top hu


/-- The finite Haar normalization factor of the literal log-radius reference measure. -/
def bellmanRadialHaarFactor : ℝ≥0 :=
  addHaarScalarFactor bellmanLogRadialHaar (volume : Measure ℝ)

/-- The actual log-radius reference measure is its finite Haar factor times volume. -/
theorem bellmanLogRadialHaar_eq_smul_volume :
    bellmanLogRadialHaar = bellmanRadialHaarFactor • (volume : Measure ℝ) :=
  isAddLeftInvariant_eq_smul bellmanLogRadialHaar volume

/-- The reference Haar factor is strictly positive, so normalization never divides by zero. -/
theorem bellmanRadialHaarFactor_ne_zero : bellmanRadialHaarFactor ≠ 0  := by
  intro h
  have he := bellmanLogRadialHaar_eq_smul_volume
  rw [h, zero_smul] at he
  exact ((Measure.map_ne_zero_iff bellmanLogRadiusHomeomorph.measurable.aemeasurable).mpr bellmanRadialHaar_ne_zero) he


/-- The normalized unit-log-radius section of the actual reweighted homogeneous measure. -/
def bellmanAngularMeasure (β : ℝ) (μ : Measure BellmanPuncturedPlane) : Measure ℝ :=
  bellmanRadialHaarFactor⁻¹ • bellmanUnitSection (bellmanLogAngularMeasure β μ)

/-- The actual angular measure is finite on compact angular sets. -/
theorem bellmanAngularMeasure_finiteOnCompacts (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  let : IsFiniteMeasureOnCompacts (bellmanUnitSection (bellmanLogAngularMeasure β μ)) :=
    bellmanUnitSection_finiteOnCompacts _
  unfold bellmanAngularMeasure
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.coe_ne_top

/-- The actual angular measure is inner regular. -/
theorem bellmanAngularMeasure_innerRegular (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ) :
    Measure.InnerRegular (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  infer_instance

/-- The weighted log-coordinate factorization uses the actual radial reference measure. -/
theorem bellmanLogAngularMeasure_factorization_radial (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      bellmanLogRadialHaar.prod (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  let : IsFiniteMeasureOnCompacts (bellmanUnitSection (bellmanLogAngularMeasure β μ)) :=
    bellmanUnitSection_finiteOnCompacts _
  rw [bellmanLogRadialHaar_eq_smul_volume, bellmanAngularMeasure,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    mul_inv_cancel₀ bellmanRadialHaarFactor_ne_zero, one_smul]
  exact bellmanLogAngularMeasure_factorization β μ hμ hd

/-- The actual coordinate measure after degree removal factors as ds/s times its angular
measure. -/
theorem bellmanAngularPullback_reweighted_factorization (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    (bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β) =
      bellmanRadialHaar.prod (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  apply bellmanLogAngularHomeomorph.measurableEmbedding.map_injective
  change bellmanLogAngularMeasure β μ = _
  change bellmanLogAngularMeasure β μ =
    Measure.map (Prod.map bellmanLogRadiusHomeomorph id)
      (bellmanRadialHaar.prod (bellmanAngularMeasure β μ))
  rw [← Measure.map_prod_map _ _ bellmanLogRadiusHomeomorph.measurable measurable_id,
    Measure.map_id]
  exact bellmanLogAngularMeasure_factorization_radial β μ hμ hd


/-- Undoing the degree weight on ds/s gives exactly s^(3-β) ds. -/
theorem bellmanRadialHaar_reweight (β : ℝ) :
    bellmanRadialHaar.withDensity
      (fun s : BellmanPositiveTime => ENNReal.ofReal (s.val ^ (4 - β))) =
      bellmanRadialWeight β := by
  have h1 : Measurable (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
    fun_prop
  have h2 : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (4 - β))) := by fun_prop
  rw [bellmanRadialHaar, ← withDensity_mul _ h1 h2]
  unfold bellmanRadialWeight
  congr 1
  funext s
  change ENNReal.ofReal s.val⁻¹ * ENNReal.ofReal (s.val ^ (4 - β)) = _
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr s.property.le),
    ← Real.rpow_neg_one, ← Real.rpow_add s.property]
  congr 1
  congr 1
  ring

/-- The inverse degree-removing weight is the reciprocal real-power weight. -/
theorem bellmanRadialDegreeWeight_inv (β : ℝ) (w : BellmanPositiveTime × ℝ) :
    (bellmanRadialDegreeWeight β w)⁻¹ = ENNReal.ofReal (w.1.val ^ (4 - β)) := by
  rw [bellmanRadialDegreeWeight,
    ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos w.1.property _),
    ← Real.rpow_neg w.1.property.le]
  congr 1
  congr 1
  ring

/-- The actual homogeneous coordinate measure is s^(3-β) ds times its actual angular measure. -/
theorem bellmanAngularPullback_factorization (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanAngularPullback μ =
      (bellmanRadialWeight β).prod (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  have hn : ∀ᵐ w ∂bellmanAngularPullback μ, bellmanRadialDegreeWeight β w ≠ 0 :=
    ae_of_all _ fun w => (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos w.1.property _)).ne'
  have ht : ∀ᵐ w ∂bellmanAngularPullback μ, bellmanRadialDegreeWeight β w ≠ ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_ne_top
  have he := congrArg (fun ρ : Measure (BellmanPositiveTime × ℝ) =>
    ρ.withDensity (fun w => (bellmanRadialDegreeWeight β w)⁻¹))
      (bellmanAngularPullback_reweighted_factorization β μ hμ hd)
  rw [withDensity_inv_same (measurable_bellmanRadialDegreeWeight β) hn ht] at he
  rw [(funext (bellmanRadialDegreeWeight_inv β))] at he
  have hm : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (4 - β))) := by fun_prop
  rw [← prod_withDensity_left (μ := bellmanRadialHaar)
    (ν := bellmanAngularMeasure β μ) hm, bellmanRadialHaar_reweight] at he
  exact he

/-- Mapping the proved product representation yields the exact positive-position restriction. -/
theorem bellmanAngularMeasure_representation (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β (bellmanAngularMeasure β μ) := by
  rw [← map_bellmanAngularPullback μ, bellmanAngularPullback_factorization β μ hμ hd]
  rfl


/-- Pulling back through the angular embedding preserves measure comparison. -/
theorem bellmanAngularPullback_mono {μ η : Measure BellmanPuncturedPlane} (h : μ ≤ η) :
    bellmanAngularPullback μ ≤ bellmanAngularPullback η := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [bellmanAngularPullback, bellmanAngularPullback,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.comap_apply μ E,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.comap_apply η E]
  exact h _

/-- Weighting both compared measures by the same nonnegative density preserves comparison. -/
theorem bellman_withDensity_mono_measure {A : Type*} [MeasurableSpace A]
    {μ η : Measure A} (h : μ ≤ η) (f : A → ENNReal) :
    μ.withDensity f ≤ η.withDensity f := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [withDensity_apply _ hE, withDensity_apply _ hE]
  exact lintegral_mono' (Measure.restrict_mono Subset.rfl h) le_rfl

/-- The canonical angular section preserves comparison of the original measures. -/
theorem bellmanAngularMeasure_mono (β : ℝ)
    {μ η : Measure BellmanPuncturedPlane} (h : μ ≤ η) :
    bellmanAngularMeasure β μ ≤ bellmanAngularMeasure β η := by
  have hl := Measure.map_mono (bellman_withDensity_mono_measure (bellmanAngularPullback_mono h) (bellmanRadialDegreeWeight β)) bellmanLogAngularHomeomorph.measurable
  unfold bellmanAngularMeasure bellmanUnitSection bellmanLogAngularMeasure
  exact smul_le_smul_left _ (Measure.map_mono (Measure.restrict_mono (s := Ioc 0 1 ×ˢ univ) Subset.rfl hl) measurable_snd)

/-- Angular extraction commutes with multiplying the original measure by a scalar. -/
theorem bellmanAngularMeasure_smul (β : ℝ) (c : ENNReal)
    (μ : Measure BellmanPuncturedPlane) :
    bellmanAngularMeasure β (c • μ) = c • bellmanAngularMeasure β μ := by
  unfold bellmanAngularMeasure bellmanUnitSection bellmanLogAngularMeasure
    bellmanAngularPullback
  rw [Measure.comap_smul, withDensity_smul_measure, Measure.map_smul,
    Measure.restrict_smul, Measure.map_smul, smul_comm]
  all_goals fun_prop


/-- Homogeneous compared Radon measures have the exact source angular representation. -/
theorem angular_disintegration (R β : ℝ) (_hR : 1 ≤ R) (_hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ F H : Measure ℝ,
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      IsFiniteMeasureOnCompacts F ∧ Measure.InnerRegular F ∧
      IsFiniteMeasureOnCompacts H ∧ Measure.InnerRegular H ∧ F ≤ H ∧
      H ≤ ENNReal.ofReal R • F := by
  refine ⟨bellmanAngularMeasure β μ, bellmanAngularMeasure β η, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨bellmanAngularMeasure_representation β μ hp.1.1 hp.2.2.2.2.2.2.1,
      bellmanAngularMeasure_representation β η hp.2.1.1 hp.2.2.2.2.2.2.2⟩
  · exact bellmanAngularMeasure_finiteOnCompacts β μ hp.1.1
  · exact bellmanAngularMeasure_innerRegular β μ hp.1.1
  · exact bellmanAngularMeasure_finiteOnCompacts β η hp.2.1.1
  · exact bellmanAngularMeasure_innerRegular β η hp.2.1.1
  · apply bellmanAngularMeasure_mono
    simpa using hp.2.2.2.1
  · rw [← bellmanAngularMeasure_smul]
    exact bellmanAngularMeasure_mono β hp.2.2.2.2.1


/-- The real-valued radius used in a separated test on positive position. -/
def bellmanTestRadius (q : ℝ × ℝ) : ℝ := q.1 ^ ((3 : ℝ)⁻¹)

/-- The angular coordinate used in a separated test on positive position. -/
def bellmanTestAngle (q : ℝ × ℝ) : ℝ := q.2 / bellmanTestRadius q

/-- The literal separated expression, before extension across the position axis. -/
def bellmanSeparatedExpression (ζ φ : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  ζ (bellmanTestRadius q) * φ (bellmanTestAngle q)

/-- The radial coordinate equals s at the source coordinate point. -/
theorem bellmanTestRadius_angularPoint (w : BellmanPositiveTime × ℝ) :
    bellmanTestRadius (bellmanAngularPoint w).val = w.1.val := by
  exact Real.pow_rpow_inv_natCast w.1.property.le (by norm_num : 3 ≠ 0)

/-- The angular coordinate equals y at the source coordinate point. -/
theorem bellmanTestAngle_angularPoint (w : BellmanPositiveTime × ℝ) :
    bellmanTestAngle (bellmanAngularPoint w).val = w.2 := by
  rw [bellmanTestAngle, bellmanTestRadius_angularPoint]
  change w.1.val * w.2 / w.1.val = w.2
  field_simp [w.1.property.ne']

/-- The radial coordinate has derivative dX/(3s²) on positive position. -/
theorem bellmanTestRadius_hasFDerivAt (w : BellmanPositiveTime × ℝ) :
    HasFDerivAt bellmanTestRadius
      ((1 / (3 * w.1.val ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (bellmanAngularPoint w).val := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := (bellmanAngularPoint w).val)).rpow_const
    (p := 3⁻¹) (Or.inl (pow_pos w.1.property 3).ne')
  change HasFDerivAt bellmanTestRadius
    ((3⁻¹ * ((bellmanAngularPoint w).val.1 ^ (3⁻¹ - 1))) •
      ContinuousLinearMap.fst ℝ ℝ ℝ) _ at hd
  have he : ((bellmanAngularPoint w).val.1 ^ ((3 : ℝ)⁻¹ - 1)) =
      (w.1.val ^ 2)⁻¹ := by
    change (w.1.val ^ 3) ^ (3⁻¹ - 1) = _
    rw [← Real.rpow_natCast_mul w.1.property.le]
    norm_num
  rw [he] at hd
  convert hd using 1
  congr 1
  simp
  ring



/-- The chain rule for a separated expression in the actual angular coordinates. -/
theorem bellmanSeparatedExpression_hasFDerivAt (ζ φ : ℝ → ℝ)
    (w : BellmanPositiveTime × ℝ) (hζ : DifferentiableAt ℝ ζ w.1.val)
    (hφ : DifferentiableAt ℝ φ w.2) :
    HasFDerivAt (bellmanSeparatedExpression ζ φ)
      ((ζ w.1.val * deriv φ w.2) •
        (w.1.val⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ -
          (w.2 / (3 * w.1.val ^ 3)) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (φ w.2 * deriv ζ w.1.val) •
          ((1 / (3 * w.1.val ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ))
      (bellmanAngularPoint w).val  := by
  have bellmanTestAngle_hasFDerivAt :
      HasFDerivAt bellmanTestAngle
      (w.1.val⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ -
        (w.2 / (3 * w.1.val ^ 3)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (bellmanAngularPoint w).val := by
    have hn : bellmanTestRadius (bellmanAngularPoint w).val ≠ 0 := by
      rw [bellmanTestRadius_angularPoint]
      exact w.1.property.ne'
    have hi := (hasDerivAt_inv hn).comp_hasFDerivAt (bellmanAngularPoint w).val
      (bellmanTestRadius_hasFDerivAt w)
    have hd := (hasFDerivAt_snd (𝕜 := ℝ) (p := (bellmanAngularPoint w).val)).mul hi
    rw [bellmanTestRadius_angularPoint] at hd
    convert! hd using 1
    rw [Function.comp_apply, bellmanTestRadius_angularPoint]
    apply ContinuousLinearMap.ext
    intro z
    change w.1.val⁻¹ * z.2 - w.2 / (3 * w.1.val ^ 3) * z.1 =
      (w.1.val * w.2) * (-(w.1.val ^ 2)⁻¹ *
        (1 / (3 * w.1.val ^ 2) * z.1)) + w.1.val⁻¹ * z.2
    field_simp [w.1.property.ne']
    ring
  have hz : HasDerivAt ζ (deriv ζ w.1.val)
      (bellmanTestRadius (bellmanAngularPoint w).val) := by
    rw [bellmanTestRadius_angularPoint]
    exact hζ.hasDerivAt
  have hp : HasDerivAt φ (deriv φ w.2)
      (bellmanTestAngle (bellmanAngularPoint w).val) := by
    rw [bellmanTestAngle_angularPoint]
    exact hφ.hasDerivAt
  convert! (hz.comp_hasFDerivAt (bellmanAngularPoint w).val (bellmanTestRadius_hasFDerivAt w)).mul (hp.comp_hasFDerivAt (bellmanAngularPoint w).val (bellmanTestAngle_hasFDerivAt)) using 1
  simp [bellmanTestRadius_angularPoint, bellmanTestAngle_angularPoint, smul_smul, mul_assoc]

/-- The transport derivative has exactly the source factors y/(3s) and -y²/(3s²). -/
theorem bellmanSeparatedExpression_transport (ζ φ : ℝ → ℝ)
    (w : BellmanPositiveTime × ℝ) (hζ : DifferentiableAt ℝ ζ w.1.val)
    (hφ : DifferentiableAt ℝ φ w.2) :
    (bellmanAngularPoint w).val.2 *
      fderiv ℝ (bellmanSeparatedExpression ζ φ) (bellmanAngularPoint w).val (1, 0) =
      w.2 / (3 * w.1.val) * deriv ζ w.1.val * φ w.2 -
        w.2 ^ 2 / (3 * w.1.val ^ 2) * ζ w.1.val * deriv φ w.2 := by
  rw [(bellmanSeparatedExpression_hasFDerivAt ζ φ w hζ hφ).fderiv]
  change (w.1.val * w.2) *
    ((ζ w.1.val * deriv φ w.2) * (w.1.val⁻¹ * 0 - w.2 / (3 * w.1.val ^ 3) * 1) +
      (φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 1)) = _
  field_simp [w.1.property.ne']
  ring

/-- The first velocity derivative is ζ(s)φ'(y)/s. -/
theorem bellmanSeparatedExpression_velocity (ζ φ : ℝ → ℝ)
    (w : BellmanPositiveTime × ℝ) (hζ : DifferentiableAt ℝ ζ w.1.val)
    (hφ : DifferentiableAt ℝ φ w.2) :
    fderiv ℝ (bellmanSeparatedExpression ζ φ) (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv φ w.2 / w.1.val := by
  rw [(bellmanSeparatedExpression_hasFDerivAt ζ φ w hζ hφ).fderiv]
  change (ζ w.1.val * deriv φ w.2) *
    (w.1.val⁻¹ * 1 - w.2 / (3 * w.1.val ^ 3) * 0) +
      (φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 0) = _
  simp [div_eq_mul_inv]


/-- Every positive-position point is the literal angular point of its inverse coordinates. -/
theorem bellmanAngularPoint_inverse (q : ℝ × ℝ) (hq : 0 < q.1) :
    (bellmanAngularPoint (bellmanAngularHomeomorph.symm ⟨q, hq⟩)).val = q := by
  exact congrArg Subtype.val (bellmanAngularHomeomorph.apply_symm_apply ⟨q, hq⟩)

/-- The first velocity formula holds throughout the open positive-position half-plane. -/
theorem bellmanSeparatedExpression_velocity_positive (ζ φ : ℝ → ℝ)
    (hζ : Differentiable ℝ ζ) (hφ : Differentiable ℝ φ)
    (q : ℝ × ℝ) (hq : 0 < q.1) :
    fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1) =
      bellmanSeparatedExpression ζ (deriv φ) q / bellmanTestRadius q := by
  rw [← (bellmanAngularPoint_inverse q hq)]
  rw [bellmanSeparatedExpression_velocity ζ φ (bellmanAngularHomeomorph.symm ⟨q, hq⟩) (hζ _) (hφ _)]
  rw [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint]

/-- The second velocity derivative is exactly ζ(s)φ''(y)/s². -/
theorem bellmanSeparatedExpression_velocity_second (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : BellmanPositiveTime × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1))
      (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv (deriv φ) w.2 / w.1.val ^ 2 := by
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hn : bellmanTestRadius (bellmanAngularPoint w).val ≠ 0 := by
    rw [bellmanTestRadius_angularPoint]
    exact w.1.property.ne'
  have hi := (hasDerivAt_inv hn).comp_hasFDerivAt (bellmanAngularPoint w).val
    (bellmanTestRadius_hasFDerivAt w)
  have hd := (bellmanSeparatedExpression_hasFDerivAt ζ (deriv φ) w (hζ.differentiable (by simp) _) (hφd.differentiable (by simp) _)).mul hi
  have he : (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1)) =ᶠ[
      𝓝 (bellmanAngularPoint w).val]
      (bellmanSeparatedExpression ζ (deriv φ) * (fun y => y⁻¹) ∘ bellmanTestRadius) := by
    have ho : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    filter_upwards [ho.mem_nhds (pow_pos w.1.property 3)] with q hqp
    rw [bellmanSeparatedExpression_velocity_positive ζ φ
      (hζ.differentiable (by simp)) (hφ.differentiable (by simp)) q hqp]
    rfl
  rw [(hd.congr_of_eventuallyEq he).fderiv]
  simp only [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint, Function.comp_apply]
  change (ζ w.1.val * deriv φ w.2) *
      (-(w.1.val ^ 2)⁻¹ * (1 / (3 * w.1.val ^ 2) * 0)) +
    w.1.val⁻¹ * ((ζ w.1.val * deriv (deriv φ) w.2) *
      (w.1.val⁻¹ * 1 - w.2 / (3 * w.1.val ^ 3) * 0) +
      (deriv φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 0)) = _
  field_simp [w.1.property.ne']
  ring


/-- A separated angular test, extended by zero to nonpositive position. -/
def bellmanAngularTest (ζ φ : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  if 0 < q.1 then bellmanSeparatedExpression ζ φ q else 0

/-- On positive position, the zero extension agrees locally with the separated expression. -/
theorem bellmanAngularTest_eventuallyEq_positive (ζ φ : ℝ → ℝ)
    (q : ℝ × ℝ) (hq : 0 < q.1) :
    bellmanAngularTest ζ φ =ᶠ[𝓝 q] bellmanSeparatedExpression ζ φ := by
  have ho : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [ho.mem_nhds hq] with z hz
  exact ite_eq_left hz

/-- The separated expression is smooth at every point with positive position. -/
theorem bellmanSeparatedExpression_contDiffAt (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (q : ℝ × ℝ) (hq : 0 < q.1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (bellmanSeparatedExpression ζ φ) q := by
  have hr : ContDiffAt ℝ (⊤ : ℕ∞) bellmanTestRadius q :=
    contDiffAt_fst.rpow_const_of_ne hq.ne'
  have hn : bellmanTestRadius q ≠ 0 :=
    (Real.rpow_pos_of_pos hq _).ne'
  exact (hζ.contDiffAt.comp q hr).mul (hφ.contDiffAt.comp q (contDiffAt_snd.div hr hn))

/-- The separated test extended by zero is smooth, including on the position axis. -/
theorem bellmanAngularTest_contDiff (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (bellmanAngularTest ζ φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 0 < q.1
  · exact ContDiffAt.congr_of_eventuallyEq
      (bellmanSeparatedExpression_contDiffAt ζ φ hζ hφ q hq)
      (bellmanAngularTest_eventuallyEq_positive ζ φ q hq)
  · by_cases hn : q.1 = 0
    · have hz : 0 ∉ tsupport ζ := fun h => (lt_irrefl 0) (hs h)
      have hr : ContinuousAt bellmanTestRadius q :=
        continuousAt_fst.rpow_const (Or.inr (by norm_num : 0 ≤ (3 : ℝ)⁻¹))
      have hr0 : bellmanTestRadius q = 0 := by simp [bellmanTestRadius, hn]
      have hec : ∀ᶠ z in 𝓝 q, ζ (bellmanTestRadius z) = 0 := by
        have ht : Tendsto bellmanTestRadius (𝓝 q) (𝓝 0) := hr0 ▸ hr
        exact ht.eventually (notMem_tsupport_iff_eventuallyEq.mp hz)
      apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
      filter_upwards [hec] with z hz
      simp [bellmanAngularTest, bellmanSeparatedExpression, hz, ite_self]
    · have hneg : q.1 < 0 := lt_of_le_of_ne (le_of_not_gt hq) hn
      have ho : IsOpen {q : ℝ × ℝ | q.1 < 0} := isOpen_lt continuous_fst continuous_const
      apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
      filter_upwards [ho.mem_nhds hneg] with z hz
      exact ite_eq_right (not_lt_of_gt hz)


/-- A compact positive radial support times a compact angular support stays away from the
origin. -/
theorem bellmanAngularTest_support_data (ζ φ : ℝ → ℝ)
    (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (bellmanAngularTest ζ φ) ∧
      tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | 0 < q.1} := by
  let K : Set (BellmanPositiveTime × ℝ) :=
    (Subtype.val ⁻¹' tsupport ζ) ×ˢ tsupport φ
  let P : BellmanPositiveTime × ℝ → ℝ × ℝ := fun w => (bellmanAngularPoint w).val
  have hk : IsCompact K := by
    apply IsCompact.prod _ hcφ
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcζ
    intro s hsζ
    exact ⟨⟨s, hs hsζ⟩, rfl⟩
  have hP : Continuous P := continuous_subtype_val.comp continuous_bellmanAngularPoint
  have hPK : IsCompact (P '' K) := hk.image hP
  have hin : Function.support (bellmanAngularTest ζ φ) ⊆ P '' K := by
    intro q hq
    have hx : 0 < q.1 := by
      by_contra hn
      exact hq (ite_eq_right hn)
    let w := bellmanAngularHomeomorph.symm ⟨q, hx⟩
    have he : P w = q := bellmanAngularPoint_inverse q hx
    have hm : ζ (bellmanTestRadius q) * φ (bellmanTestAngle q) ≠ 0 := by
      change bellmanAngularTest ζ φ q ≠ 0 at hq
      simpa only [bellmanAngularTest, ite_eq_left hx, bellmanSeparatedExpression] using hq
    refine ⟨w, ?_, he⟩
    constructor
    · change w.1.val ∈ tsupport ζ
      have hr : bellmanTestRadius q = w.1.val := by
        rw [← he]
        exact bellmanTestRadius_angularPoint w
      rw [← hr]
      exact subset_tsupport ζ ((mul_ne_zero_iff.mp hm).1)
    · change w.2 ∈ tsupport φ
      have ha : bellmanTestAngle q = w.2 := by
        rw [← he]
        exact bellmanTestAngle_angularPoint w
      rw [← ha]
      exact subset_tsupport φ ((mul_ne_zero_iff.mp hm).2)
  have hts : tsupport (bellmanAngularTest ζ φ) ⊆ P '' K :=
    closure_minimal hin hPK.isClosed
  refine ⟨hPK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans ?_⟩
  rintro q ⟨w, _, rfl⟩
  exact pow_pos w.1.property 3

/-- Compact angular tests with positive radial support satisfy the punctured-test support
rule. -/
theorem bellmanAngularTest_support_punctured (ζ φ : ℝ → ℝ)
    (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} := by
  intro q hq he
  have hx := (bellmanAngularTest_support_data ζ φ hcζ hcφ hs).2 hq
  rw [he] at hx
  change 0 < 0 at hx
  exact lt_irrefl 0 hx


/-- The literal radial integral is the positive Lebesgue integral with s^(3-β). -/
theorem bellmanRadialWeight_integral (β : ℝ) (f : ℝ → ℝ) :
    (∫ s, f s.val ∂bellmanRadialWeight β) =
      ∫ s in Ioi (0 : ℝ), s ^ (3 - β) * f s := by
  have hm : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (3 - β))) := by fun_prop
  rw [bellmanRadialWeight, integral_withDensity_eq_integral_toReal_smul hm]
  · have hw (s : BellmanPositiveTime) :
        (ENNReal.ofReal (s.val ^ (3 - β))).toReal = s.val ^ (3 - β) :=
      ENNReal.toReal_ofReal (Real.rpow_nonneg s.property.le _)
    simp [hw]
    have hem : MeasurableEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Ioi
    have he := hem.integral_map
      (fun s : ℝ => s ^ (3 - β) * f s) (μ := bellmanPositiveTimeVolume)
    rw [map_bellmanPositiveTimeVolume_coe] at he
    exact he.symm
  · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- A test supported in positive position integrates against precisely that restriction. -/
theorem bellman_integral_positive_restrict (μ : Measure BellmanPuncturedPlane)
    (f : ℝ × ℝ → ℝ) (hs : tsupport f ⊆ {q : ℝ × ℝ | 0 < q.1}) :
    (∫ q, f q.val ∂μ.restrict {q | 0 < q.val.1}) = ∫ q, f q.val ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  apply image_eq_zero_of_notMem_tsupport
  exact fun h => hq (hs h)


/-- The zero extension has the exact source transport derivative at every angular point. -/
theorem bellmanAngularTest_transport (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : BellmanPositiveTime × ℝ) :
    (bellmanAngularPoint w).val.2 *
      fderiv ℝ (bellmanAngularTest ζ φ) (bellmanAngularPoint w).val (1, 0) =
      w.2 / (3 * w.1.val) * deriv ζ w.1.val * φ w.2 -
        w.2 ^ 2 / (3 * w.1.val ^ 2) * ζ w.1.val * deriv φ w.2 := by
  rw [(bellmanAngularTest_eventuallyEq_positive ζ φ (bellmanAngularPoint w).val (pow_pos w.1.property 3)).fderiv_eq]
  exact bellmanSeparatedExpression_transport ζ φ w
    (hζ.differentiable (by simp) _) (hφ.differentiable (by simp) _)

/-- The second velocity derivative of the zero extension is exactly ζ(s)φ''(y)/s². -/
theorem bellmanAngularTest_velocity_second (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : BellmanPositiveTime × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ (bellmanAngularTest ζ φ) q (0, 1))
      (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv (deriv φ) w.2 / w.1.val ^ 2 := by
  have hf : (fun q => fderiv ℝ (bellmanAngularTest ζ φ) q (0, 1)) =ᶠ[
      𝓝 (bellmanAngularPoint w).val]
      (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1)) := by
    filter_upwards [(bellmanAngularTest_eventuallyEq_positive ζ φ (bellmanAngularPoint w).val (pow_pos w.1.property 3)).fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hq
  rw [hf.fderiv_eq]
  exact bellmanSeparatedExpression_velocity_second ζ φ hζ hφ w


/-- A compact positive-radius test has compact support on the positive radial subtype. -/
theorem bellmanRadialTest_compact (ψ : ℝ → ℝ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (fun s : BellmanPositiveTime => ψ s.val) := by
  have hk : IsCompact ((Subtype.val : BellmanPositiveTime → ℝ) ⁻¹' tsupport ψ) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hc
    intro s hsψ
    exact ⟨⟨s, hs hsψ⟩, rfl⟩
  exact hk.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset_preimage ψ continuous_subtype_val)

/-- Dividing a positive-radius compact test by a power of s is integrable for every degree. -/
theorem bellmanRadialTest_integrable (β : ℝ) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) (n : ℕ) :
    Integrable (fun s : BellmanPositiveTime => ψ s.val / s.val ^ n)
      (bellmanRadialWeight β) := by
  have hcont : Continuous (fun s : BellmanPositiveTime => ψ s.val / s.val ^ n) :=
    (hψ.comp continuous_subtype_val).div (continuous_subtype_val.pow n)
      (fun s => pow_ne_zero n s.property.ne')
  apply hcont.integrable_of_hasCompactSupport
  convert! (bellmanRadialTest_compact ψ hc hs).mul_right
    (f' := fun s : BellmanPositiveTime => (s.val ^ n)⁻¹) using 1



/-- The transport integral factors into the two exact radial and angular terms. -/
theorem bellmanAngularRep_transport_integral (β : ℝ) (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    (∫ q, q.val.2 * fderiv ℝ (bellmanAngularTest ζ φ) q.val (1, 0)
      ∂bellmanAngularRep β F) =
      (1 / 3 : ℝ) * (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) *
        (∫ y, y * φ y ∂F) -
      (1 / 3 : ℝ) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
        (∫ y, y ^ 2 * deriv φ y ∂F)  := by
  have bellmanAngularTestFactor_integrable [IsFiniteMeasureOnCompacts F] (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (n : ℕ) :
      Integrable (fun y => y ^ n * ψ y) F := by
    exact ((continuous_id.pow n).mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have hζd := (contDiff_infty_iff_deriv.mp hζ).2
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hr1 : Integrable (fun s : BellmanPositiveTime => deriv ζ s.val / s.val)
      (bellmanRadialWeight β) := by
    simpa using bellmanRadialTest_integrable β (deriv ζ)
      hζd.continuous hcζ.deriv (tsupport_deriv_subset.trans hs) 1
  have ha1 : Integrable (fun y => y * φ y) F := by
    simpa using bellmanAngularTestFactor_integrable φ
      hφ.continuous hcφ 1
  rw [bellmanAngularRep,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.integral_map]
  have hfun : (fun w : BellmanPositiveTime × ℝ => (bellmanAngularPoint w).val.2 *
      fderiv ℝ (bellmanAngularTest ζ φ) (bellmanAngularPoint w).val (1, 0)) =
      (fun w : BellmanPositiveTime × ℝ =>
        (1 / 3 : ℝ) * (deriv ζ w.1.val / w.1.val * (w.2 * φ w.2)) -
        (1 / 3 : ℝ) * (ζ w.1.val / w.1.val ^ 2 * (w.2 ^ 2 * deriv φ w.2))) := by
    funext w
    rw [bellmanAngularTest_transport ζ φ hζ hφ w]
    ring
  rw [hfun, integral_sub ((hr1.mul_prod ha1).const_mul (1 / 3 : ℝ))
    (((bellmanRadialTest_integrable β ζ hζ.continuous hcζ hs 2).mul_prod (bellmanAngularTestFactor_integrable (deriv φ) hφd.continuous hcφ.deriv 2)).const_mul (1 / 3 : ℝ)), integral_const_mul, integral_const_mul,
    integral_prod_mul (fun s : BellmanPositiveTime => deriv ζ s.val / s.val)
      (fun y : ℝ => y * φ y),
    integral_prod_mul (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2)
      (fun y : ℝ => y ^ 2 * deriv φ y)]
  ring

/-- The second velocity integral factors with the same radial multiplier as the angular
equation. -/
theorem bellmanAngularRep_velocity_integral (β : ℝ) (H : Measure ℝ) [SFinite H]
    (ζ φ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ q, fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
      q.val (0, 1) ∂bellmanAngularRep β H) =
      (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
        (∫ y, deriv (deriv φ) y ∂H) := by
  rw [bellmanAngularRep,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.integral_map]
  have hfun : (fun w : BellmanPositiveTime × ℝ =>
      fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
        (bellmanAngularPoint w).val (0, 1)) =
      (fun w : BellmanPositiveTime × ℝ =>
        (ζ w.1.val / w.1.val ^ 2) * deriv (deriv φ) w.2) := by
    funext w
    rw [bellmanAngularTest_velocity_second ζ φ hζ hφ w]
    ring
  rw [hfun]
  exact integral_prod_mul (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2)
    (deriv (deriv φ))


/-- Radial integration by parts produces the source coefficient β-2. -/
theorem bellmanAngularRadial_integrationByParts (β a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hza : ζ a = 0) (hzb : ζ b = 0) :
    (∫ s in a..b, s ^ (2 - β) * deriv ζ s) =
      (β - 2) * (∫ s in a..b, s ^ (1 - β) * ζ s) := by
  have hp : ∀ s ∈ uIcc a b, 0 < s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ha.trans_le hs.1
  have hw : ContDiffOn ℝ 1 (fun s : ℝ => s ^ (2 - β)) (uIcc a b) :=
    contDiffOn_id.rpow_const_of_ne fun s hs => (hp s hs).ne'
  have hz : AbsolutelyContinuousOnInterval ζ a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (hζ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn
  have he := hw.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hz
  rw [hza, hzb, mul_zero, mul_zero, sub_self, zero_sub] at he
  have hd : (∫ s in a..b, deriv (fun z : ℝ => z ^ (2 - β)) s * ζ s) =
      (2 - β) * (∫ s in a..b, s ^ (1 - β) * ζ s) := by
    calc
      _ = ∫ s in a..b, (2 - β) * (s ^ (1 - β) * ζ s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change deriv (fun z : ℝ => z ^ (2 - β)) s * ζ s =
          (2 - β) * (s ^ (1 - β) * ζ s)
        rw [(Real.hasDerivAt_rpow_const (p := 2 - β) (Or.inl (hp s hs).ne')).deriv]
        have hex : (2 - β) - 1 = 1 - β := by ring
        rw [hex]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hd] at he
  linear_combination he


/-- Dividing a radial test by s^n reduces the literal radial exponent by n. -/
theorem bellmanRadialWeight_integral_div (β : ℝ) (ψ : ℝ → ℝ) (n : ℕ) :
    (∫ s, ψ s.val / s.val ^ n ∂bellmanRadialWeight β) =
      ∫ s in Ioi (0 : ℝ), s ^ ((3 - β) - n) * ψ s := by
  rw [bellmanRadialWeight_integral β (fun s : ℝ => ψ s / s ^ n)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  change s ^ (3 - β) * (ψ s / s ^ n) = s ^ ((3 - β) - n) * ψ s
  rw [Real.rpow_sub hs (3 - β) (n : ℝ), Real.rpow_natCast]
  ring

/-- A positive-position supported integrand has the same positive and full real integral. -/
theorem bellman_positiveIntegral_eq_full {ψ : ℝ → ℝ}
    (hs : Function.support ψ ⊆ Ioi (0 : ℝ)) :
    (∫ s in Ioi (0 : ℝ), ψ s) = ∫ s, ψ s := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hn
  by_contra h
  exact hn (hs h)

/-- The two radial factors satisfy the exact relation required by the angular equation. -/
theorem bellmanRadialWeight_deriv_relation (β a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hs : tsupport ζ ⊆ Ioo a b) :
    (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) =
      (β - 2) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
  have hd : tsupport (deriv ζ) ⊆ Ioo a b := tsupport_deriv_subset.trans hs
  have hs1 : Function.support (fun s : ℝ => s ^ (2 - β) * deriv ζ s) ⊆ Ioc a b := by
    intro s h
    have hz : deriv ζ s ≠ 0 := (mul_ne_zero_iff.mp h).2
    exact ⟨(hd (subset_tsupport _ hz)).1, (hd (subset_tsupport _ hz)).2.le⟩
  have hs2 : Function.support (fun s : ℝ => s ^ (1 - β) * ζ s) ⊆ Ioc a b := by
    intro s h
    have hz : ζ s ≠ 0 := (mul_ne_zero_iff.mp h).2
    exact ⟨(hs (subset_tsupport _ hz)).1, (hs (subset_tsupport _ hz)).2.le⟩
  have hp1 : Function.support (fun s : ℝ => s ^ (2 - β) * deriv ζ s) ⊆ Ioi 0 :=
    fun s h => ha.trans (hs1 h).1
  have hp2 : Function.support (fun s : ℝ => s ^ (1 - β) * ζ s) ⊆ Ioi 0 :=
    fun s h => ha.trans (hs2 h).1
  have h1 := bellmanRadialWeight_integral_div β (deriv ζ) 1
  simp [Nat.cast_one] at h1
  rw [h1, bellmanRadialWeight_integral_div β ζ 2]
  norm_num only [Nat.cast_ofNat]
  have he1 : (3 - β) - 1 = 2 - β := by ring
  have he2 : (3 - β) - 2 = 1 - β := by ring
  rw [he1, he2, bellman_positiveIntegral_eq_full hp1,
    bellman_positiveIntegral_eq_full hp2,
    ← intervalIntegral.integral_eq_integral_of_support_subset hs1,
    ← intervalIntegral.integral_eq_integral_of_support_subset hs2]
  have hza : ζ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl a) (hs h).1)
  have hzb : ζ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl b) (hs h).2)
  exact bellmanAngularRadial_integrationByParts β a b ha hab ζ hζ hza hzb


/-- An explicit smooth radial test makes the common angular multiplier strictly positive. -/
theorem exists_bellmanAngularRadialTest (β : ℝ) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Ioo (1 : ℝ) 3 ∧
      0 < (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) ∧
      (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) =
        (β - 2) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
  let ζ : ContDiffBump (2 : ℝ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hs : tsupport (ζ : ℝ → ℝ) ⊆ Ioo 1 3 := by
    rw [ζ.tsupport_eq]
    intro s hs
    rw [Metric.mem_closedBall, Real.dist_eq] at hs
    change |s - 2| ≤ 1 / 2 at hs
    constructor <;> linarith [abs_le.mp hs]
  have hsp : tsupport (ζ : ℝ → ℝ) ⊆ Ioi 0 :=
    fun s hsζ => lt_trans (by norm_num : (0 : ℝ) < 1) (hs hsζ).1
  have hc : HasCompactSupport (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2) := by
    convert! (bellmanRadialTest_compact ζ ζ.hasCompactSupport hsp).mul_right
      (f' := fun s : BellmanPositiveTime => (s.val ^ 2)⁻¹) using 1
  have hcont : Continuous (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2) :=
    (ζ.continuous.comp continuous_subtype_val).div (continuous_subtype_val.pow 2)
      (fun s => pow_ne_zero 2 s.property.ne')
  have hn : ∀ s : BellmanPositiveTime, 0 ≤ ζ s.val / s.val ^ 2 :=
    fun s => div_nonneg ζ.nonneg (sq_nonneg _)
  have hself : ζ (2 : ℝ) = 1 := ζ.one_of_mem_closedBall (Metric.mem_closedBall_self
    (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hp : 0 < (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
    apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hc hn
      (x := ⟨2, by norm_num⟩)
    change ζ (2 : ℝ) / 2 ^ 2 ≠ 0
    rw [hself]
    norm_num
  exact ⟨ζ, ζ.contDiff, ζ.hasCompactSupport, hs, hp,
    bellmanRadialWeight_deriv_relation β 1 3 (by norm_num) (by norm_num) ζ ζ.contDiff hs⟩


/-- The actual homogeneous stationary pair has angular measures satisfying the source
equation. -/
theorem exists_angular_adjoint (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ F H : Measure ℝ,
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      IsBellmanAngularAdjointPair 1 R β F H := by
  obtain ⟨F, H, hrep, hF, hFi, hH, hHi, hlo, hhi⟩ :=
    angular_disintegration R β hR hβ μ η hp
  let : IsFiniteMeasureOnCompacts F := hF
  let : IsFiniteMeasureOnCompacts H := hH
  refine ⟨F, H, hrep, hF, hFi, hH, hHi, ?_, hhi, ?_⟩
  · simpa using hlo
  intro φ hφ hcφ
  obtain ⟨ζ, hζ, hcζ, hsζ, hK, hrel⟩ := exists_bellmanAngularRadialTest β
  have hsζp : tsupport ζ ⊆ Ioi (0 : ℝ) :=
    fun s hs => lt_trans (by norm_num : (0 : ℝ) < 1) (hsζ hs).1
  have he := hp.2.2.2.2.2.1 (bellmanAngularTest ζ φ) (bellmanAngularTest_contDiff ζ φ hζ hφ hsζp) ((bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).1) (bellmanAngularTest_support_punctured ζ φ hcζ hcφ hsζp)
  let fx : ℝ × ℝ → ℝ :=
    fun q => q.2 * fderiv ℝ (bellmanAngularTest ζ φ) q (1, 0)
  let fv : ℝ × ℝ → ℝ :=
    fun q => fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1)) q (0, 1)
  have hts := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).2
  have hsx : tsupport fx ⊆ {q : ℝ × ℝ | 0 < q.1} :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hts)
  have hsv : tsupport fv ⊆ {q : ℝ × ℝ | 0 < q.1} :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hts)
  change (∫ q, fx q.val ∂μ) + (∫ q, fv q.val ∂η) = 0 at he
  rw [← bellman_integral_positive_restrict μ fx hsx,
    ← bellman_integral_positive_restrict η fv hsv, hrep.1, hrep.2] at he
  change (∫ q, q.val.2 * fderiv ℝ (bellmanAngularTest ζ φ) q.val (1, 0)
    ∂bellmanAngularRep β F) +
    (∫ q, fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
      q.val (0, 1) ∂bellmanAngularRep β H) = 0 at he
  rw [bellmanAngularRep_transport_integral β F ζ φ hζ hφ hcζ hcφ hsζp,
    bellmanAngularRep_velocity_integral β H ζ φ hζ hφ, hrel] at he
  have hzero : (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
      ((∫ y, deriv (deriv φ) y ∂H) - (1 / 3 : ℝ) * (∫ y, y ^ 2 * deriv φ y ∂F) +
        ((β - 2) / 3) * (∫ y, y * φ y ∂F)) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hzero).resolve_left hK.ne'


/-- The degree-dependent radial measure transforms with exponent beta minus four. -/
theorem bellmanRadialWeight_map_scale (β r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanRadialScale r hr) (bellmanRadialWeight β) =
      ENNReal.ofReal (r ^ (β - 4)) • bellmanRadialWeight β := by
  rw [bellmanRadialWeight, bellman_map_withDensity _ _ _ (by fun_prop),
    map_bellmanPositiveTimeVolume_radialScale, withDensity_smul_measure]
  have he : (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (((bellmanRadialScale r hr).symm s).val ^ (3 - β))) =
      ENNReal.ofReal (r ^ (β - 3)) •
        (fun s : BellmanPositiveTime => ENNReal.ofReal (s.val ^ (3 - β))) := by
    funext s
    change ENNReal.ofReal ((r⁻¹ * s.val) ^ (3 - β)) = _
    rw [Real.mul_rpow (inv_nonneg.mpr hr.le) s.property.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)]
    have hp : (r⁻¹) ^ (3 - β) = r ^ (β - 3) := by
      rw [← Real.rpow_neg_eq_inv_rpow]
      congr 1
      ring
    rw [hp]
    rfl
  rw [he, withDensity_smul _ (by fun_prop), smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  have hp : r⁻¹ * r ^ (β - 3) = r ^ (β - 4) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  rw [hp]

/-- A radial strip at velocity y has exactly the source tail weight times a fixed positive
mass. -/
theorem bellmanRadialWeight_velocity_strip (β y : ℝ) (hy : 0 < y) :
    bellmanRadialWeight β {s | 1 ≤ y * s.val ∧ y * s.val ≤ 2} =
      ENNReal.ofReal (y ^ (β - 4)) *
        bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2} := by
  have hm : MeasurableSet {s : BellmanPositiveTime | 1 ≤ s.val ∧ s.val ≤ 2} := by
    measurability
  have he := congrArg (fun μ : Measure BellmanPositiveTime =>
      μ {s | 1 ≤ s.val ∧ s.val ≤ 2}) (bellmanRadialWeight_map_scale β y hy)
  rw [Measure.map_apply (bellmanRadialScale y hy).measurable hm,
    Measure.smul_apply, smul_eq_mul] at he
  exact he


/-- The source rectangle combines both velocity signs while avoiding zero velocity. -/
def bellmanAngularTailRectangle : Set BellmanPuncturedPlane :=
  {q | 0 ≤ q.val.1 ∧ q.val.1 ≤ 1 ∧ 1 ≤ |q.val.2| ∧ |q.val.2| ≤ 2}

/-- The velocity annulus on the real line is compact. -/
theorem bellman_velocity_annulus_compact : IsCompact {v : ℝ | 1 ≤ |v| ∧ |v| ≤ 2} := by
  apply isCompact_Icc.of_isClosed_subset
    ((isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const))
  intro v hv
  exact abs_le.mp hv.2

/-- The rectangle stays compact on the punctured plane because its velocities avoid zero. -/
theorem bellmanAngularTailRectangle_isCompact : IsCompact bellmanAngularTailRectangle := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ {v : ℝ | 1 ≤ |v| ∧ |v| ≤ 2}) :=
    isCompact_Icc.prod bellman_velocity_annulus_compact
  have he : bellmanAngularTailRectangle =
      (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) ⁻¹'
        (Icc (0 : ℝ) 1 ×ˢ {v : ℝ | 1 ≤ |v| ∧ |v| ≤ 2}) := by
    ext q
    simp [bellmanAngularTailRectangle, and_assoc]
  rw [he]
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' hK
  intro q hq
  refine ⟨⟨q, ?_⟩, rfl⟩
  intro hz
  have hv := hq.2.1
  rw [hz] at hv
  norm_num at hv

/-- In radial coordinates the source rectangle contains the full velocity strips at large
angle. -/
theorem bellmanAngularTail_strip_subset :
    {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
      1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} ⊆
      bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle := by
  intro w hw
  change 2 < |w.2| ∧ 1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2 at hw
  change 0 ≤ w.1.val ^ 3 ∧ w.1.val ^ 3 ≤ 1 ∧
    1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2
  have hs : w.1.val ≤ 1 := by
    have hv := hw.2.2
    rw [abs_mul, abs_of_pos w.1.property] at hv
    nlinarith [w.1.property, hw.1]
  exact ⟨pow_nonneg w.1.property.le 3,
    (pow_le_pow_left₀ w.1.property.le hs 3).trans_eq (one_pow 3), hw.2.1, hw.2.2⟩

/-- Local finiteness on the original plane bounds both angular velocity strips. -/
theorem bellmanAngularTail_strip_finite (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F) :
    (bellmanRadialWeight β).prod F
      {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} < ⊤ := by
  have he : (bellmanRadialWeight β).prod F
      (bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle) =
      μ.restrict {q | 0 < q.val.1} bellmanAngularTailRectangle := by
    rw [hrep, bellmanAngularRep, Measure.map_apply continuous_bellmanAngularPoint.measurable bellmanAngularTailRectangle_isCompact.measurableSet]
  calc
    _ ≤ (bellmanRadialWeight β).prod F
        (bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle) :=
      measure_mono bellmanAngularTail_strip_subset
    _ = _ := he
    _ ≤ μ bellmanAngularTailRectangle := Measure.restrict_le_self _
    _ < ⊤ := bellmanAngularTailRectangle_isCompact.measure_lt_top


/-- The radial reference strip has positive mass for every density degree. -/
theorem bellmanRadialWeight_reference_ne_zero (β : ℝ) :
    bellmanRadialWeight β {s : BellmanPositiveTime | 1 ≤ s.val ∧ s.val ≤ 2} ≠ 0 := by
  have ho : IsOpen {s : BellmanPositiveTime | 1 < s.val ∧ s.val < 2} := by
    exact (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  have hn : ({s : BellmanPositiveTime | 1 < s.val ∧ s.val < 2} : Set _).Nonempty := by
    refine ⟨⟨3 / 2, by norm_num⟩, ?_⟩
    norm_num
  apply ne_of_gt
  exact (ho.measure_pos (bellmanRadialWeight β) hn).trans_le (measure_mono (fun s hs => ⟨hs.1.le, hs.2.le⟩))

/-- Integrating the two-sided velocity strips gives the literal angular tail factor. -/
theorem bellmanAngularTail_strip_mass (β : ℝ) (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] :
    (bellmanRadialWeight β).prod F
      {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} =
      bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2} *
        (∫⁻ y in {y : ℝ | 2 < |y|}, ENNReal.ofReal (|y| ^ (β - 4)) ∂F) := by
  have hm : MeasurableSet {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
      1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} := by measurability
  rw [Measure.prod_apply_symm hm]
  have hf : (fun y => bellmanRadialWeight β
      ((fun s => (s, y)) ⁻¹' {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2})) =
      {y : ℝ | 2 < |y|}.indicator (fun y =>
        ENNReal.ofReal (|y| ^ (β - 4)) *
          bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2}) := by
    funext y
    by_cases hy : 2 < |y|
    · rw [indicator_of_mem (show y ∈ {y : ℝ | 2 < |y|} from hy)]
      have he : ((fun s => (s, y)) ⁻¹'
          {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
            1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2}) =
          {s : BellmanPositiveTime | 1 ≤ |y| * s.val ∧ |y| * s.val ≤ 2} := by
        ext s
        simp [hy, abs_mul, abs_of_pos s.property, mul_comm s.val |y|]
      rw [he]
      exact bellmanRadialWeight_velocity_strip β |y| (by linarith)
    · rw [indicator_of_notMem (show y ∉ {y : ℝ | 2 < |y|} from hy)]
      have he : ((fun s => (s, y)) ⁻¹'
          {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
            1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2}) = ∅ := by
        ext s
        simp [hy, mem_empty_iff_false]
      rw [he, measure_empty]
  rw [hf, lintegral_indicator (by measurability), lintegral_mul_const _ (by fun_prop)]
  exact mul_comm _ _

/-- Local finiteness of the original measure implies finite weighted angular tail mass. -/
theorem bellmanAngularTail_lintegral_finite (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F) :
    (∫⁻ y in {y : ℝ | 2 < |y|}, ENNReal.ofReal (|y| ^ (β - 4)) ∂F) < ⊤ := by
  have hm := bellmanAngularTail_strip_finite β μ F hrep
  rw [bellmanAngularTail_strip_mass] at hm
  exact ENNReal.lt_top_of_mul_ne_top_right hm.ne (bellmanRadialWeight_reference_ne_zero β)


/-- The finite weighted angular mass is the source tail integrability for its actual density. -/
theorem bellmanAngularDensity_tail (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F)
    (f : ℝ → ℝ) (hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : LocallyIntegrable f volume) (hn : ∀ᵐ x ∂volume, 0 ≤ f x) :
    IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  let S : Set ℝ := {y | 2 < |y|}
  have hS : MeasurableSet S := by measurability
  have hm : Measurable (fun y : ℝ => |y| ^ (β - 4)) := by fun_prop
  have hi : IntegrableOn (fun y : ℝ => |y| ^ (β - 4)) S F := by
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ fun y => Real.rpow_nonneg (abs_nonneg y) _)).mp
    exact (bellmanAngularTail_lintegral_finite β μ F hrep).ne
  rw [hF, IntegrableOn, restrict_withDensity hS] at hi
  have ht := (integrable_withDensity_iff_integrable_smul₀' hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).mp hi
  apply ht.congr
  filter_upwards [ae_restrict_of_ae hn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]


/-- A genuine homogeneous pair produces compatible angular measures, densities and finite
tails. -/
theorem exists_angular_densities_tail (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ (F H : Measure ℝ) (f h J : ℝ → ℝ),
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      (
      F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
      LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
      (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
      (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
      (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y)) ∧
      IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  obtain ⟨F, H, hrep, hang⟩ := exists_angular_adjoint R β hR hβ μ η hp
  obtain ⟨f, h, J, hd⟩ := angular_has_densities R β hR F H hang
  let : IsFiniteMeasureOnCompacts μ := hp.1.1
  let : IsFiniteMeasureOnCompacts F := hang.1
  exact ⟨F, H, f, h, J, hrep, hd,
    bellmanAngularDensity_tail β μ F hrep.1 f hd.1 hd.2.2.1 hd.2.2.2.1⟩

end HypoellipticAleksandrov.KineticAleksandrov

