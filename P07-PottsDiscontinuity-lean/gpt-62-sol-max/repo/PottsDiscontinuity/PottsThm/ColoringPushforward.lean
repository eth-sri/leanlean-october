module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.PottsThm.ColoringCylinderLaw

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open PottsDiscontinuity.Duality
open scoped ENNReal

noncomputable section

abbrev iidPotts (q : ℕ) : Measure (Vertex → Set.Icc 1 q) :=
  iidFieldMeasure (ProbabilityTheory.uniformOn Set.univ)

private theorem iidPotts_isProbability {q : ℕ} (c₀ : Set.Icc 1 q) :
    IsProbabilityMeasure (iidPotts q) := by
  let : Nonempty (Set.Icc 1 q) := ⟨c₀⟩
  unfold iidPotts iidFieldMeasure
  infer_instance

noncomputable def coloringMeasure {q : ℕ} (φ : ProbabilityMeasure LatticeConfiguration)
    (c₀ : Set.Icc 1 q) : Measure (SpinSpace q) := (φ.toMeasure.prod (iidPotts q)).map (clusterColoring c₀)

instance coloringMeasure_probability {q : ℕ} (φ : ProbabilityMeasure LatticeConfiguration)
    (c₀ : Set.Icc 1 q) : IsProbabilityMeasure (coloringMeasure φ c₀) := by
  have := iidPotts_isProbability c₀
  have := φ.property
  unfold coloringMeasure
  infer_instance

noncomputable def coloringProbability {q : ℕ} (φ : ProbabilityMeasure LatticeConfiguration)
    (c₀ : Set.Icc 1 q) : ProbabilityMeasure (SpinSpace q) := ⟨coloringMeasure φ c₀, inferInstance⟩

section

variable {q : ℕ} (φ : ProbabilityMeasure LatticeConfiguration) (c₀ : Set.Icc 1 q)

private theorem coloring_cylinder (A : Finset Vertex) (ξ : SpinSpace q) {ι : Type*} [Finite ι]
    (r : LatticeConfiguration → Setoid ι) (K : Setoid ι → ℝ) (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R})
    (hfiber : ∀ᵐ ω ∂φ.toMeasure, iidPotts q {u | ∀ a : ↥A, clusterColoring c₀ (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (K (r ω))) :
    ((φ.toMeasure.prod (iidPotts q)).map (clusterColoring c₀)).real (spinCylinder q A ξ) =
      partitionExpectation φ.toMeasure r K := by
  have := iidPotts_isProbability c₀
  have := φ.property
  let F := clusterColoring c₀
  let E := {z | ∀ a : ↥A, F z a.val = ξ a.val}
  have heq : F ⁻¹' spinCylinder q A ξ = E := by ext z; simp [E, spinCylinder]
  have hF := measurable_clusterColoring c₀
  have hC := (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  change ∀ᵐ ω ∂φ.toMeasure, iidPotts q (Prod.mk ω ⁻¹' E) = ENNReal.ofReal (K (r ω)) at hfiber
  rw [Measure.real_def, Measure.map_apply hF hC, heq, Measure.prod_apply (heq ▸ hF hC),
    lintegral_congr_ae hfiber, toReal_lintegral_finitePartitionKernel φ.toMeasure r K hK hr]

end

/-- The canonical free cluster coloring has the Edwards--Sokal cylinder law
whenever the bond measure almost surely has only finite clusters. -/
theorem freeColoringMap_isFreeESC {q : ℕ}
    (φ : ProbabilityMeasure LatticeConfiguration) (c₀ : Set.Icc 1 q)
    (hno : φ.toMeasure Duality.existsInfiniteCluster = 0) :
    IsFreeEdwardsSokalColouring q φ.toMeasure (coloringMeasure φ c₀) := by
  classical
  have hq : 0 < q := Nat.zero_lt_one.trans_le (c₀.property.1.trans c₀.property.2)
  refine ⟨inferInstance, fun A ξ => ?_⟩
  unfold freeESCylinder
  refine coloring_cylinder φ c₀ A ξ (infiniteFreePartition (fun a : ↥A => a.val)) _
    (fun R => ?_) (infiniteFreePartition_measurableSet _) ?_
  · unfold clusterCylinderProbability
    split <;> positivity
  · have hfinite : ∀ᵐ ω ∂φ.toMeasure, ∀ x, (RCInfinite.cluster ω x).Finite :=
      ae_iff.mpr (by simpa [Duality.existsInfiniteCluster, RCInfinite.cluster, Duality.cluster] using hno)
    filter_upwards [hfinite] with ω hω
    exact freeClusterColoring_fiber_cylinder_uniform q hq ω A ξ c₀ hω

/-- The canonical wired cluster coloring has the wired Edwards--Sokal cylinder
law for every bond measure. Infinite clusters are assigned the fixed boundary
color. -/
theorem wiredColoringMap_isWiredESC {q : ℕ}
    (φ : ProbabilityMeasure LatticeConfiguration) (i : Fin (q + 1))
    (hi : 1 ≤ (i : ℕ)) :
    IsWiredEdwardsSokalColouring q φ.toMeasure i hi (coloringMeasure φ (boundaryColor q i hi)) := by
  classical
  refine ⟨inferInstance, fun A ξ => ?_⟩
  unfold wiredESCylinder
  refine coloring_cylinder φ (boundaryColor q i hi) A ξ
    (infiniteWiredPartition (Option.map (fun a : ↥A => a.val))) _
    (fun R => ?_) (infiniteWiredPartition_measurableSet _) ?_
  · unfold pinnedClusterCylinderProbability
    split <;> positivity
  · exact Filter.Eventually.of_forall fun ω =>
      wiredClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ i hi

/-- A single-site law is uniform on finite clusters and the pin on infinite ones. -/
theorem coloringMeasure_site {q : ℕ} (φ : ProbabilityMeasure LatticeConfiguration)
    (pin c : Set.Icc 1 q) (x : Vertex) :
    (coloringMeasure φ pin).real {σ | σ x = c} =
      1 / (q : ℝ) + ((if pin = c then 1 else 0) - 1 / (q : ℝ)) * φ.toMeasure.real (infiniteAt x) := by
  classical
  let E : Set (SpinSpace q) := {σ | σ x = c}
  let A := infiniteAt x
  let p : ℝ≥0∞ := if pin = c then 1 else 0
  let F := clusterColoring pin
  have hF := measurable_clusterColoring pin
  have hE : MeasurableSet E := (measurable_pi_apply (X := fun _ : Vertex => Set.Icc 1 q) x)
    (measurableSet_singleton c)
  have hA : MeasurableSet A := measurableSet_infiniteAt x
  have := iidPotts_isProbability pin
  have := φ.property
  let : Nonempty (Set.Icc 1 q) := ⟨pin⟩
  have hf (ω : LatticeConfiguration) : iidPotts q (Prod.mk ω ⁻¹' (F ⁻¹' E)) =
      A.piecewise (fun _ => p) (fun _ => (q : ℝ≥0∞)⁻¹) ω := by
    cases h : clusterRepresentative ω x with
    | none =>
      have hw : ω ∈ A := (clusterRepresentative_none_iff ω x).mp h
      rw [Set.piecewise_eq_of_mem _ _ _ hw]
      have he : Prod.mk ω ⁻¹' (F ⁻¹' E) = {u | pin = c} := by
        ext u; simp [F, E, clusterColoring, h]
      by_cases hc : pin = c <;> simp [he, p, hc]
    | some y =>
      have hw : ω ∉ A := fun hh => by
        have := (clusterRepresentative_none_iff ω x).mpr hh
        simp_all
      have he : Prod.mk ω ⁻¹' (F ⁻¹' E) = (fun u : SpinSpace q => u y) ⁻¹' {c} := by
        ext u; simp [F, E, clusterColoring, h]
      rw [he, ← Measure.map_apply (measurable_pi_apply y) (measurableSet_singleton c),
        iidPotts, iidFieldMeasure, Measure.infinitePi_map_eval, pottsUniformColor_singleton,
        Set.piecewise_eq_of_notMem _ _ _ hw]
  change ((φ.toMeasure.prod (iidPotts q)).map F).real E = _
  rw [Measure.real_def, Measure.map_apply hF hE, Measure.prod_apply (hF hE)]
  rw [lintegral_congr hf]
  rw [lintegral_piecewise hA, lintegral_const, lintegral_const,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ]
  have hp : p ≠ ∞ := by dsimp [p]; split <;> simp
  have hq : q ≠ 0 := (Nat.zero_lt_one.trans_le (pin.property.1.trans pin.property.2)).ne'
  have hq' : (q : ℝ≥0∞)⁻¹ ≠ ∞ := by simp [hq]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp (measure_ne_top _ _))
    (ENNReal.mul_ne_top hq' (measure_ne_top _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  change p.toReal * φ.toMeasure.real A + (q : ℝ)⁻¹ * φ.toMeasure.real Aᶜ = _
  rw [measureReal_compl hA]
  by_cases hc : pin = c <;> simp [p, hc, A] <;> ring


end
end PottsDiscontinuity.PottsThm
