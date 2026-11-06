module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.MaximalSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Selection
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Weak maximal estimate for the kinetic cylinder basis

The estimate is proved by disjoint selection, homogeneous inflation volume, and measure
charging. In particular, no metric-ball density theorem is used for the eccentric basis.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/- The union of radius-at-most-one cylinders where E occupies at least the threshold.
The threshold is in ENNReal so the measure calculation stays exact before finite conversions. -/
def maximalCylinderUnion {d : ℕ} (E : Set (KineticPoint d)) (tau : ENNReal) :
    Set (KineticPoint d) :=
  ⋃ z ∈ {z : KineticPoint d × ℝ | 0 < z.2 ∧ z.2 ≤ 1 ∧
    tau * volume (backwardCylinder z.1 z.2) ≤ volume (E ∩ backwardCylinder z.1 z.2)},
    backwardCylinder z.1 z.2

/- A density-threshold cylinder family satisfies the homogeneous weak measure estimate. -/
theorem cylinder_family_weak_type {d : ℕ} {ι : Type*}
    (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (E : Set (KineticPoint d)) (tau : ENNReal)
    (hdensity : ∀ i ∈ t, tau * volume (backwardCylinder (P i) (r i)) ≤
      volume (E ∩ backwardCylinder (P i) (r i))) :
    tau * volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
      ENNReal.ofReal ((8 : ℝ) ^ (4*d+2)) * volume E := by
  obtain ⟨u, hut, _, _, hcover, hcharge⟩ : ∃ u ⊆ t, u.Countable ∧
      u.PairwiseDisjoint (fun i => backwardCylinder (P i) (r i)) ∧
      volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
        ∑' i : u, volume (inflatedCylinder (P i) (r i) 8) ∧
      (∑' i : u, volume (E ∩ backwardCylinder (P i) (r i))) ≤ volume E := by
    obtain ⟨u, hut, hcount, hdisj, hcover⟩ : ∃ u ⊆ t, u.Countable ∧
        u.PairwiseDisjoint (fun i => backwardCylinder (P i) (r i)) ∧
        (⋃ i ∈ t, backwardCylinder (P i) (r i)) ⊆
          ⋃ i ∈ u, inflatedCylinder (P i) (r i) 8 := by
      let : SecondCountableTopology (KineticPoint d) :=
        (KineticPoint.homeomorphProd d).secondCountableTopology
      obtain ⟨u, hut, hdisj, hcover⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement
          (fun i => backwardCylinder (P i) (r i)) t r 2 (by norm_num)
          (fun i hi => (hr i hi).le) R hR (fun i hi => cylinder_nonempty (P i) (hr i hi))
      have hcount : u.Countable := hdisj.countable_of_nonempty_interior fun i hi => by
        rw [(isOpen_cylinder (P i) (r i)).interior_eq]
        exact cylinder_nonempty (P i) (hr i (hut hi))
      refine ⟨u, hut, hcount, hdisj, ?_⟩
      intro X hX
      obtain ⟨i, hi, hXi⟩ := mem_iUnion₂.mp hX
      obtain ⟨j, hj, hij, hrj⟩ := hcover i hi
      exact mem_iUnion₂.mpr ⟨j, hj,
        cylinder_subset_inflation_of_inter (hr i hi) (hr j (hut hj)) hrj hij hXi⟩
    refine ⟨u, hut, hcount, hdisj, ?_, ?_⟩
    · exact (measure_mono hcover).trans
        (measure_biUnion_le volume hcount (fun i => inflatedCylinder (P i) (r i) 8))
    · calc
        (∑' i : u, volume (E ∩ backwardCylinder (P i) (r i))) =
            ∑' i : u, (volume.restrict E) (backwardCylinder (P i) (r i)) := by
          apply tsum_congr
          intro i
          rw [Measure.restrict_apply (isOpen_cylinder (P i) (r i)).measurableSet,
            inter_comm]
        _ = (volume.restrict E) (⋃ i ∈ u, backwardCylinder (P i) (r i)) :=
          (measure_biUnion hcount hdisj
            (fun i _ => (isOpen_cylinder (P i) (r i)).measurableSet)).symm
        _ ≤ (volume.restrict E) univ := measure_mono (subset_univ _)
        _ = volume E := Measure.restrict_apply_univ E
  let C := ENNReal.ofReal ((8 : ℝ) ^ (4*d+2))
  calc
    tau * volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
        tau * ∑' i : u, volume (inflatedCylinder (P i) (r i) 8) :=
      mul_le_mul_right hcover tau
    _ = C * ∑' i : u, tau * volume (backwardCylinder (P i) (r i)) := by
      simp_rw [volume_inflatedCylinder (P _) (hr _ (hut (Subtype.prop _)))]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      exact mul_left_comm _ _ _
    _ ≤ C * ∑' i : u, volume (E ∩ backwardCylinder (P i) (r i)) := by
      apply mul_le_mul_right
      exact ENNReal.tsum_le_tsum fun i => hdensity i (hut i.2)
    _ ≤ C * volume E := mul_le_mul_right hcharge C

/- The literal kinetic maximal set satisfies a weak (1,1) estimate for indicators. -/
theorem maximalCylinderUnion_weak_type {d : ℕ} (E : Set (KineticPoint d)) (tau : ENNReal) :
    tau * volume (maximalCylinderUnion E tau) ≤
      ENNReal.ofReal ((8 : ℝ) ^ (4*d+2)) * volume E := by
  exact cylinder_family_weak_type Prod.fst Prod.snd
    {z : KineticPoint d × ℝ | 0 < z.2 ∧ z.2 ≤ 1 ∧
      tau * volume (backwardCylinder z.1 z.2) ≤ volume (E ∩ backwardCylinder z.1 z.2)}
    1 (fun _ hz => hz.1) (fun _ hz => hz.2.1) E tau (fun _ hz => hz.2.2)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
