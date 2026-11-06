module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
import Mathlib.Tactic

/-! # A strict density deficit in the union of critical cylinders -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

variable {d : ℕ} {ι : Type*} (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ) (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R) (E : Set (KineticPoint d)) (hE : NullMeasurableSet E volume)

include hr hR hE
/-- A uniformly sub-full cylinder family leaves a definite fraction of its union outside E. -/
theorem cylinder_union_density_defect
    {eta : ℝ} (heta : 0 ≤ eta)
    (hdensity : ∀ i ∈ t, (volume (E ∩ backwardCylinder (P i) (r i))).toReal ≤
      (1-eta)*(volume (backwardCylinder (P i) (r i))).toReal) :
    ENNReal.ofReal eta * volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
      ENNReal.ofReal ((8 : ℝ)^(4*d+2)) *
        volume ((⋃ i ∈ t, backwardCylinder (P i) (r i)) \ E) := by
  let H := ⋃ i ∈ t, backwardCylinder (P i) (r i)
  apply cylinder_family_weak_type P r t R hr hR (H \ E) (ENNReal.ofReal eta)
  intro i hi

  have heq : (H \ E) ∩ backwardCylinder (P i) (r i) =
      backwardCylinder (P i) (r i) \ E := by
    ext X
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(subset_iUnion₂_of_subset i hi subset_rfl) h.1, h.2⟩, h.1⟩⟩
  rw [heq]
  exact measure_density_defect hE (volume_cylinder_pos_ne_top (P i) (hr i hi)).2
    heta (hdensity i hi)

/-- Real-valued form of the strict density reduction inside a finite critical union. -/
theorem cylinder_union_density_reduction
    (hfinite : volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≠ ⊤)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hdensity : ∀ i ∈ t, (volume (E ∩ backwardCylinder (P i) (r i))).toReal ≤
      (1-eta)*(volume (backwardCylinder (P i) (r i))).toReal) :
    (volume (E ∩ (⋃ i ∈ t, backwardCylinder (P i) (r i)))).toReal ≤
      (1-eta/((8 : ℝ)^(4*d+2))) *
        (volume (⋃ i ∈ t, backwardCylinder (P i) (r i))).toReal := by
  let sharedTerm_77cc915cfb := ((8 : ℝ) ^ (4 * d + 2))
  let H := ⋃ i ∈ t, backwardCylinder (P i) (r i)
  have hD : volume (H \ E) ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)
  have hI : volume (H ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (measure_mono inter_subset_left)

  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD) (cylinder_union_density_defect P r t R hr hR E hE heta hdensity)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal heta,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ sharedTerm_77cc915cfb)] at hreal
  have hsum := congrArg ENNReal.toReal (measure_inter_add_sdiff₀  H hE)
  rw [ENNReal.toReal_add hI hD, inter_comm H E] at hsum

  have hdiv : eta*(volume H).toReal/(sharedTerm_77cc915cfb) ≤ (volume (H \ E)).toReal :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hreal)
  rw [mul_div_right_comm] at hdiv
  nlinarith only [hsum, hdiv]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
