import Mathlib.Tactic

import GS.Extensions.OriginalFibres
open GS.MatrixBase




/-!
# Uniform small-domain conditions for the original fibre argument

Scalar sign/angle assumptions are proved uniformly
on K_eta from continuity. The one analytic input that remains is an open
neighbourhood V of zero on which the actual originalPsi is injective.
No neighbourhood COVERAGE of the whole GS family is asserted by this module.
-/

namespace GS.Extensions

-- Use the coordinatewise maximum norm only in this module.
attribute [local instance] Matrix.normedAddCommGroup

/-- The default product norm is BOUNDED BY a Frobenius radius; it is not
identified with the Frobenius norm. -/
 theorem matrix_norm_le_of_frobSq_le {A : Mat q} {η : ℝ}
    (hη : 0≤η) (h : cFrobSq A≤η^2) : ‖A‖≤η := by
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro j
  simpa only [Real.norm_eq_abs,abs_of_nonneg hη] using abs_entry_le_of_frobSq_le h i j

 theorem originalPsi_positive_domain_open (Q₀ : Mat q) :
    IsOpen {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j} := by
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const (by
    have hc := continuous_originalPsi Q₀
    fun_prop)

 theorem exists_uniform_normalized_original (Q₀ : Mat q)
    (hQ : ∀ i j, Q₀ i j≠0) (V : Set (Mat q))
    (hV : IsOpen V) (h₀ : (0:Mat q)∈V) :
    ∃ η : ℝ, 0<η ∧ ∀ p ∈ originalK q η, NormalizedOriginal Q₀ V p := by
  let W := V ∩ {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j}
  have hW := hV.inter (originalPsi_positive_domain_open Q₀)
  have hW₀ : (0:Mat q)∈W := by aesop (add norm [originalPsi_zero])
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW 0 hW₀
  let η := min (δ/4) (Real.pi/8)
  have hη : 0<η := lt_min (by positivity) (by positivity)
  have hηδ : η≤δ/4 := min_le_left _ _
  refine ⟨η,hη,?_⟩
  rintro ⟨ell,r,c,z,u⟩ hp
  rcases hp with ⟨he,hr,hr₀,hc,hz,hcn,hzn,hu⟩
  have hcnorm := matrix_norm_le_of_frobSq_le hη.le hcn
  have hznorm := matrix_norm_le_of_frobSq_le hη.le hzn
  have hcplus : c+z∈W := by
    apply hball
    change dist (c+z) 0 < δ
    rw [dist_zero_right]
    have hn := norm_add_le c z
    linarith
  have hcminus : c-z∈W := by
    apply hball
    change dist (c-z) 0 < δ
    rw [dist_zero_right]
    have hn := norm_sub_le c z
    linarith
  refine ⟨hu,hr₀,?_,?_,hcplus.1,hcminus.1⟩
  · grind
  · grind



end GS.Extensions
