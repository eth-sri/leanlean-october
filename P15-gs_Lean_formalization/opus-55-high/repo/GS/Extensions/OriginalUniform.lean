module

public import GS.Extensions.OriginalFibres

@[expose] public section


/-!
# Uniform small-domain conditions for the original fibre argument

Scalar sign/angle assumptions are proved uniformly
on K_eta from continuity. The one analytic input that remains is an open
neighbourhood V of zero on which the actual originalPsi is injective.
No neighbourhood COVERAGE of the whole GS family is asserted by this module.
-/

noncomputable section
namespace GS.Extensions

-- Use the coordinatewise maximum norm only in this module.
attribute [local instance] Matrix.normedAddCommGroup

/-- The full same-fibres statement on some compact K_eta now needs only the
standard local exponential-chart input, not separately supplied signs/angles
or an assumption that f and g have the same fibres. -/
 theorem original_same_fibres_of_open_chart {q : ℕ} (hq : 0<q) (Q₀ : Mat q)
    (hQ : ∀ i j, Q₀ i j≠0) (V : Set (Mat q))
    (hV : IsOpen V) (h₀ : (0:Mat q)∈V) (hinj : Set.InjOn (originalPsi Q₀) V) :
    ∃ η : ℝ, 0<η ∧ ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p=originalF Q₀ p' ↔ originalG p=originalG p' := by
  let W := V ∩ {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j}
  have hc := continuous_originalPsi Q₀
  have hW : IsOpen W := hV.inter (by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (by fun_prop))
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW 0 ⟨h₀, by simp_all [originalPsi_zero]⟩
  let η := min (δ/4) (Real.pi/8)
  have hη : 0<η := by positivity
  have hn : ∀ p ∈ originalK q η, NormalizedOriginal Q₀ V p := by
    rintro ⟨ell,r,c,z,u⟩ ⟨he,hr,hr₀,hc,hz,hcn,hzn,hu⟩
    have hnorm {A : Mat q} (h : frobSq A≤η^2) : ‖A‖≤η :=
      (pi_norm_le_iff_of_nonneg hη.le).mpr fun i => (pi_norm_le_iff_of_nonneg hη.le).mpr fun j => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg hη.le] using abs_entry_le_of_frobSq_le h i j
    have h1 := hnorm hcn
    have h2 := hnorm hzn
    have hcplus : c+z∈W := hball (by simp; grind [norm_add_le c z])
    have hcminus : c-z∈W := hball (by simp; grind [norm_sub_le c z])
    refine ⟨hu,hr₀,?_,?_,hcplus.1,hcminus.1⟩ <;> grind
  exact ⟨η,hη,fun p hp p' hp' => original_same_fibres_normalized hq Q₀ V hinj p p'
    (hn p hp) (hn p' hp')⟩

end GS.Extensions
