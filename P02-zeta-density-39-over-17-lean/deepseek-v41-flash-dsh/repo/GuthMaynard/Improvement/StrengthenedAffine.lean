module
public import GuthMaynard.Improvement.UnequalFullInput

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Literal supremum norm for ordinary real inputs. For the compact smooth
inputs of the endpoint, boundedness and agreement with the Schwartz
order-zero seminorm are proved below. -/
def sourceSup (f : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |f x|))

def FourierSupInput (D : ℝ → ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ n : ℕ, ∀ ξ : ℝ, ξ ≠ 0 →
    ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤ D β n*T^β*(T/|ξ|)^n*sourceSup f

theorem sourceSup_eq_seminorm (f : 𝓢(ℝ, ℝ)) :
    sourceSup f = SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
  have hbound : ∀ x, |f x| ≤ SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
    intro x
    simpa only [gmAffineComplexify_apply,Complex.norm_real,Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (gmAffineComplexify f) x
  have hbdd : BddAbove (Set.range (fun x => |f x|)) :=
    ⟨_,by rintro y ⟨x,rfl⟩; exact hbound x⟩
  have hle : ∀ x, |f x| ≤ sourceSup f := fun x => le_csSup hbdd (mem_range_self x)
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro y ⟨x,rfl⟩; exact hbound x)
  · apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) 0 0 _ ((abs_nonneg (f 0)).trans (hle 0))
    intro x
    simpa only [pow_zero,iteratedDeriv_zero,one_mul,gmAffineComplexify_apply,Complex.norm_real,Real.norm_eq_abs] using hle x

end GuthMaynard.Improvement
