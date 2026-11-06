module

public import RequestProject.TraceH1
public import RequestProject.SmoothDiskCutoff
public import Mathlib.Tactic.Ring

/-!
# Actual smooth pullback tests in local disk coordinates

The coordinate function need only be smooth near the closed disk.
Composition followed by a fixed cutoff is linear in the source test.
Its values and differential on the closed disk are the actual composed
values and chain differential.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Metric

variable {R : ℝ}

/-- A global smooth test representing composition in a disk neighbourhood. -/
def smoothDiskCompositionLin  (hR : 1 < R) (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (ball 0 R)) :
    smoothTraceTests →ₗ[ℂ] smoothTraceTests where
  toFun f := ⟨smoothDiskCutoff R hR ((f : ℂ → ℂ) ∘ F),
    smoothDiskCutoff_testFunction hR (f.property.1.comp_contDiffOn hF)⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    change (smoothDiskCutoffBump R hR z : ℂ) * (f (F z) + g (F z)) =
      (smoothDiskCutoffBump R hR z : ℂ) * f (F z) +
        (smoothDiskCutoffBump R hR z : ℂ) * g (F z)
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change (smoothDiskCutoffBump R hR z : ℂ) * (c * f (F z)) =
      c * ((smoothDiskCutoffBump R hR z : ℂ) * f (F z))
    ring

theorem smoothDiskCompositionLin_eq_closedDisk  (hR : 1 < R)
    F hF
    f  (hz : z ∈ closedBall 0 1) :
    smoothDiskCompositionLin hR F hF f z = f (F z) :=
  smoothDiskCutoff_eq_closedDisk hR ((f : ℂ → ℂ) ∘ F) hz

theorem fderiv_smoothDiskCompositionLin  (hR : 1 < R)
    F hF
    f  (hz : z ∈ closedBall 0 1) :
    fderiv ℝ (smoothDiskCompositionLin hR F hF f : ℂ → ℂ) z =
      (fderiv ℝ (f : ℂ → ℂ) (F z)).comp (fderiv ℝ F z) := by
  change fderiv ℝ (smoothDiskCutoff R hR (f ∘ F)) z = _
  rw [fderiv_smoothDiskCutoff_eq hR (f ∘ F) hz]
  exact fderiv_comp z (f.property.1.differentiable (by simp) (F z))
    ((hF.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt
      (by simp))

end PolyaNeumann

end
