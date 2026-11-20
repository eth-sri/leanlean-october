module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Separation.Hausdorff
public import RequestProject.SmoothCompactExtension

/-!
# Smooth inverse coordinates near a compact injective set

Compact injectivity and local invertibility give an inverse on an open
neighborhood, rather than a homeomorphism of the whole plane. Smooth
functions in these inverse coordinates then have genuine compactly
supported physical representatives near the image of the compact set.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter
open scoped Topology

theorem localSmoothInverse_testFunction (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ f : ℂ → ℂ, TestFunction univ f ∧
      ∀ x ∈ e '' K, f =ᶠ[𝓝 x] (φ ∘ e.symm) := by
  apply exists_smooth_compact_extension
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)) e.open_target
    (image_subset_iff.mpr (fun x hx => e.mapsTo (hKs hx)))
  exact hφ.comp_contDiffOn hes

end PolyaNeumann

end
