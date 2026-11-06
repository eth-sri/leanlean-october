module

public import HypoellipticAleksandrov.Parabolic.NestedQuantitativeSmoothCutoffExistence
public import HypoellipticAleksandrov.Parabolic.ParabolicW12TimeReflection

/-!
# Original-time interior geometry

This file constructs the nested spatial cutoffs and strict reverse-time slabs
used to invoke the interior Caccioppoli theorem on an original-time cylinder.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/- Compact containment of an original-time cylinder supplies the nested
spatial cutoffs and strict reverse-time slabs required by the interior
Caccioppoli theorem. -/
theorem reverseTimeMap_preimage_originalTimeInteriorCylinder
    {d } (r₁ s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) :
    reverseTimeMap r₁ ⁻¹'
        (Set.Ioo (r₁ - s₁) (r₁ - s₀) ×ˢ O) =
      Set.Ioo s₀ s₁ ×ˢ O := by
  ext z
  rcases z with ⟨r, y⟩
  simp only [Set.mem_preimage, reverseTimeMap_apply, Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hl, hu⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩
  · rintro ⟨⟨hl, hu⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
