module

public import RequestProject.OrderPosetCovering

@[expose] public section

/-! Actual interval-covering maps remain covering maps after an order isomorphism. -/
namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]
  {f : P → Q}

private theorem postcompose_up (hf : IsPosetCover f) (e : Q ≃o R)
    (a : P) (r : R) (h : e (f a) ≤ r) : ∃! b, a ≤ b ∧ e (f b) = r := by
  simpa only [e.apply_eq_iff_eq_symm_apply] using hf.up a (e.symm r) (e.le_symm_apply.mpr h)

theorem postcompose_orderIso (hf : IsPosetCover f) (e : Q ≃o R) :
    IsPosetCover (fun p => e (f p)) :=
  ⟨e.monotone.comp hf.mono, e.surjective.comp hf.surj,
    postcompose_up hf e, postcompose_up hf.dual e.dual⟩

end FiniteChains.Comb.IsPosetCover
