/- Equivalences of literal lower domains induced by occurrence maps. -/
module

public import VaughtConjecture.Knight.Cell

@[expose] public section

namespace VaughtConjecture.Knight.CellScheme

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  {D : CellScheme A} {E : CellScheme B} {I J : Finset ι × ℕ}

noncomputable def belowEquivOfMap (f : Cell D → Cell E) (hf : Function.Injective f)
    (h : ∀ d, GradedLe (D.cell d) I ↔ GradedLe (E.cell (f d)) J)
    (exhaustive : ∀ d, GradedLe (E.cell d) J → ∃ c, f c = d) : D.below I ≃ E.below J :=
  Equiv.ofBijective (fun d => ⟨f d.1, (h _).mp d.2⟩) ⟨by
    intro d e he
    exact Subtype.ext (hf (congrArg Subtype.val he)), by
    intro d
    obtain ⟨c, hc⟩ := exhaustive d.1 d.2
    exact ⟨⟨c, (h c).mpr (hc ▸ d.2)⟩, Subtype.ext hc⟩⟩

noncomputable def belowEquivOfIndex (f : Cell D → Cell E) (hf : Function.Injective f)
    (h : ∀ d, E.cell (f d) = D.cell d)
    (exhaustive : ∀ d, GradedLe (E.cell d) J → ∃ c, f c = d) : D.below J ≃ E.below J :=
  belowEquivOfMap f hf (fun d => by rw [h d]) exhaustive

end VaughtConjecture.Knight.CellScheme
