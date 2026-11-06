import Mathlib.Tactic

import RequestProject.PresPosetReading

/-!
# The comparison with the model built on a prescribed choice of relator words

`RequestProject/PresPosetAlpha.lean` and `RequestProject/PresPosetReading.lean` compare a
presentation `ρ` with the poset model of its presentation complex built on the *canonical*
choice `presWords ρ` of representing words.  For the surface block the attaching words matter:
the polygon of the surface must read the relator word letter by letter, so the model has to be
built on the **prescribed** word family `w` with `FreeGroup.mk (w j) = ρ j`.

This file repeats the two halves of the comparison for such a prescribed `w`:

* `FiniteChains.PresModel.alphaHomW` — the marked comparison homomorphism of `ρ` with the
  fundamental group of `PresPos w`;
* `FiniteChains.PresModel.alphaHomW_injective` — it is injective, the reading homomorphism of
  the model being a left inverse.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel


open Comb


variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

include hw

/-- **The marked comparison homomorphism** of the presentation `ρ` with the model built on the
prescribed relator words `w`. -/
def alphaHomW : PresGroup ρ →* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  QuotientGroup.lift _ (alphaFree w) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    have h := alphaFree_relator w j
    rwa [hw j] at h)

@[simp] theorem alphaHomW_mk (x : FreeGroup α) :
    alphaHomW ρ w hw (QuotientGroup.mk x) = alphaFree w x := rfl



/-- The reading homomorphism of the model with values in the presentation group. -/
def readingPresW : Pi1 (orderCx (PresPos w)) (ptBase w) →* PresGroup ρ :=
  reading w (fun i => QuotientGroup.mk (FreeGroup.of i)) (by
    intro j
    have hlift : (FreeGroup.lift fun i : α => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
        = QuotientGroup.mk' (relSub ρ) := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp
    show FreeGroup.lift _ (FreeGroup.mk (w j)) = 1
    rw [hlift, hw j]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨j, rfl⟩)))

theorem readingPresW_alphaHomW (x : PresGroup ρ) :
    readingPresW ρ w hw (alphaHomW ρ w hw x) = x := by
  induction x using QuotientGroup.induction_on with
  | _ y =>
      have key : ((readingPresW ρ w hw).comp (alphaHomW ρ w hw)).comp
          (QuotientGroup.mk' (relSub ρ)) = QuotientGroup.mk' (relSub ρ) := by
        aesop
      exact DFunLike.congr_fun key y

/-- **The presentation group embeds into the fundamental group of the model built on the
prescribed relator words.** -/
abbrev alphaHomW_injective  :=
  Function.LeftInverse.injective (FiniteChains.PresModel.readingPresW_alphaHomW ρ w hw)

end FiniteChains.PresModel

