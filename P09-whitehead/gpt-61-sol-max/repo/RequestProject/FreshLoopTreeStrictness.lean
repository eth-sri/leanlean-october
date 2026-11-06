import Mathlib.Tactic

import RequestProject.TreeExtension

/-! A fresh loop or a fresh face survives collapse of compatible spanning
trees. Ordinary strictness by a fresh edge alone would not suffice.
 -/

namespace FiniteChains.Comb

variable {X Y : Complex2.{u}}

def FreshLoopOrFace (h : Hom X Y)  :=
  (∃ e : Y.E, Y.src e = Y.tgt e ∧ e ∉ Set.range h.onE) ∨
    ∃ f : Y.F, f ∉ Set.range h.onF

namespace SpanningTree

theorem height_step_of_isTree (T : SpanningTree X) {e : X.E} (he : T.isTree e) :
    T.ht (X.src e) + 1 = T.ht (X.tgt e) ∨
      T.ht (X.tgt e) + 1 = T.ht (X.src e) := by
  classical grind [FiniteChains.Comb.SpanningTree.isTree_iff, FiniteChains.Comb.SpanningTree.up_src, FiniteChains.Comb.SpanningTree.up_ht, germSrc, germTgt]

theorem not_isTree_of_loop (T : SpanningTree X) {e : X.E}
    (he : X.src e = X.tgt e) : ¬T.isTree e := by
  intro ht
  have hs := T.height_step_of_isTree ht
  rw [he] at hs
  omega

theorem nonTree_or_face_fresh {h : Hom X Y} {T : SpanningTree X}
    {U : SpanningTree Y} (ht : ∀ e, U.isTree (h.onE e) ↔ T.isTree e)
    (hp : FreshLoopOrFace h) :
    (∃ a : NonTree U, a ∉ Set.range (nonTreeIncl ht)) ∨
      ∃ f : Y.F, f ∉ Set.range h.onF := by
  rcases hp with ⟨e, hloop, he⟩ | hf
  · left
    refine ⟨⟨e, U.not_isTree_of_loop hloop⟩, ?_⟩
    rintro ⟨a, ha⟩
    exact he ⟨a.val, congrArg Subtype.val ha⟩
  · exact Or.inr hf

end FiniteChains.Comb.SpanningTree

