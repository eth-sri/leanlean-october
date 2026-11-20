module

public import RequestProject.TreeExtension

@[expose] public section

/-! A fresh loop or a fresh face survives collapse of compatible spanning
trees. Ordinary strictness by a fresh edge alone would not suffice.
 -/

namespace FiniteChains.Comb
universe u

variable {X Y : Complex2.{u}}

def FreshLoopOrFace (h : Hom X Y) :=
  (∃ e : Y.E, Y.src e = Y.tgt e ∧ e ∉ Set.range h.onE) ∨
    ∃ f : Y.F, f ∉ Set.range h.onF

namespace SpanningTree

variable (T : SpanningTree X) {e : X.E}

theorem height_step_of_isTree (he : T.isTree e) :
    T.ht (X.src e) + 1 = T.ht (X.tgt e) ∨
      T.ht (X.tgt e) + 1 = T.ht (X.src e) := by
  obtain ⟨a, ha, hea⟩ := (T.isTree_iff e).mp he
  have hs := T.up_src a ha
  have hh := T.up_ht a ha
  cases hb : (T.up a ha).2 with
  | false =>
      simp_all [germSrc, hb, hea, germTgt]
  | true =>
      simp_all [germSrc, hb, hea, germTgt]

theorem not_isTree_of_loop
    (he : X.src e = X.tgt e) : ¬T.isTree e := by
  intro ht
  have hs := T.height_step_of_isTree ht
  simp_all

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

end SpanningTree
end FiniteChains.Comb
