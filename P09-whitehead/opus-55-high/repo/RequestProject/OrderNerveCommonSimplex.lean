import RequestProject.OrderNerveRealizationContraction


namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical
variable {P : Type} [PartialOrder P]

/-- Two simplices whose vertices are pairwise cross-comparable lie in an actual
common simplex, with explicit simplex operators for both inclusions. -/
theorem orderNerveSimplex_common
    (s : (nerve P).obj (Opposite.op n)) (t : (nerve P).obj (Opposite.op k))
    (hc : ∀ i j, s.obj i ≤ t.obj j ∨ t.obj j ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (b : k ⟶ m),
      (nerve P).map a.op u = s ∧ (nerve P).map b.op u = t := by
  classical
  let A := Set.range s.obj ∪ Set.range t.obj
  have hA : IsChain (· ≤ ·) A := by
    intro x hx y hy _
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (s.map (homOfLE h)))
        · exact Or.inr (leOfHom (s.map (homOfLE h)))
      simp_all
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · grind
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (t.map (homOfLE h)))
        · exact Or.inr (leOfHom (t.map (homOfLE h)))
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  letI : Nonempty A := ⟨⟨s.obj 0, Or.inl ⟨0, rfl⟩⟩⟩
  cases' Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A))) with r hr
  let e := (Fintype.orderIsoFinOfCardEq A hr).symm
  let u :=
    (show Monotone (fun i => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor
  let a := SimplexCategory.mkHom
    ⟨fun i => e ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (s.map (homOfLE h)))⟩
  let b := SimplexCategory.mkHom
    ⟨fun i => e ⟨t.obj i, Or.inr ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (t.map (homOfLE h)))⟩
  refine ⟨⦋r⦌, u, a, b, ?_, ?_⟩
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply _))
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply _))
