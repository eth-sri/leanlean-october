module

public import RequestProject.ExponentCorrection

@[expose] public section

/-!
# Words in commuting elements, and the elimination step of Lemma 3.1

If the images `u i` of the generators of a free group pairwise commute, then the image of a
word depends only on its vector of exponent sums.  Consequently, if a family of words `r j`
maps to `1` and the exponent vectors of the `r j` span the whole lattice `ℤ^{(I)}`, then
every `u i` is trivial (`FiniteChains.eq_one_of_expCol_surjective`).

This is the elimination used twice in Section 3 of the paper: in Lemma 3.1 it turns the
relators `r_j(U) = ∏_i U_i^{M_{ij}}` of the reduced presentation of `Y_D`, together with
surjectivity of the exponent-sum matrix `M` of the acyclic core, into `U_i = [a_i, b_i] = 1`.
`RequestProject/InitialPair.lean` records the same step in the shape in which the paper
states it; the version proved here is the one used to compute the fundamental group of the
complex `Y_D` built in `RequestProject/InitialComplex.lean`.
-/


namespace FiniteChains

universe u v

variable {I : Type u} {H : Type v} [Group H]

open scoped IsMulCommutative in
/-- **The elimination step.**  Let the elements `u i` of a group commute pairwise, let each
word `r j` map to `1`, and let the exponent vectors of the `r j` span `ℤ^{(I)}`.  Then every
`u i` is trivial. -/
theorem eq_one_of_expCol_surjective {J : Type*} (u : I → H) (hu : ∀ i k, Commute (u i) (u k))
    (r : J → FreeGroup I) (hrel : ∀ j, FreeGroup.lift u (r j) = 1)
    (hsurj : Function.Surjective (expMatrix r)) : ∀ i, u i = 1 := by
  let S := Subgroup.closure (Set.range u)
  letI : IsMulCommutative S := Subgroup.isMulCommutative_closure (k := Set.range u) (by
    rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ _
    exact hu i k)
  let U (i : I) : S := ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let g := (FreeAbelianGroup.lift (Additive.ofMul ∘ U)).comp Finsupp.toFreeAbelianGroup
  have hg (i : I) : g (Finsupp.single i 1) = Additive.ofMul (U i) := by simp [g]
  have hword : (AddMonoidHom.toMultiplicativeLeft g).comp expSumTotal = FreeGroup.lift U := by
    apply FreeGroup.ext_hom
    intro i
    change Additive.toMul (g (expSumTotal (FreeGroup.of i)).toAdd) = _
    rw [expSumTotal_of, hg, FreeGroup.lift_apply_of]
    rfl
  have hsub : S.subtype.comp (FreeGroup.lift U) = FreeGroup.lift u := by
    apply FreeGroup.ext_hom
    intro i
    simp [U]
  have hcol (j : J) : g (expVec (r j)) = 0 := by
    change Additive.ofMul ((AddMonoidHom.toMultiplicativeLeft g).comp expSumTotal (r j)) = 0
    rw [hword]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    exact (DFunLike.congr_fun hsub (r j)).trans (hrel j)
  have hzero (c) : g (expMatrix r c) = 0 := by
    simp [expMatrix_apply, Finsupp.sum, map_sum, map_zsmul, hcol]
  intro i
  have hz : ∀ x, g x = 0 := hsurj.forall.2 hzero
  have h := hz (Finsupp.single i 1)
  rw [hg] at h
  exact congrArg (fun x => (Additive.toMul x : S).val) h

end FiniteChains
