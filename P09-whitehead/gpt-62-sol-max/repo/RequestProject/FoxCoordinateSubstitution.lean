module

public import RequestProject.FoxNaturality
public import RequestProject.SubstOneWay

@[expose] public section

/-! Fox coordinates retained by a word substitution. -/

namespace FiniteChains

variable {α β : Type*}

theorem groupRingMap_grp (φ : FreeGroup α →* FreeGroup β) (w : FreeGroup α) :
    MonoidAlgebra.mapDomainRingHom ℤ φ (grp w) = grp (φ w) := MonoidAlgebra.mapDomain_single

/-- If the generator derivatives at `b` are concentrated at `a`, the same
coordinate transformation holds for every word. -/
theorem fox_subst_weighted_coordinate [DecidableEq α] [DecidableEq β]
    (φ : FreeGroup α →* FreeGroup β)
    (a : α) (b : β) (d : FreeGroupRing β)
    (h : ∀ i, fox b (φ (FreeGroup.of i)) = if a = i then d else 0)
    (w : FreeGroup α) :
    fox b (φ w) = MonoidAlgebra.mapDomainRingHom ℤ φ (fox a w) * d := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => rw [h, fox_of]; simp
  | inv_of i ih =>
      rw [map_inv, fox_inv, fox_inv, map_neg, map_mul, ih, groupRingMap_grp, map_inv]
      noncomm_ring
  | mul v w hv hw =>
      rw [map_mul, fox_mul, fox_mul, map_add, map_mul, groupRingMap_grp, hv, hw]
      noncomm_ring

/-- A coordinate of a Fox derivative is preserved when the substituted
generators have the corresponding Kronecker derivatives. -/
theorem fox_subst_coordinate [DecidableEq α] [DecidableEq β]
    (φ : FreeGroup α →* FreeGroup β) (a : α) (b : β)
    (h : ∀ i, fox b (φ (FreeGroup.of i)) = if a = i then 1 else 0)
    (w : FreeGroup α) :
    fox b (φ w) = MonoidAlgebra.mapDomainRingHom ℤ φ (fox a w) := by
  simpa using fox_subst_weighted_coordinate φ a b 1 h w

namespace BlockFamily
universe u
variable {A S : Type u} {I Z : S → Type u}
  [DecidableEq A] [∀ s, DecidableEq (I s)] [∀ s, DecidableEq (Z s)]

/-- Substituting arbitrary old words for the markings retains every internal
Fox coordinate, before taking a quotient or an augmentation. -/
theorem fox_blockSubst_internal (u : ∀ s, I s → FreeGroup A) (s : S)
    (z : Z s) (w : FreeGroup (I s ⊕ Z s)) :
    fox (Sum.inr z) (blockSubst u s w) =
      MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) (fox (Sum.inr z) w) := by
  apply fox_subst_coordinate
  rintro (i | z')
  · rw [blockSubst_of_inl,
      fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl)]
    simp
  · simp only [blockSubst_of_inr, fox_of, Sum.inr.injEq]

end BlockFamily
end FiniteChains
