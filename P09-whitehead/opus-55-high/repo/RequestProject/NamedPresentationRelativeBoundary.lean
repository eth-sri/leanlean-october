import RequestProject.NamedPresentationFoxMatrix
noncomputable section


/-! Exact relative Fox coordinates over an arbitrary receiving group ring. -/
namespace FiniteChains.NamedPresentation
variable {α J I G : Type} [DecidableEq α] [DecidableEq I] [Fintype J] [Fintype I]
  [Group G] (ρ : J → FreeGroup α) (w : I → FreeGroup α)
  (φ : PresGroup (rel ρ w) →* G)

def receivedWordCoefficientMap :=
  (MonoidAlgebra.mapDomainRingHom ℤ φ).comp (wordCoefficientMap ρ w)

def receivedFoxBoundary (β : J ⊕ I → MonoidAlgebra ℤ G)
    (g : α ⊕ I) :=
  ∑ m, β m * MonoidAlgebra.mapDomainRingHom ℤ φ (foxMatrixPres _ g m)

/-- Vanishing at the internal generators is an equality between the old
two-boundary and the chain of the marked word paths, not an absolute cycle. -/
theorem receivedFoxBoundary_internal β a :
    receivedFoxBoundary ρ w φ β (Sum.inl a) =
      (∑ j, β (Sum.inl j) * receivedWordCoefficientMap ρ w φ (fox a (ρ j))) -
      ∑ i, β (Sum.inr i) * receivedWordCoefficientMap ρ w φ (fox a (w i)) := by
  classical
  rw [receivedFoxBoundary, Fintype.sum_sum_type]
  simp [matrix_internal_relator, matrix_internal_name, map_neg, mul_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem receivedFoxBoundary_internal_zero_iff β :
    (∀ a, receivedFoxBoundary ρ w φ β (Sum.inl a) = 0) ↔
      ∀ a, (∑ j, β (Sum.inl j) * receivedWordCoefficientMap ρ w φ (fox a (ρ j))) =
        ∑ i, β (Sum.inr i) * receivedWordCoefficientMap ρ w φ (fox a (w i)) := by
  simp [receivedFoxBoundary_internal, sub_eq_zero]
