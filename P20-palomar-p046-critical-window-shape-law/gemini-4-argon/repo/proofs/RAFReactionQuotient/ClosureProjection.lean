module

public import proofs.RAF.Concrete.SeedGateway

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF RAF.Concrete

variable {M R J : Type*} [DecidableEq M] [DecidableEq R] [DecidableEq J]

omit [DecidableEq R] in
/-- Identifying reaction descriptions with identical chemistry preserves every
finite stage of ordinary reversible closure. -/
theorem closureAt_image (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (S : Finset R) (k : ℕ) :
    revClosureAt P (S.image π) k = revClosureAt Q S k := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    simp only [revClosureAt, ih, revClosureStep]
    congr 1
    ext x
    simp [Finset.mem_biUnion, RevEnabledLhs, RevEnabledRhs, hl, hr]

def orCatalysis (π : R → J) (C : Catalysis M R) : Catalysis M J :=
  fun x j => ∃ r, π r = j ∧ C x r

omit [DecidableEq R] in
/-- Projection of a RAF retains its catalytic witnesses. -/
theorem raf_image (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (C : Catalysis M R) (S : Finset R) (hS : IsRevRAF Q C S) :
    IsRevRAF P (orCatalysis π C) (S.image π) := by
  refine ⟨hS.1.image π, ?_, ?_⟩
  · intro j hj
    obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k, hk⟩ := hS.2.1 r hmem
    exact ⟨k, by simpa only [hl, hr, closureAt_image Q P π hl hr hf] using hk⟩
  · intro j hj
    obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨x, k, hx, hc⟩ := hS.2.2 r hmem
    exact ⟨x, k, by rwa [closureAt_image Q P π hl hr hf], r, rfl, hc⟩

end RAFReactionQuotient
