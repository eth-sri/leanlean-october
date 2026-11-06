module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Polymer RAF.Concrete

/-- A finite executable evaluator, using the literal source's closure iteration. -/
def computedClosure (N L : ℕ) (S : Finset $ Reaction N) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S $ Fintype.card $ Molecule N

variable {M R : Type*}

/-- A bounded potential that grows at every nonstationary round forces stabilization. -/
theorem revClosureAt_sub  [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)
    (μ : Finset M → ℕ) (B : ℕ) (hB : ∀ C, μ C ≤ B)
    (hμ : ∀ C, revClosureStep Q S C ≠ C → μ C < μ (revClosureStep Q S C)) (k : ℕ) :
    revClosureAt Q S k ⊆ revClosureAt Q S B := by
  have h1 k : k ≤ μ (revClosureAt Q S k) ∨ revClosureAt Q S (k+1) = revClosureAt Q S k := by
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
      · exact .inr $ congrArg (revClosureStep Q S) he
      · exact .inl $ (ih.resolve_right he).trans_lt $ hμ _ he
  have h2 : revClosureAt Q S (B+1) = revClosureAt Q S B := by
    by_contra hn
    have := hμ _ hn
    grind
  induction k with
  | zero => exact revClosureAt_mono_stage Q S $ Nat.zero_le _
  | succ k ih => exact (revClosureStep_mono Q subset_rfl ih).trans h2.subset

variable [Fintype M] [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)

theorem card_closure_sub   (k : ℕ) : revClosureAt Q S k ⊆ revClosureAt Q S (Fintype.card M) :=
  revClosureAt_sub Q S _ _ Finset.card_le_univ (fun _ h =>
    Finset.card_lt_card $ Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, Ne.symm h⟩) k

theorem filter_closure_eq   [DecidablePred fun x => ∃ k, x ∈ revClosureAt Q S k] :
    Finset.univ.filter (∃ k, · ∈ revClosureAt Q S k) = revClosureAt Q S (Fintype.card M) := by
  ext
  simp
  exact ⟨fun ⟨k, h⟩ => card_closure_sub Q S k h, fun h => ⟨_, h⟩⟩


/-- Exact semantics: the executable finite iteration equals the existing closure. -/
theorem computedClosure_eq (N L : ℕ) (S : Finset $ Reaction N) :
    computedClosure N L S = temporaryReactionClosure L S :=
  by classical exact (filter_closure_eq _ _).symm

end RAFCriticalWindowQuantitative
