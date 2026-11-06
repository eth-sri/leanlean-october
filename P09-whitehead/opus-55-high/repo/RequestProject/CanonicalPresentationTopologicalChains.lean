import RequestProject.PresentationWordTopologicalChains


namespace FiniteChains.PresModel
variable {α J : ℕ → Type}

/-- Carry the chosen padding generator along the given generator inclusions. -/
def presentationMarkedGenerator (f : ∀ i, α i ↪ α (i + 1)) (a : α 0) : ∀ i, α i
  | 0 => a
  | i + 1 => f i (presentationMarkedGenerator f a i)

variable [∀ i, DecidableEq (α i)]
  (ρ : ∀ i, J i → FreeGroup (α i))
  (f : ∀ i, α i ↪ α (i + 1)) (g : ∀ i, J i ↪ J (i + 1))
  (hr : ∀ i j, ρ (i + 1) (g i j) = FreeGroup.map (f i) (ρ i j)) (a : α 0)

/-- All nonempty word representatives and their literal compatibility are
derived from the labelled group presentations, simultaneously at every stage. -/
def canonicalPresentationStep (i : ℕ) :
    PresWordEmbedding (presCanonicalWords (ρ i) (presentationMarkedGenerator f a i))
      (presCanonicalWords (ρ (i + 1)) (presentationMarkedGenerator f a (i + 1))) :=
  canonicalPresWordEmbedding _ _ _ _ (hr i)
    _
