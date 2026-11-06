module

public import proofs.HordijkSteelThreshold.BooleanEdgeCuts

@[expose] public section

namespace HordijkSteelThreshold

def indexedEdgeStep {V E : Type*} (active : Finset E) (a b : E → V) (x y : V) : Prop :=
  ∃ e ∈ active, a e = x ∧ b e = y

def indexedEdgeReach {V E : Type*} (active : Finset E) (a b : E → V) : V → V → Prop :=
  Relation.EqvGen (indexedEdgeStep active a b)

theorem exists_disabled_separating_bond {V E : Type*} [DecidableEq E]
    (edges active : Finset E) (a b : E → V) (x y : V)
    (hhost : indexedEdgeReach edges a b x y)
    (hxy : ¬ indexedEdgeReach active a b x y) :
    ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ edges \ active ∧
      (booleanEdgeCut edges a b f).Nonempty ∧
      ∀ g : V → Bool, (booleanEdgeCut edges a b g).Nonempty →
        booleanEdgeCut edges a b g ⊆ booleanEdgeCut edges a b f →
        booleanEdgeCut edges a b g = booleanEdgeCut edges a b f := by
  classical
  let f₀ : V → Bool := fun v => decide (indexedEdgeReach active a b x v)
  have hn : ∃ k : ℕ, ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ edges \ active ∧ (booleanEdgeCut edges a b f).card = k := by
    have hx : indexedEdgeReach active a b x x := .refl x
    refine ⟨_, f₀, by simp [f₀, hx, hxy], fun e he => ?_, rfl⟩
    obtain ⟨heE, hdiff⟩ := Finset.mem_filter.mp he
    refine Finset.mem_sdiff.mpr ⟨heE, fun heA => hdiff ?_⟩
    have hab : indexedEdgeReach active a b (a e) (b e) := .rel _ _ ⟨e, heA, rfl, rfl⟩
    have hi : indexedEdgeReach active a b x (a e) ↔ indexedEdgeReach active a b x (b e) :=
      ⟨fun h => .trans _ _ _ h hab, fun h => .trans _ _ _ h (.symm _ _ hab)⟩
    simp only [f₀, hi]
  obtain ⟨f, hf, hc, hcard⟩ := Nat.find_spec hn
  refine ⟨f, hf, hc, ?_, minimal_separating_cut_is_bond edges a b (edges \ active) x y f hf hc
    fun g hg hgc => hcard ▸ Nat.find_min' hn ⟨g, hg, hgc, rfl⟩⟩
  by_contra hne
  apply hf; clear hxy f₀ hn hf hcard
  induction hhost with
  | rel _ _ h => obtain ⟨e, he, rfl, rfl⟩ := h; by_contra hd; exact hne ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end HordijkSteelThreshold
