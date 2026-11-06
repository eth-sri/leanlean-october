module

public import proofs.HordijkSteelThreshold.BooleanEdgeCuts

@[expose] public section

namespace HordijkSteelThreshold

variable {V E : Type*}

variable (active : Finset E) (a b : E → V)

def indexedEdgeStep   (x y : V) : Prop :=
  ∃ e ∈ active, a e = x ∧ b e = y

def indexedEdgeReach   : V → V → Prop :=
  Relation.EqvGen $ indexedEdgeStep active a b


theorem eqvGen_congr {α β : Type*} {r : α → α → Prop} (f : α → β)
    (h : ∀ a b, r a b → f a = f b) {a b : α} (hab : Relation.EqvGen r a b) : f a = f b :=
  (Equivalence.eqvGen_iff (r := fun x y => f x = f y) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩).1 $ hab.mono h

/-- Any pair connected in the host but disconnected by the enabled edges
has a disabled separating bond. The conclusion gives global cut minimality,
which is what the diamond-potential argument requires. -/
theorem exists_disabled_separating_bond  [DecidableEq E]
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
  have hn : ∃ k : ℕ, ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ edges \ active ∧ (booleanEdgeCut edges a b f).card = k := by
    refine ⟨_, fun v => decide $ indexedEdgeReach active a b x v,
      by simpa using fun h => hxy $ h.1 $ Relation.EqvGen.refl x, fun e he => ?_, rfl⟩
    simp only [booleanEdgeCut, Finset.mem_filter, Finset.mem_sdiff] at he ⊢
    refine ⟨he.1, fun heA => he.2 ?_⟩
    have hab : Relation.EqvGen (indexedEdgeStep active a b) (a e) (b e) := .rel _ _ ⟨e, heA, rfl, rfl⟩
    exact decide_eq_decide.2 ⟨(.trans _ _ _ · hab), (.trans _ _ _ · hab.symm)⟩
  obtain ⟨f, hf, hc, hcard⟩ := Nat.find_spec hn
  have hmin g hg hgc :
      (booleanEdgeCut edges a b f).card ≤ (booleanEdgeCut edges a b g).card :=
    hcard ▸ Nat.find_min' hn ⟨g, hg, hgc, rfl⟩
  refine ⟨f, hf, hc, ?_, fun g hgne hgsub => ?_⟩
  · by_contra hn
    exact hf $ eqvGen_congr f (fun _ _ ⟨e, he, ha, hb⟩ => ha ▸ hb ▸ by
      by_contra hd; exact hn ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩⟩) hhost
  by_cases hsep : g x ≠ g y
  · exact Finset.eq_of_subset_of_card_le hgsub $ hmin g hsep $ hgsub.trans hc
  have := hmin (fun v => f v ^^ g v) $ by simp_all
  have hx : booleanEdgeCut edges a b (fun v => f v ^^ g v) = booleanEdgeCut edges a b f \ booleanEdgeCut edges a b g := by
    ext e
    have := @hgsub e
    revert this
    simp only [booleanEdgeCut, Finset.mem_filter, Finset.mem_sdiff]
    cases f (a e) <;> cases f (b e) <;> cases g (a e) <;> cases g (b e) <;> simp_all
  grind

end HordijkSteelThreshold
