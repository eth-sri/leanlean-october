/- Reconstruction of all rows from an original proper boundary and an enlarged grade cut. -/
module

public import VaughtConjecture.Knight.SemanticPatch
public import VaughtConjecture.Knight.GradeCutBoundary

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D L E : CellScheme A} {k : ℕ}

structure GradeCutAssembly (D L E : CellScheme A) (k : ℕ) where
  old : Cell D ↪ Cell E
  low : Cell L ↪ Cell E
  old_index : ∀ c, E.cell (old c) = D.cell c
  low_index : ∀ c, E.cell (low c) = L.cell c
  old_proper : ∀ c, ¬ A ⊆ D.scope c
  low_height : ∀ c, L.grade c ≤ k
  proper_exhaustive : ∀ d, ¬ A ⊆ E.scope d → ∃ c, old c = d
  cut_exhaustive : ∀ d, E.grade d ≤ k → ∃ c, low c = d
  cover : ∀ d, (∃ a, old a = d) ∨ (∃ b, low b = d)
  common : Cell (GradeCutBoundary.scheme D k) → Cell L
  common_map : ∀ c, low (common c) = old (GradeCutBoundary.toCell D k c)

namespace GradeCutAssembly

noncomputable section

/-- The original proper carrier together with its bare grade cut. -/
def initial (D : CellScheme A) (k : ℕ) (hp : ∀ d : Cell D, D.scope d ≠ A) :
    GradeCutAssembly D (GradeCutBoundary.scheme D k) D k where
  old := Function.Embedding.refl _
  low := (GradeCutBoundary.toCell D k).toEmbedding
  old_index _ := rfl
  low_index _ := rfl
  old_proper d hd := hp d (Finset.Subset.antisymm (D.scope_subset d) hd)
  low_height := GradeCutBoundary.grade_bound D k
  proper_exhaustive d _ := ⟨d, rfl⟩
  cut_exhaustive _ := GradeCutBoundary.exhaustive D k
  cover d := Or.inl ⟨d, rfl⟩
  common := id
  common_map _ := rfl

open SourceLayerCarrier in
/-- Add the same full-scope layer on both sides of an assembled grade cut. -/
def append (G : GradeCutAssembly D L E k) (Q : Type*) [Fintype Q]
    (j : ℕ) (hj : 0 < j) (hA : j ≤ A.card) (hjk : j ≤ k) :
    GradeCutAssembly D (scheme L Q j hj hA) (scheme E Q j hj hA) k where
  old := G.old.trans ⟨fun d => toCell E Q j hj hA (.inl d), (old_order E Q j hj hA).injective⟩
  low := appendMap Q j hj hA G.low
  old_index d := (cell_toCell E Q j hj hA (.inl (G.old d))).trans (G.old_index d)
  low_index := appendMap_index Q j hj hA G.low G.low_index
  old_proper := G.old_proper
  low_height := grade_bound L Q j hj hA G.low_height hjk
  proper_exhaustive d hd := by
    obtain ⟨a, rfl⟩ := old_occurrence E Q j hj hA d (fun he => hd (by rw [CellScheme.scope, he]))
    obtain ⟨c, rfl⟩ := G.proper_exhaustive a (by simpa only [CellScheme.scope, cell_toCell, index] using hd)
    exact ⟨c, rfl⟩
  cut_exhaustive := appendMap_exhaustive Q j hj hA G.low G.cut_exhaustive
  cover d := by
    obtain ⟨x, rfl⟩ := (enumeration E Q j hj hA).surjective d
    rcases x with a | q
    · rcases G.cover a with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact Or.inl ⟨c, rfl⟩
      · exact Or.inr ⟨toCell L Q j hj hA (.inl c), appendMap_toCell Q j hj hA G.low _⟩
    · exact Or.inr ⟨toCell L Q j hj hA (.inr q), appendMap_toCell Q j hj hA G.low _⟩
  common c := toCell L Q j hj hA (.inl (G.common c))
  common_map c := (appendMap_toCell Q j hj hA G.low (.inl (G.common c))).trans
    (congrArg (fun d => toCell E Q j hj hA (.inl d)) (G.common_map c))

variable (G : GradeCutAssembly D L E k)

abbrev union : SemanticPatchUnion D L E where
  old := ⟨G.old, G.old_index, fun c d hd => G.proper_exhaustive d (fun h => G.old_proper c (h.trans hd.1))⟩
  low := ⟨G.low, G.low_index, fun c d hd => G.cut_exhaustive d (hd.2.trans (G.low_height c))⟩
  cover := G.cover

theorem common_index (c : Cell (GradeCutBoundary.scheme D k)) :
    L.cell (G.common c) = (GradeCutBoundary.scheme D k).cell c :=
  (G.low_index _).symm.trans ((congrArg E.cell (G.common_map c)).trans (G.old_index _))

/-- An overlap is necessarily the image of a cell in the original grade cut. -/
theorem overlap {a : Cell D} {b : Cell L} (h : G.old a = G.low b) :
    ∃ c, GradeCutBoundary.toCell D k c = a ∧ G.common c = b := by
  have hg : D.grade a = L.grade b := congrArg Prod.snd
    ((G.old_index a).symm.trans ((congrArg E.cell h).trans (G.low_index b)))
  obtain ⟨c, hc⟩ := GradeCutBoundary.exhaustive D k (hg.trans_le (G.low_height b))
  exact ⟨c, hc, G.low.injective ((G.common_map c).trans ((congrArg G.old hc).trans h))⟩

variable (sem : Semantics D) (low : Semantics L)

abbrev Compatible := ∀ (c : Cell (GradeCutBoundary.scheme D k))
    (d : (GradeCutBoundary.scheme D k).below ((GradeCutBoundary.scheme D k).cell c)),
    low.E (G.common c) ⟨G.common d.1, by rw [G.common_index, G.common_index]; exact d.2⟩ =
      (GradeCutBoundary.rows D k sem).E c d

theorem agreement (h : G.Compatible sem low) : G.union.Agreement sem low := by
  apply G.union.agreement_of_shared sem low (GradeCutBoundary.toCell D k) G.common
    (fun c => (G.common_map c).symm) (fun he => G.overlap he)
  · intro c d
    exact GradeCutBoundary.exhaustive D k (d.2.2.trans (GradeCutBoundary.grade_bound D k c))
  · exact fun c d hd => (h c ⟨d, hd⟩).symm

abbrev rows := G.union.rows sem low

variable {sem low}

theorem cut_respects_iff (h : G.Compatible sem low) (J : Finset ι × ℕ) (hJ : J.2 ≤ k)
    (p : L.below J → ExtOrd) : RespectsSemanticsBelow low J p ↔
    RespectsSemanticsBelow (G.rows sem low) J (p ∘
      (G.union.low.belowEquiv J (fun d hd => G.cut_exhaustive d (hd.2.trans hJ))).symm) :=
  G.union.low.respects_iff (G.union.low_row sem low (G.agreement sem low h)) J _ p

theorem paste_low {p : Cell D → ExtOrd} {q : Cell L → ExtOrd}
    (hag : ∀ c, q (G.common c) = p (GradeCutBoundary.toCell D k c)) (b : Cell L) :
    G.union.paste p q (G.low b) = q b :=
  G.union.paste_low (fun _ _ h => by obtain ⟨c, rfl, rfl⟩ := G.overlap h; exact (hag c).symm) b

/-- A labelling assembled from lawful labellings on both patches is lawful. -/
theorem respects (h : G.Compatible sem low) {p : Cell D → ExtOrd} {q : Cell L → ExtOrd}
    {r : Cell E → ExtOrd} (hp : RespectsSemantics sem p) (hq : RespectsSemantics low q)
    (hold : ∀ c, r (G.old c) = p c) (hlow : ∀ c, r (G.low c) = q c) :
    RespectsSemantics (G.rows sem low) r := by
  apply G.union.respects sem low (G.agreement sem low h)
  · simpa only [Function.comp_def, hold] using hp
  · simpa only [Function.comp_def, hlow] using hq

/-- The same patching argument is local: only the part of the old section below `J` is needed. -/
theorem paste_respectsBelow (h : G.Compatible sem low) {J : Finset ι × ℕ}
    {p : Cell D → ExtOrd} {q : Cell L → ExtOrd}
    (hp : RespectsSemanticsBelow sem J (fun d => p d.1)) (hq : RespectsSemantics low q)
    (hag : ∀ c, q (G.common c) = p (GradeCutBoundary.toCell D k c)) :
    RespectsSemanticsBelow (G.rows sem low) J (fun d => G.union.paste p q d.1) := by
  have hr (c : E.below J) : RespectsSemanticsBelow (G.rows sem low) (E.cell c.1)
      (fun d => G.union.paste p q d.1) := by
    obtain ⟨d, hd⟩ | ⟨d, hd⟩ := G.cover c.1
    · rw [← hd]
      exact (G.union.old.respects (G.union.old_row sem low) _ (G.union.old.closed d)
        (hp.mono (G.old_index d ▸ hd ▸ c.2)) (G.union.paste_old p q)).castIndex (G.old_index d).symm
    · rw [← hd]
      exact (G.union.low.respects (G.union.low_row sem low (G.agreement sem low h)) _
        (G.union.low.closed d) (hq.toBelow _) (G.paste_low hag)).castIndex (G.low_index d).symm
  constructor
  · intro c
    exact (hr c).orderly ⟨c.1, GradedLe.refl _⟩
  · intro c
    exact (hr c).locality ⟨c.1, GradedLe.refl _⟩
  · intro c t hs hg
    obtain ⟨w, hw, hb⟩ := (hr t).availability ⟨c.1, hs, hg.le⟩ ⟨t.1, GradedLe.refl _⟩ hs hg
    exact ⟨⟨w.1, w.2.trans t.2⟩, hw, hb⟩

theorem paste_respects (h : G.Compatible sem low) {p : Cell D → ExtOrd} {q : Cell L → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics low q)
    (hag : ∀ c, q (G.common c) = p (GradeCutBoundary.toCell D k c)) :
    RespectsSemantics (G.rows sem low) (G.union.paste p q) :=
  G.respects h hp hq (G.union.paste_old p q) (G.paste_low hag)

end

end GradeCutAssembly

end VaughtConjecture.Knight
