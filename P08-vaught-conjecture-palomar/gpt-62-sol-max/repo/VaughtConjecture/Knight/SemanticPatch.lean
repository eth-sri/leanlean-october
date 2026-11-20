/- Pasting literal semantic rows on covering, downward-closed occurrence images. -/
module

public import VaughtConjecture.Knight.CellBelowEquiv
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.CappedLifting

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {D : CellScheme A} {E : CellScheme B}

/-- An occurrence embedding that contains the entire domain of each of its rows. -/
structure SemanticPatch (D : CellScheme A) (E : CellScheme B) where
  map : Cell D ↪ Cell E
  index : ∀ c, E.cell (map c) = D.cell c
  closed : ∀ (c : Cell D) (d : Cell E), GradedLe (E.cell d) (D.cell c) → ∃ a, map a = d

namespace SemanticPatch

noncomputable section

variable (P : SemanticPatch D E)

abbrev belowEquiv (J : Finset ι × ℕ)
    (exhaustive : ∀ d, GradedLe (E.cell d) J → ∃ c, P.map c = d) : D.below J ≃ E.below J :=
  CellScheme.belowEquivOfIndex P.map P.map.injective P.index exhaustive

abbrev owner (c : Cell D) := P.belowEquiv (D.cell c) (P.closed c)

abbrev row (sem : Semantics D) (c : Cell D) (d : E.below (D.cell c)) := sem.E c ((P.owner c).symm d)

theorem row_orderly (sem : Semantics D) (c : Cell D) (d : E.below (D.cell c)) :
    SelfVis (E.grade d.1) (P.row sem c d) := by
  obtain ⟨a, rfl⟩ := (P.owner c).surjective d
  change SelfVis (E.grade (P.map a.1)) (sem.E c ((P.owner c).symm (P.owner c a)))
  rw [Equiv.symm_apply_apply, CellScheme.grade, P.index]
  exact (sem.orderly c a).symm

theorem row_congr (sem : Semantics D) {a b : Cell D} (h : a = b)
    {d : E.below (D.cell a)} {e : E.below (D.cell b)} (he : d.1 = e.1) :
    P.row sem a d = P.row sem b e := by
  subst b
  rw [Subtype.ext he]

theorem row_at (sem : Semantics D) (c : Cell D) (d : D.below (D.cell c))
    (e : E.below (D.cell c)) (h : P.map d.1 = e.1) : P.row sem c e = sem.E c d := by
  have he : P.owner c d = e := Subtype.ext h
  exact congrArg (sem.E c) (he ▸ (P.owner c).symm_apply_apply d)

/-- Literal equality of every row on the patch, including all lower arguments. -/
abbrev Preserves (sem : Semantics D) (rows : Semantics E) :=
  ∀ (c : Cell D) (d : D.below (D.cell c)),
    rows.E (P.map c) ⟨P.map d.1, by rw [P.index, P.index]; grind⟩ = sem.E c d

theorem respects_iff {sem : Semantics D} {rows : Semantics E} (hrows : P.Preserves sem rows)
    (J : Finset ι × ℕ) (hJ : ∀ d, GradedLe (E.cell d) J → ∃ c, P.map c = d)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔ RespectsSemanticsBelow rows J (p ∘ (P.belowEquiv J hJ).symm) :=
  respects_iff_of_index_equiv (P.belowEquiv J hJ) (fun d => P.index d.1)
    (fun c d _ => (hrows c.1 d).symm) p

/-- Transport a whole section to any exhaustive lower domain of the patch. -/
theorem respects {sem : Semantics D} {rows : Semantics E} (hrows : P.Preserves sem rows)
    (J : Finset ι × ℕ) (hJ : ∀ d, GradedLe (E.cell d) J → ∃ c, P.map c = d)
    {p : Cell D → ExtOrd} {r : Cell E → ExtOrd}
    (hp : RespectsSemanticsBelow sem J (fun d => p d.1)) (hr : ∀ c, r (P.map c) = p c) :
    RespectsSemanticsBelow rows J (fun d => r d.1) := by
  convert (P.respects_iff hrows J hJ _).mp hp using 1
  funext d
  obtain ⟨a, rfl⟩ := (P.belowEquiv J hJ).surjective d
  aesop

theorem _root_.VaughtConjecture.Knight.RespectsSemanticsBelow.castIndex {sem : Semantics E}
    {I J : Finset ι × ℕ} (h : I = J) {p : E.below I → ExtOrd}
    (hp : RespectsSemanticsBelow sem I p) :
    RespectsSemanticsBelow sem J (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := by aesop

theorem lift {sem : Semantics D} {rows : Semantics E} (hrows : P.Preserves sem rows)
    {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ∀ d, GradedLe (E.cell d) J → ∃ c, P.map c = d)
    (hl : CappedLift sem h) : CappedLift rows h :=
  CappedLift.of_equiv (P.belowEquiv I fun d hd => hJ d (hd.trans h)) (P.belowEquiv J hJ)
    (fun _ => rfl) le_rfl (P.respects_iff hrows I fun d hd => hJ d (hd.trans h))
    (P.respects_iff hrows J hJ) hl

def ownerEquiv (c : Cell D) : D.below (D.cell c) ≃ E.below (E.cell (P.map c)) :=
  CellScheme.belowEquivOfMap P.map P.map.injective (fun d => by rw [P.index, P.index])
    (fun d hd => P.closed c d (P.index c ▸ hd))

theorem owner_respects_iff {sem : Semantics D} {rows : Semantics E} (hrows : P.Preserves sem rows)
    (c : Cell D) (q : E.below (E.cell (P.map c)) → ExtOrd) :
    RespectsSemanticsBelow rows _ q ↔ RespectsSemanticsBelow sem _ (q ∘ P.ownerEquiv c) :=
  iff_comp_symm (P.ownerEquiv c).symm
    (respects_iff_of_index_equiv (P.ownerEquiv c) (fun d => P.index d.1)
      (fun x d _ => (hrows x.1 d).symm)) q

theorem consistent_at {sem : Semantics D} {rows : Semantics E} (hrows : P.Preserves sem rows)
    (hs : sem.IsConsistent) (c : Cell D) :
    RespectsSemanticsBelow rows (E.cell (P.map c)) (rows.E (P.map c)) := by
  apply (P.owner_respects_iff hrows c _).mpr
  convert hs c using 1
  funext d
  exact hrows c d

end

end SemanticPatch

/-- A pair of downward-closed occurrence images covering the carrier. -/
structure SemanticPatchUnion (D : CellScheme A) (L : CellScheme B) (E : CellScheme C) where
  old : SemanticPatch D E
  low : SemanticPatch L E
  cover : ∀ d, (∃ a, old.map a = d) ∨ (∃ b, low.map b = d)

namespace SemanticPatchUnion

variable {L : CellScheme C}

noncomputable section

variable (U : SemanticPatchUnion D L E)

open Classical in
/-- The first patch takes priority on the overlap. -/
def paste {α : Sort*} (p : Cell D → α) (q : Cell L → α) (c : Cell E) : α :=
  if h : ∃ a, U.old.map a = c then p h.choose else q ((U.cover c).resolve_left h).choose

theorem paste_old {α : Sort*} (p : Cell D → α) (q : Cell L → α) (a : Cell D) :
    U.paste p q (U.old.map a) = p a := by
  have h : ∃ c, U.old.map c = U.old.map a := ⟨a, rfl⟩
  rw [paste, dif_pos h, U.old.map.injective h.choose_spec]

theorem paste_low {α : Sort*} {p : Cell D → α} {q : Cell L → α}
    (h : ∀ a b, U.old.map a = U.low.map b → p a = q b) (b : Cell L) :
    U.paste p q (U.low.map b) = q b := by
  unfold paste
  split
  · rename_i ha
    exact h _ _ ha.choose_spec
  · rename_i ha
    exact congrArg q (U.low.map.injective ((U.cover _).resolve_left ha).choose_spec)

theorem paste_pred {α : Sort*} {P : α → Prop} {p : Cell D → α} {q : Cell L → α}
    (hp : ∀ a, P (p a)) (hq : ∀ b, P (q b)) (d : Cell E) : P (U.paste p q d) := by
  unfold paste
  split
  · exact hp _
  · exact hq _

theorem paste_rel {α β : Sort*} {R : α → β → Prop} {p : Cell D → α} {q : Cell L → α}
    {p' : Cell D → β} {q' : Cell L → β} (hp : ∀ a, R (p a) (p' a)) (hq : ∀ b, R (q b) (q' b))
    (d : Cell E) : R (U.paste p q d) (U.paste p' q' d) := by
  classical
  by_cases h : ∃ a, U.old.map a = d
  · simpa only [paste, dif_pos h] using hp h.choose
  · simpa only [paste, dif_neg h] using hq ((U.cover d).resolve_left h).choose

variable (sem : Semantics D) (low : Semantics L)

open Classical in
def rows : Semantics E where
  E c d := if h : ∃ a, U.old.map a = c then
    U.old.row sem h.choose ⟨d.1, by rw [← U.old.index, h.choose_spec]; grind⟩
    else
      let h' := (U.cover c).resolve_left h
      U.low.row low h'.choose ⟨d.1, by rw [← U.low.index, h'.choose_spec]; grind⟩
  orderly c d := by
    split
    · exact (U.old.row_orderly sem _ _).symm
    · exact (U.low.row_orderly low _ _).symm

theorem old_row : U.old.Preserves sem (U.rows sem low) := by
  intro c d
  have h : ∃ a, U.old.map a = U.old.map c := ⟨c, rfl⟩
  have he := U.old.map.injective h.choose_spec
  simp only [rows, dif_pos h]
  exact (U.old.row_congr sem he (e := U.old.owner c d) rfl).trans
    (congrArg (sem.E c) ((U.old.owner c).symm_apply_apply d))

abbrev Agreement := ∀ (a : Cell D) (b : Cell L) (h : U.old.map a = U.low.map b)
    (d : E.below (D.cell a)), U.old.row sem a d =
      U.low.row low b ⟨d.1, by rw [← U.low.index, ← h, U.old.index]; grind⟩

/-- Agreement can be checked on representatives of the common downward-closed boundary. -/
theorem agreement_of_shared {α : Type*} (f : α → Cell D) (g : α → Cell L)
    (shared : ∀ i, U.old.map (f i) = U.low.map (g i))
    (overlap : ∀ {a b}, U.old.map a = U.low.map b → ∃ i, f i = a ∧ g i = b)
    (closed : ∀ i (d : D.below (D.cell (f i))), ∃ j, f j = d.1)
    (compatible : ∀ i j (h : GradedLe (D.cell (f j)) (D.cell (f i))),
      sem.E (f i) ⟨f j, h⟩ = low.E (g i) ⟨g j, by
        rw [← U.low.index, ← U.low.index, ← shared, ← shared, U.old.index, U.old.index]
        exact h⟩) : U.Agreement sem low := by
  intro a b hab d
  obtain ⟨i, rfl, rfl⟩ := overlap hab
  obtain ⟨e, he⟩ := (U.old.owner (f i)).surjective d
  obtain ⟨j, hj⟩ := closed i e
  have hd : GradedLe (D.cell (f j)) (D.cell (f i)) := hj ▸ e.2
  have hm : U.old.map (f j) = d.1 := (congrArg U.old.map hj).trans (congrArg Subtype.val he)
  have hg : GradedLe (L.cell (g j)) (L.cell (g i)) := by
    rw [← U.low.index, ← U.low.index, ← shared, ← shared, U.old.index, U.old.index]
    exact hd
  exact (U.old.row_at sem _ ⟨f j, hd⟩ _ hm).trans
    ((compatible i j hd).trans (U.low.row_at low _ ⟨g j, hg⟩ _ ((shared j).symm.trans hm)).symm)

theorem low_row (h : U.Agreement sem low) : U.low.Preserves low (U.rows sem low) := by
  intro c d
  simp only [rows]
  split
  · rename_i he
    exact (h _ c he.choose_spec _).trans (congrArg (low.E c) ((U.low.owner c).symm_apply_apply d))
  · rename_i he
    have hc := U.low.map.injective ((U.cover _).resolve_left he).choose_spec
    exact (U.low.row_congr low hc (e := U.low.owner c d) rfl).trans
      (congrArg (low.E c) ((U.low.owner c).symm_apply_apply d))

theorem coded (hs : sem.IsCoded) (hl : low.IsCoded) : (U.rows sem low).IsCoded := by
  intro c d
  simp only [rows]
  split
  · rename_i h
    have hg : E.grade c = D.grade h.choose := congrArg Prod.snd
      ((congrArg E.cell h.choose_spec).symm.trans (U.old.index h.choose))
    rw [hg]
    exact hs _ _
  · rename_i h
    let h' := (U.cover c).resolve_left h
    have hg : E.grade c = L.grade h'.choose := congrArg Prod.snd
      ((congrArg E.cell h'.choose_spec).symm.trans (U.low.index h'.choose))
    rw [hg]
    exact hl _ _

theorem consistent (h : U.Agreement sem low) (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (U.rows sem low).IsConsistent := by
  intro c
  rcases U.cover c with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact U.old.consistent_at (U.old_row sem low) hs a
  · exact U.low.consistent_at (U.low_row sem low h) hl b

/-- Lawfulness on both patches suffices: every owner's whole lower domain is retained. -/
theorem respects (h : U.Agreement sem low) {p : Cell E → ExtOrd}
    (hp : RespectsSemantics sem (p ∘ U.old.map)) (hq : RespectsSemantics low (p ∘ U.low.map)) :
    RespectsSemantics (U.rows sem low) p := by
  apply RespectsSemantics.of_local
  intro c
  rcases U.cover c with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact (U.old.owner_respects_iff (U.old_row sem low) a _).mpr (hp.toBelow _)
  · exact (U.low.owner_respects_iff (U.low_row sem low h) b _).mpr (hq.toBelow _)

end

end SemanticPatchUnion

end VaughtConjecture.Knight
