/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Order.WithBot

@[expose] public section

namespace VaughtConjecture.Knight

/-- The extended ordinal line `{-∞} ∪ Ordinal ∪ {∞}` of labels (Knight, Def. 2.2.1):
`⊥` is the bottom label `-∞`, `⊤` is the top label `∞`, and `ExtOrd.ofOrd α` is the ordinal
`α`.  Fixed at `Ordinal.{0}` (see the module docstring). -/
abbrev ExtOrd : Type 1 := WithBot (WithTop Ordinal.{0})

namespace ExtOrd

/-- Embed an ordinal into the extended ordinal line as an ordinal label. -/
def ofOrd (α : Ordinal.{0}) : ExtOrd := ((α : WithTop Ordinal.{0}) : ExtOrd)

@[simp] theorem ofOrd_ne_bot (α : Ordinal.{0}) : ofOrd α ≠ (⊥ : ExtOrd) :=
  WithBot.coe_ne_bot

@[simp] theorem ofOrd_ne_top (α : Ordinal.{0}) : ofOrd α ≠ (⊤ : ExtOrd) :=
  fun h => WithTop.coe_ne_top (WithBot.coe_injective h)

@[simp] theorem ofOrd_inj {α β : Ordinal.{0}} : ofOrd α = ofOrd β ↔ α = β := by
  simp [ofOrd]

@[simp] theorem ofOrd_le_ofOrd {α β : Ordinal.{0}} : ofOrd α ≤ ofOrd β ↔ α ≤ β := by
  simp [ofOrd]

@[simp] theorem ofOrd_lt_ofOrd {α β : Ordinal.{0}} : ofOrd α < ofOrd β ↔ α < β := by
  simp [ofOrd]

@[simp] theorem bot_lt_ofOrd (α : Ordinal.{0}) : (⊥ : ExtOrd) < ofOrd α :=
  WithBot.bot_lt_coe _

@[simp] theorem ofOrd_lt_top (α : Ordinal.{0}) : ofOrd α < (⊤ : ExtOrd) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top α)

@[simp] theorem not_ofOrd_le_bot (α : Ordinal.{0}) : ¬ ofOrd α ≤ (⊥ : ExtOrd) :=
  not_le_of_gt (bot_lt_ofOrd α)

/-- Every label is the bottom label, the top label, or an ordinal label. -/
theorem cases (x : ExtOrd) : x = ⊥ ∨ x = ⊤ ∨ ∃ α : Ordinal.{0}, x = ofOrd α := by
  induction x using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => simp_all
    | coe α => tauto

/-- For a map of the extended line, check monotonicity on ordinals and at the endpoints. -/
theorem monotone_ofOrd {Y : Type*} [Preorder Y] {f : ExtOrd → Y}
    (hbot : ∀ x, f ⊥ ≤ f x) (htop : ∀ x, f x ≤ f ⊤)
    (hord : Monotone (f ∘ ofOrd)) : Monotone f := by
  intro x y h
  rcases cases x with rfl | rfl | ⟨a, rfl⟩
  · exact hbot _
  · rw [top_le_iff.mp h]
  · rcases cases y with rfl | rfl | ⟨b, rfl⟩
    · exact (not_ofOrd_le_bot a h).elim
    · exact htop _
    · exact hord (ofOrd_le_ofOrd.mp h)

end ExtOrd

namespace Value

open Ordinal ExtOrd

/-- The limit part `μ` in the decomposition `α = μ + n` (`n < ω`), defined as `ω * (α / ω)`
by the ordinal division algorithm. -/
noncomputable def limitPart (α : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * (α / Ordinal.omega0)

/-- The finite part `n` in the decomposition `α = μ + n`, the natural number `α % ω`. -/
noncomputable def finitePart (α : Ordinal.{0}) : ℕ :=
  (Ordinal.lt_omega0.mp (Ordinal.mod_lt α Ordinal.omega0_ne_zero)).choose

/-- The residue `α % ω` is the finite part, as an ordinal. -/
theorem finitePart_spec (α : Ordinal.{0}) :
    (α % Ordinal.omega0 : Ordinal) = ↑(finitePart α) :=
  (Ordinal.lt_omega0.mp (Ordinal.mod_lt α Ordinal.omega0_ne_zero)).choose_spec

theorem finitePart_natCast (n : ℕ) : finitePart (n : Ordinal.{0}) = n := by
  have h := finitePart_spec (n : Ordinal.{0})
  rw [Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 n)] at h
  exact_mod_cast h.symm

/-- The fundamental decomposition `α = limitPart α + finitePart α`. -/
theorem decomposition (α : Ordinal.{0}) : limitPart α + ↑(finitePart α) = α := by
  rw [limitPart, ← finitePart_spec]
  apply Ordinal.div_add_mod

/-- `limitPart` is monotone. -/
theorem limitPart_mono {γ δ : Ordinal.{0}} (h : γ ≤ δ) : limitPart γ ≤ limitPart δ :=
  mul_le_mul_right (Ordinal.div_le_left h _) _

/-- `limitPart δ ≤ δ`. -/
theorem limitPart_le (δ : Ordinal.{0}) : limitPart δ ≤ δ :=
  Ordinal.mul_div_le δ Ordinal.omega0

/-- A limit ordinal `α ≤ δ` lies below the limit part of `δ`: `α = ω * k` for some `k`, and
`ω * k ≤ δ` forces `k ≤ δ / ω`. -/
theorem succLimit_le_limitPart {α δ : Ordinal.{0}}
    (hα : Order.IsSuccLimit α) (h : α ≤ δ) :
    α ≤ limitPart δ := by
  unfold limitPart
  obtain ⟨k, rfl⟩ : Ordinal.omega0 ∣ α :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hα.isSuccPrelimit
  exact mul_le_mul_right ((Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp h) Ordinal.omega0

/-- The finite part of `limitPart ξ + i` is `i`: `(ω * q + i) % ω = i % ω = i`. -/
theorem finitePart_limitPart_add_nat (ξ : Ordinal.{0}) (i : ℕ) :
    finitePart (limitPart ξ + i) = i := by
  have h := finitePart_spec (limitPart ξ + i)
  rw [limitPart, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 i)] at h
  exact_mod_cast h.symm

/-- The limit part of `limitPart ξ + i` is `limitPart ξ`: `(ω * q + i) / ω = q + i / ω = q`. -/
theorem limitPart_limitPart_add_nat (ξ : Ordinal.{0}) (i : ℕ) :
    limitPart (limitPart ξ + i) = limitPart ξ := by
  have h := decomposition (limitPart ξ + i)
  rw [finitePart_limitPart_add_nat] at h
  exact (Ordinal.add_right_cancel i).mp h

/-- Replace the finite part of `α` by `m` (Knight, Def. 2.2.2). -/
noncomputable def ordinalReplace (α : Ordinal.{0}) (m : ℕ) : Ordinal.{0} :=
  limitPart α + m

/-- Visibility replacement (Knight, Def. 2.2.3): if the finite part of `α` is below the
visibility threshold `K`, replace it by `m`; otherwise leave `α` unchanged. -/
noncomputable def visibilityReplace (α : Ordinal.{0}) (K m : ℕ) : Ordinal.{0} :=
  if finitePart α < K then ordinalReplace α m else α

/-- Visibility replacement on labels (Knight, Def. 2.2.1 together with Def. 2.2.3): the
bottom and top labels are fixed, and an ordinal label is replaced by `visibilityReplace`. -/
noncomputable def extVisibilityReplace (γ : ExtOrd) (K m : ℕ) : ExtOrd :=
  match γ with
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some α) => ExtOrd.ofOrd (visibilityReplace α K m)

@[simp] theorem extVisibilityReplace_bot (K m : ℕ) :
    extVisibilityReplace ⊥ K m = ⊥ := rfl

@[simp] theorem extVisibilityReplace_top (K m : ℕ) :
    extVisibilityReplace ⊤ K m = ⊤ := rfl

@[simp] theorem extVisibilityReplace_ofOrd (α : Ordinal.{0}) (K m : ℕ) :
    extVisibilityReplace (ofOrd α) K m = ofOrd (visibilityReplace α K m) := rfl

/-- `visibilityReplace α K K = α` iff `K ≤ finitePart α`, i.e. iff the visibility threshold
does not trigger.  (If it triggers, the finite part becomes `K ≠ finitePart α`, and ordinal
addition cancels on the left.) -/
theorem visibilityReplace_self_iff (α : Ordinal.{0}) (K : ℕ) :
    visibilityReplace α K K = α ↔ K ≤ finitePart α := by
  unfold visibilityReplace
  split_ifs with hlt
  · refine ⟨fun h => ?_, by lia⟩
    exfalso
    have key : limitPart α + ↑K = limitPart α + ↑(finitePart α) :=
      h.trans (decomposition α).symm
    simp_all
  simp_all

/-- Self-visibility (Knight, Lemma 2.2.4): a label `γ` satisfies `γ = γ ⊔⁺_K K` iff it is the
bottom label, the top label, or an ordinal whose finite part is at least `K`.

Knight-VC's original skeleton stated the ordinal case as `finitePart α = K`
(`IsKTimesSucc`); the correct characterisation is `K ≤ finitePart α`: for `K ≤ finitePart α`
the replacement is a no-op, and for `finitePart α < K` it changes the finite part to `K`,
which never gives back `α` (left cancellation of ordinal addition).  Knight-VC's name was
`lemma_2_2_4`. -/
theorem extVisibilityReplace_self_iff (γ : ExtOrd) (K : ℕ) :
    extVisibilityReplace γ K K = γ ↔
      (γ = (⊥ : ExtOrd) ∨ γ = (⊤ : ExtOrd) ∨
        ∃ α : Ordinal.{0}, γ = ofOrd α ∧ K ≤ finitePart α) := by
  rcases ExtOrd.cases γ with rfl | rfl | ⟨α, rfl⟩
  · simp
  · simp
  · simp [visibilityReplace_self_iff]

/-- Self-visibility at threshold `k` implies self-visibility at every `k' ≤ k`. -/
theorem extVisReplace_self_of_le {v : ExtOrd} {k k' : ℕ}
    (h : extVisibilityReplace v k k = v) (hle : k' ≤ k) :
    extVisibilityReplace v k' k' = v := by grind [extVisibilityReplace_self_iff]

/-- For a limit ordinal `α`, visibility replacement of an ordinal `≥ α` stays `≥ α`:
`limitPart δ ≥ α`, so `ordinalReplace δ i = limitPart δ + i ≥ α`. -/
theorem visReplace_ge_of_ge_limit {α : Ordinal.{0}}
    (hα : Order.IsSuccLimit α)
    {δ : Ordinal.{0}} (hδ : α ≤ δ) (k i : ℕ) :
    α ≤ visibilityReplace δ k i := by
  unfold visibilityReplace
  split_ifs with hfp
  · exact le_trans (succLimit_le_limitPart hα hδ) le_self_add
  assumption

/-- For a limit ordinal `α`, visibility replacement of an ordinal `< α` stays `< α`
(`β < α → β + 1 < α`, iterated finitely often). -/
theorem visReplace_lt_of_lt_limit {α : Ordinal.{0}}
    (hα : Order.IsSuccLimit α)
    {δ : Ordinal.{0}} (hδ : δ < α) (k i : ℕ) :
    visibilityReplace δ k i < α := by
  unfold visibilityReplace
  split_ifs with hfp
  · unfold ordinalReplace
    have hlp_lt : limitPart δ < α := lt_of_le_of_lt (limitPart_le δ) hδ
    induction i with
    | zero => simpa using hlp_lt
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact hα.succ_lt ih
  assumption

/-- For a limit ordinal `α`, visibility replacement on labels preserves `ofOrd α ≤ ·`
(`visReplace_ge_of_ge_limit` on ordinal labels; `⊤` is fixed). -/
theorem extVisReplace_ge_of_ge_limit {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {x : ExtOrd} (hx : ofOrd α ≤ x) (k i : ℕ) :
    ofOrd α ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · assumption
  · assumption
  simp_all [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, visReplace_ge_of_ge_limit]

/-- For a limit ordinal `α`, visibility replacement on labels preserves `· < ofOrd α`
(`visReplace_lt_of_lt_limit` on ordinal labels; `⊥` is fixed). -/
theorem extVisReplace_lt_of_lt_limit {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {x : ExtOrd} (hx : x < ofOrd α) (k i : ℕ) :
    extVisibilityReplace x k i < ofOrd α := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · assumption
  · assumption
  simp_all [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd, visReplace_lt_of_lt_limit]

/-- Visibility replacement stays `≤ δ` when `γ ≤ δ`, `δ` is self-visible at `k`, and the
replacement value is `≤ k`. -/
theorem visReplace_le_of_le_selfVis {γ δ : Ordinal.{0}} {k i : ℕ}
    (hγδ : γ ≤ δ) (hδ_sv : k ≤ finitePart δ) (hi : i ≤ k) :
    visibilityReplace γ k i ≤ δ := by
  unfold visibilityReplace
  split_ifs with h
  · unfold ordinalReplace
    have hi' : (i : Ordinal) ≤ (k : Ordinal) := by exact_mod_cast hi
    have hk' : (k : Ordinal) ≤ (finitePart δ : Ordinal) := by exact_mod_cast hδ_sv
    calc limitPart γ + (i : Ordinal)
        ≤ limitPart δ + (k : Ordinal) := add_le_add (limitPart_mono hγδ) hi'
      _ ≤ limitPart δ + (finitePart δ : Ordinal) := add_le_add_right hk' (limitPart δ)
      _ = δ := decomposition δ
  assumption

/-- Vertical truncation of a label at stage `α` (the pointwise content of Knight's reduction
map, Def. 3.1.2, on a single cell): ordinal labels `≥ α` become the top label `⊤`; ordinal
labels `< α`, and `⊥`, `⊤`, are kept.  This is the **strict** truncation (decision #84): the
boundary label `ofOrd α` is sent to `⊤`, so the labels of a stage-`α` type are `< ofOrd α` or
`⊤` (`truncExt_bound`), and truncation commutes with visibility replacement at every limit
stage without a boundary side condition (`truncExt_evr_comm`); Knight-VC's non-strict variant
(`β ≤ α` kept) fails there. -/
noncomputable def truncExt (α : Ordinal.{0}) (γ : ExtOrd) : ExtOrd :=
  match γ with
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some β) => if β < α then ExtOrd.ofOrd β else ⊤

@[simp] theorem truncExt_bot (α : Ordinal.{0}) : truncExt α ⊥ = ⊥ := rfl

@[simp] theorem truncExt_top (α : Ordinal.{0}) : truncExt α ⊤ = ⊤ := rfl

theorem truncExt_ofOrd (α β : Ordinal.{0}) :
    truncExt α (ofOrd β) = if β < α then ofOrd β else ⊤ := rfl

@[simp] theorem truncExt_ofOrd_of_lt {α β : Ordinal.{0}} (h : β < α) :
    truncExt α (ofOrd β) = ofOrd β := by
  rw [truncExt_ofOrd, ite_eq_left h]

@[simp] theorem truncExt_ofOrd_of_le {α β : Ordinal.{0}} (h : α ≤ β) :
    truncExt α (ofOrd β) = ⊤ := by
  rw [truncExt_ofOrd, ite_eq_right (not_lt_of_ge h)]

theorem truncExt_eq_ite (α : Ordinal.{0}) (x : ExtOrd) :
    truncExt α x = if x < ofOrd α then x else ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩ <;> simp [truncExt_ofOrd]

theorem truncExt_bound (α : Ordinal.{0}) (x : ExtOrd) :
    truncExt α x < ofOrd α ∨ truncExt α x = ⊤ := by
  rw [truncExt_eq_ite]; split_ifs <;> tauto

theorem truncExt_id_of_lt {α : Ordinal.{0}} {x : ExtOrd} (hx : x < ofOrd α) :
    truncExt α x = x := by rw [truncExt_eq_ite, if_pos hx]

theorem truncExt_id_of_bound {α : Ordinal.{0}} {x : ExtOrd}
    (h : x < ofOrd α ∨ x = ⊤) : truncExt α x = x := by
  rcases h with h | rfl
  · exact truncExt_id_of_lt h
  · rfl

theorem truncExt_eq_top_of_ge {α : Ordinal.{0}} {x : ExtOrd} (hx : ofOrd α ≤ x) :
    truncExt α x = ⊤ := by rw [truncExt_eq_ite, if_neg hx.not_gt]

theorem truncExt_eq_top_iff {α : Ordinal.{0}} {x : ExtOrd} :
    truncExt α x = ⊤ ↔ ofOrd α ≤ x := by
  rw [truncExt_eq_ite]
  split_ifs with h
  · exact iff_of_false (ne_top_of_lt h) h.not_ge
  · simp [le_of_not_gt h]

theorem truncExt_le_self (α : Ordinal.{0}) (x : ExtOrd) : x ≤ truncExt α x := by
  rw [truncExt_eq_ite]; split_ifs <;> simp

theorem truncExt_mono (α : Ordinal.{0}) : Monotone (truncExt α) := by
  intro x y hxy
  by_cases hy : y < ofOrd α
  · rwa [truncExt_id_of_lt hy, truncExt_id_of_lt (hxy.trans_lt hy)]
  · rw [truncExt_eq_top_of_ge (le_of_not_gt hy)]
    exact le_top

theorem truncExt_lt_iff {α : Ordinal.{0}} {x y : ExtOrd} (hy : y ≤ ofOrd α) :
    truncExt α x < y ↔ x < y :=
  ⟨(truncExt_le_self _ _).trans_lt, fun h => (truncExt_id_of_lt (h.trans_le hy)).symm ▸ h⟩

theorem lt_truncExt_iff {α : Ordinal.{0}} {x y : ExtOrd} (hy : y < ofOrd α) :
    y < truncExt α x ↔ y < x := by
  rw [truncExt_eq_ite]
  split_ifs with hx
  · rfl
  · simp [hy.trans_le (le_of_not_gt hx), hy.trans_le le_top]

theorem truncExt_preserves_selfVis (α : Ordinal.{0}) (x : ExtOrd) (K : ℕ)
    (h : extVisibilityReplace x K K = x) :
    extVisibilityReplace (truncExt α x) K K = truncExt α x := by
  rw [truncExt_eq_ite]; split_ifs <;> simp_all

theorem truncExt_min (α : Ordinal.{0}) (x y : ExtOrd) :
    truncExt α (min x y) = min (truncExt α x) (truncExt α y) :=
  (truncExt_mono α).map_min

theorem truncExt_compose {γ α : Ordinal.{0}} (hle : γ ≤ α) (x : ExtOrd) :
    truncExt γ (truncExt α x) = truncExt γ x := by
  rw [truncExt_eq_ite α x]
  split_ifs with hx
  · rfl
  · rw [truncExt_top, truncExt_eq_top_of_ge ((ofOrd_le_ofOrd.mpr hle).trans (le_of_not_gt hx))]

theorem truncExt_eq_bot_iff {α : Ordinal.{0}} {x : ExtOrd} :
    truncExt α x = ⊥ ↔ x = ⊥ := by grind [truncExt_eq_ite, bot_lt_ofOrd]

/-- Truncation commutes with visibility replacement at every limit stage `α`, for every label
and every threshold and replacement value (Knight, Def. 2.3.9(5) for the reduction map):
`truncExt α (evr x k i) = evr (truncExt α x) k i`.  For an ordinal label `δ < α` the
replacement stays `< α` (`visReplace_lt_of_lt_limit`) and both sides are the replacement; for
`δ ≥ α` it stays `≥ α` (`visReplace_ge_of_ge_limit`) and both sides are `⊤`.  (With
Knight-VC's non-strict truncation `T`, keeping `ofOrd α`, this fails at the boundary label,
e.g. `α = ω`, `k = i = 1`: `T ω (evr (ofOrd ω) 1 1) = ⊤` but
`evr (T ω (ofOrd ω)) 1 1 = ofOrd (ω + 1)`; that was the reason for decision #84.) -/
theorem truncExt_evr_comm {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (x : ExtOrd) (k i : ℕ) :
    truncExt α (extVisibilityReplace x k i) =
    extVisibilityReplace (truncExt α x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · rfl
  · rfl
  · rcases lt_or_ge δ α with hδ | hδ
    · simp_all [truncExt_ofOrd_of_lt, extVisibilityReplace_ofOrd, visReplace_lt_of_lt_limit]
    grind [truncExt_ofOrd_of_le, extVisibilityReplace_ofOrd, visReplace_ge_of_ge_limit, extVisibilityReplace_top]

/-- A non-successor ordinal: zero or a limit.  Knight's Def. 3.2.1(4)(b) quantifies over
"non-successor `γ` with `0 ≤ γ < α`", which includes `γ = 0`, excluded by Mathlib's
`Order.IsSuccLimit` (`Ordinal.not_isSuccLimit_zero`). -/
def IsNonSuccessor (γ : Ordinal.{0}) : Prop := γ = 0 ∨ Order.IsSuccLimit γ

/-- The canonical block levels `ω + ω * ξ` (the ω-blocks of `docs/TERMINOLOGY.md`): block `ξ`
is the step from `blockLevel ξ` to `blockLevel (ξ + 1) = blockLevel ξ + ω`. -/
noncomputable def blockLevel (ξ : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 + Ordinal.omega0 * ξ

theorem blockLevel_succ (ξ : Ordinal.{0}) :
    blockLevel (Order.succ ξ) = blockLevel ξ + Ordinal.omega0 := by
  unfold blockLevel
  rw [Ordinal.mul_succ, add_assoc]

theorem blockLevel_strictMono : StrictMono blockLevel := by
  intro ξ η h
  unfold blockLevel
  simp_all

@[simp] theorem blockLevel_zero : blockLevel 0 = Ordinal.omega0 := by
  simp [blockLevel]

/-- Every canonical block level is a limit ordinal. -/
theorem isSuccLimit_blockLevel (ξ : Ordinal.{0}) : Order.IsSuccLimit (blockLevel ξ) := by
  unfold blockLevel
  rw [Ordinal.isSuccLimit_iff, Ordinal.isSuccPrelimit_iff_omega0_dvd]
  exact ⟨(Ordinal.omega0_pos.trans_le le_self_add).ne',
    (Ordinal.dvd_add_iff dvd_rfl).mpr (dvd_mul_right _ _)⟩

end Value

namespace ExtOrd

open Value

/-- Values bounded at a stage are determined by any nonempty cofinal set of reads. -/
theorem eq_of_forall_truncExt_eq {I : Type*} [Nonempty I] {x y : ExtOrd}
    {δ : Ordinal.{0}} {c : I → Ordinal.{0}} (hcof : ∀ γ < δ, ∃ i, γ < c i)
    (hx : x < ofOrd δ ∨ x = ⊤) (hy : y < ofOrd δ ∨ y = ⊤)
    (h : ∀ i, truncExt (c i) x = truncExt (c i) y) : x = y := by
  have bound {a b : ExtOrd} (ha : a < ofOrd δ ∨ a = ⊤)
      (hab : ∀ i, truncExt (c i) a = truncExt (c i) b) : b ≤ a := by
    rcases ha with ha | rfl
    · obtain ⟨i, hi⟩ : ∃ i, a < ofOrd (c i) := by
        rcases cases a with rfl | rfl | ⟨γ, rfl⟩ <;> simp_all
      exact (truncExt_le_self _ _).trans_eq ((hab i).symm.trans (truncExt_id_of_lt hi))
    · exact le_top
  exact le_antisymm (bound hy fun i => (h i).symm) (bound hx h)

end ExtOrd

end VaughtConjecture.Knight
