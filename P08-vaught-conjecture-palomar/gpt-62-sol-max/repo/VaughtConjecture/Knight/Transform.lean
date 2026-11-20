/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.MinMax
public import VaughtConjecture.Knight.VisibilityBandArithmetic

@[expose] public section

namespace VaughtConjecture.Knight

namespace Transform

open Value ExtOrd

section

variable {D : Type*} (grade : D → ℕ)

/-- Orderliness (Knight, Def. 2.3.4): each label of `p` is self-visible at the grade of its
cell, `p d = extVisibilityReplace (p d) (grade d) (grade d)`. -/
def IsOrderly (p : D → ExtOrd) : Prop :=
  ∀ d : D, p d = extVisibilityReplace (p d) (grade d) (grade d)

/-- The transformation relation `p ⇒ q` (Knight, Def. 2.3.9, verbatim): there are a
suppressor `g : ℕ → ExtOrd` and a shifter `σ : ExtOrd → ExtOrd` with

1. `g` antitone: `n < m → g m ≤ g n`;
2. `g` self-visible: `g n = g n ⊔⁺_n n`;
3. `σ ⊥ = ⊥`;
4. `σ` monotone;
5. for all `α` and `k` with `σ α ≤ g k` and all `i ≤ k`, `σ (α ⊔⁺_k i) = σ α ⊔⁺_k i`;

such that `q d = min (σ (p d)) (g (grade d))` for every cell `d`.  (No inflationarity of `σ`
and no guard on clause 5, unlike Knight-VC's relation; see the module docstring.) -/
def TransformsTo (p q : D → ExtOrd) : Prop :=
  ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
    (∀ n m : ℕ, n < m → g m ≤ g n) ∧
    (∀ n : ℕ, g n = extVisibilityReplace (g n) n n) ∧
    (σ (⊥ : ExtOrd) = ⊥) ∧
    Monotone σ ∧
    (∀ (α : ExtOrd) (k : ℕ),
        σ α ≤ g k →
        ∀ i : ℕ, i ≤ k →
          σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i) ∧
    (∀ d : D, q d = min (σ (p d)) (g (grade d)))

end

variable {D : Type*} {grade : D → ℕ}

/-- Reflexivity: every labelling transforms to itself, with witnesses `σ = id` and `g = ⊤`
(clause 5 holds for `id` trivially). -/
theorem TransformsTo.refl (p : D → ExtOrd) : TransformsTo grade p p :=
  ⟨fun _ => ⊤, id,
    fun _ _ _ => le_refl ⊤,
    fun _ => rfl,
    rfl,
    monotone_id,
    fun _ _ _ _ _ => rfl,
    by simp⟩

/-- Reindexing: a transformation on cells `D` pulls back along any map `φ : D' → D` of cell
families (same witnesses `g`, `σ`; used to transport locality along face restriction). -/
theorem TransformsTo.reindex {D' : Type*} {p q : D → ExtOrd} (h : TransformsTo grade p q)
    (φ : D' → D) : TransformsTo (grade ∘ φ) (p ∘ φ) (q ∘ φ) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  exact ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, by tauto⟩

/-- A downward-closed part of the image that is stable under replacement
pulls back across a guarded shifter. A downward move can be reversed within its block. -/
theorem preimage_of_replacement {P : ExtOrd → Prop} {σ : ExtOrd → ExtOrd} (hm : Monotone σ)
    {k i : ℕ} (hi : i ≤ k) (down : ∀ {x y}, x ≤ y → P y → P x)
    (stable : ∀ {x j}, j ≤ k → P x → P (extVisibilityReplace x k j))
    (comm : ∀ x, P (σ x) → ∀ j, j ≤ k →
      σ (extVisibilityReplace x k j) = extVisibilityReplace (σ x) k j)
    {x : ExtOrd} (hx : P (σ (extVisibilityReplace x k i))) : P (σ x) := by
  obtain hik | rfl := hi.lt_or_eq
  · rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
    · exact hx
    · exact hx
    by_cases h : finitePart a < k
    · rw [extVisibilityReplace_ofOrd, visibilityReplace, if_pos h, ordinalReplace] at hx
      have he := comm _ hx (finitePart a) h.le
      rw [extVisibilityReplace_ofOrd, visibilityReplace,
        if_pos (by rwa [finitePart_limitPart_add_nat]), ordinalReplace,
        limitPart_limitPart_add_nat, decomposition] at he
      exact he.symm ▸ stable h.le hx
    · rwa [extVisibilityReplace_ofOrd, visibilityReplace, if_neg h] at hx
  · exact down (hm (Value.le_extVisibilityReplace_self x _)) hx

/-- Strict truncation of targets at a limit preserves the transformation. -/
theorem TransformsTo.truncExt_target {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p q : D → ExtOrd} (h : TransformsTo grade p q) :
    TransformsTo grade p (truncExt α ∘ q) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  refine ⟨truncExt α ∘ g, truncExt α ∘ σ,
    fun n m h => truncExt_mono α (hg_dec n m h),
    fun k => (truncExt_preserves_selfVis α _ _ (hg_vis k).symm).symm,
    by rw [Function.comp_apply, hσ_bot]; rfl,
    fun x y hxy => truncExt_mono α (hσ_mono hxy),
    ?_,
    fun d => by simp only [Function.comp_apply]; rw [hσ_eq d, truncExt_min]⟩
  intro x k hle i hi
  simp only [Function.comp_apply] at hle ⊢
  rw [← truncExt_evr_comm hα (σ x) k i]
  by_cases hxk : σ x ≤ g k
  · -- the original clause applies
    tauto
  -- `g k < σ x`: both truncations are `⊤`
  have hlt : g k < σ x := not_le.mp hxk
  have htop : truncExt α (g k) = ⊤ := by
    have heq : truncExt α (g k) = truncExt α (σ x) :=
      le_antisymm (truncExt_mono α hlt.le) hle
    rcases truncExt_bound α (g k) with hb | hb
    · exfalso
      have hgk : truncExt α (g k) = g k :=
        truncExt_id_of_lt ((truncExt_le_self α (g k)).trans_lt hb)
      have hσx : truncExt α (σ x) = σ x :=
        truncExt_id_of_lt ((truncExt_le_self α (σ x)).trans_lt (heq ▸ hb))
      grind
    · exact hb
  have hαg : ofOrd α ≤ g k := truncExt_eq_top_iff.mp htop
  have hασ : ofOrd α ≤ σ x := hαg.trans hlt.le
  rw [truncExt_eq_top_of_ge (extVisReplace_ge_of_ge_limit hα hασ k i)]
  apply truncExt_eq_top_of_ge
  by_contra hn
  exact hασ.not_gt (preimage_of_replacement (P := (· < ofOrd α)) hσ_mono hi
    (fun h h' => h.trans_lt h') (fun _ hx => extVisReplace_lt_of_lt_limit hα hx _ _)
    (fun x hx => hσ_vis x k (hx.le.trans hαg)) (not_le.mp hn))

/-- Every labelling transforms to the constantly-`−∞` labelling (witnesses `σ ≡ ⊥`, `g ≡ ⊤`;
clause 5 is `⊥ = ⊥`). -/
theorem TransformsTo.to_bot {X : Type*} {grade : X → ℕ} (p : X → ExtOrd) :
    TransformsTo grade p (fun _ => ⊥) :=
  ⟨fun _ => ⊤, fun _ => ⊥,
    fun _ _ _ => le_refl ⊤,
    fun _ => rfl,
    rfl,
    monotone_const,
    by simp,
    by simp⟩

end Transform

end VaughtConjecture.Knight
