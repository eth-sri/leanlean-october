/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibilityAlgebra
public import VaughtConjecture.Knight.Semantics

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- The five clauses of Def. 2.3.9 for a suppressor/shifter pair. -/
structure Witness (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd) : Prop where
  anti : ∀ n m : ℕ, n < m → g m ≤ g n
  vis : ∀ n : ℕ, g n = extVisibilityReplace (g n) n n
  bot : σ ⊥ = ⊥
  mono : Monotone σ
  clause5 : ∀ (α : ExtOrd) (k : ℕ), σ α ≤ g k → ∀ i : ℕ, i ≤ k →
    σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i

theorem Witness.transformsTo {D : Type*} {grade : D → ℕ} {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd}
    (hw : Witness g σ) {f t : D → ExtOrd} (heq : ∀ d, t d = min (σ (f d)) (g (grade d))) :
    TransformsTo grade f t :=
  ⟨g, σ, hw.anti, hw.vis, hw.bot, hw.mono, hw.clause5, heq⟩

/-- The suppressor `⊤` at grades `≤ K`, `⊥` above. -/
def gTop (K : ℕ) : ℕ → ExtOrd := fun k => if k ≤ K then ⊤ else ⊥

theorem gTop_of_le {K k : ℕ} (h : k ≤ K) : gTop K k = ⊤ := ite_eq_left h

theorem gTop_of_gt {K k : ℕ} (h : K < k) : gTop K k = ⊥ := ite_eq_right (not_le.mpr h)

theorem Witness.comm {K : ℕ} {τ : ExtOrd → ExtOrd} (h : Witness (gTop K) τ)
    (x : ExtOrd) {k i : ℕ} (hk : k ≤ K) (hi : i ≤ k) :
    τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i :=
  h.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi

theorem gTop_anti (K : ℕ) : Antitone (gTop K) := by
  intro n m h
  unfold gTop
  split_ifs <;> first | exact le_rfl | exact bot_le | omega

theorem gTop_vis (K k : ℕ) : SelfVis k (gTop K k) := by
  unfold gTop
  split_ifs <;> rfl

theorem witness_id (K : ℕ) : Witness (gTop K) id :=
  ⟨fun _ _ h => gTop_anti K h.le, fun k => (gTop_vis K k).symm,
    rfl, monotone_id, fun _ _ _ _ _ => rfl⟩

theorem Witness.zero_repl {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd} (h : Witness g τ)
    (x : ExtOrd) (hx : τ x = ⊥) (k : ℕ) {i : ℕ} (hi : i ≤ k) :
    τ (extVisibilityReplace x k i) = ⊥ := by
  rw [h.clause5 x k (hx ▸ bot_le) i hi, hx, extVisibilityReplace_bot]

theorem Witness.of_top {K : ℕ} {τ : ExtOrd → ExtOrd} (hb : τ ⊥ = ⊥) (hm : Monotone τ)
    (comm : ∀ x k i, k ≤ K → i ≤ k → τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i)
    (zero : ∀ x, τ x = ⊥ → ∀ k i, i ≤ k → τ (extVisibilityReplace x k i) = ⊥) :
    Witness (gTop K) τ := by
  refine ⟨(witness_id K).anti, (witness_id K).vis, hb, hm, fun x k h i hi => ?_⟩
  rcases le_or_gt k K with hk | hk
  · exact comm x k i hk hi
  · rw [gTop_of_gt hk, le_bot_iff] at h
    rw [zero x h k i hi, h, extVisibilityReplace_bot]

theorem Witness.transformsTo_top {D : Type*} {grade : D → ℕ} {K : ℕ} {σ : ExtOrd → ExtOrd}
    (hw : Witness (gTop K) σ) {f t : D → ExtOrd} (hg : ∀ d, grade d ≤ K)
    (heq : ∀ d, t d = σ (f d)) : TransformsTo grade f t :=
  hw.transformsTo (fun d => by rw [gTop_of_le (hg d), min_top_right, heq])

/-- Truncating and capping the suppressor keeps the same shifter. -/
theorem Transform.TransformsTo.cap {D : Type*} {grade : D → ℕ} {p q : D → ExtOrd} {K : ℕ} {γ : ExtOrd}
    (h : TransformsTo grade p q) (hK : ∀ d, grade d ≤ K) (hγ : SelfVis K γ) :
    TransformsTo grade p (fun d => min (q d) γ) := by
  obtain ⟨g, σ, hg, hv, hb, hm, hc, he⟩ := h
  refine ⟨fun k => min (gTop K k) (min (g k) γ), σ, ?_, ?_, hb, hm, ?_, ?_⟩
  · exact fun n m h => min_le_min (gTop_anti K h.le) (min_le_min_right _ (hg n m h))
  · intro k
    rcases le_or_gt k K with hk | hk
    · simpa only [gTop_of_le hk, min_top_left] using (selfVis_min (hv k).symm (hγ.mono hk)).symm
    · simp only [gTop_of_gt hk, min_bot_left, extVisibilityReplace_bot]
  · exact fun x k h i hi => hc x k (h.trans ((min_le_right _ _).trans (min_le_left _ _))) i hi
  · intro d
    simp only [gTop_of_le (hK d), min_top_left, ← min_assoc, ← he]

/-- Pointwise maximum preserves witnesses with the same suppressor. Both guards
follow from the guard on the maximum; neither locality is discarded. -/
theorem Witness.max {g : ℕ → ExtOrd} {σ τ : ExtOrd → ExtOrd}
    (hσ : Witness g σ) (hτ : Witness g τ) : Witness g (fun a => max (σ a) (τ a)) where
  anti := hσ.anti
  vis := hσ.vis
  bot := by rw [hσ.bot, hτ.bot, max_self]
  mono := fun _ _ h => max_le_max (hσ.mono h) (hτ.mono h)
  clause5 := by
    intro a k hk i hi
    rw [hσ.clause5 a k ((le_max_left _ _).trans hk) i hi,
      hτ.clause5 a k ((le_max_right _ _).trans hk) i hi,
      extVisibilityReplace_max _ _ hi]

section Capped

variable {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}

/-- Above a visible cutoff allowed by the guard, replacements stay above it. -/
theorem cap_le_of_evr {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hσmono : Monotone σ)
    (hσevr : ∀ x k, σ x ≤ g k → ∀ i, i ≤ k →
      σ (extVisibilityReplace x k i) = extVisibilityReplace (σ x) k i)
    {cap : ExtOrd} {k : ℕ} (hvis : SelfVis k cap) (hcap : cap ≤ g k)
    {x : ExtOrd} (hx : cap < σ x) {i : ℕ} (hi : i ≤ k) :
    cap < σ (extVisibilityReplace x k i) :=
  lt_of_not_ge fun h => hx.not_ge (preimage_of_replacement (P := (· ≤ cap)) hσmono hi
    (fun ha hb => ha.trans hb) (fun hj hy => extVisibilityReplace_le_of_le_selfVis hj hvis hy)
    (fun y hy => hσevr y k (hy.trans hcap)) h)

/-- A controller of maximal grade gives a bounded shifter with exact readback. -/
theorem exists_bounded_exact_capped_witness (hmax : ∀ d, grade d ≤ grade c) (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (grade c)) τ ∧
      (∀ x, τ x ≤ p c) ∧ (∀ d, τ (E d) = min (p d) (p c)) := by
  by_cases hb : p c = ⊥
  · exact ⟨fun _ => ⊥, Witness.of_top rfl monotone_const (by simp) (by simp),
      fun _ => bot_le, by simp [hb]⟩
  obtain ⟨g, σ, hanti, -, hbot, hmono, hcomm, hread⟩ := hloc
  have hg : ∀ k ≤ grade c, p c ≤ g k := by
    have hc := hread c
    simp only [min_self] at hc
    exact fun k hk => hc.le.trans ((min_le_right _ _).trans (suppressor_le_of_grade_le hanti hk))
  refine ⟨fun x => min (σ x) (p c), Witness.of_top (by simp [hbot]) (hmono.min monotone_const) ?_ ?_,
    fun _ => min_le_right _ _, ?_⟩
  · intro x k i hk hi
    have hv := hvis.mono hk
    rcases le_or_gt (σ x) (p c) with h | h
    · rw [min_eq_left h, hcomm x k (h.trans (hg k hk)) i hi,
        min_eq_left (extVisibilityReplace_le_of_le_selfVis hi hv h)]
    · rw [min_eq_right h.le, evr_eq_self_of_selfVis hv,
        min_eq_right (cap_le_of_evr hmono hcomm hv (hg k hk) h hi).le]
  · intro x hx k i hi
    change min (σ x) (p c) = ⊥ at hx
    have hz : σ x = ⊥ := by simpa [hb] using hx
    simp [hcomm x k (hz ▸ bot_le) i hi, hz]

  · intro d
    simpa only [min_assoc, min_self, min_eq_right (hg _ (hmax d))] using
      congrArg (fun x => min x (p c)) (hread d).symm

end Capped

section Rows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- Exact, bounded readback of a lawful labeling from a controller's semantic row. -/
theorem RespectsSemanticsBelow.rowWitness {J : Finset ι × ℕ} {p : D.below J → ExtOrd}
    (hp : RespectsSemanticsBelow sem J p) (c : D.below J) :
    ∃ τ, Witness (gTop (D.grade c.1)) τ ∧ (∀ x, τ x ≤ p c) ∧
      ∀ d, τ (sem.E c.1 d) = min (p (CellScheme.below.incl c d)) (p c) :=
  exists_bounded_exact_capped_witness (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
    (fun d => d.2.2) (hp.orderly c).symm (hp.locality c)

theorem RespectsSemantics.rowWitness {p : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (c : Cell D) :
    ∃ τ, Witness (gTop (D.grade c)) τ ∧ (∀ x, τ x ≤ p c) ∧
      ∀ d, τ (sem.E c d) = min (p d.1) (p c) :=
  (hp.toBelow (D.cell c)).rowWitness ⟨c, GradedLe.refl _⟩

end Rows

end VaughtConjecture.Knight
