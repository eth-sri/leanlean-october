module

public import Chazelle.Core.ClusterSplitRam
public import Chazelle.Core.ClusterSplitMath
public import Chazelle.Core.ClusterTrees
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-I, part 33: the split step is correct

The mathematics connecting the RAM split step (`ClusterSplitRam.lean`) to the typed separator
(`ClusterSplitMath.lean`) and to the work-stack invariant (`ClusterStack.lean`):

* `iterate_parentN`, `anc_window`: the ancestors of `u` in a window of levels are the vertices
  `up^[lu - t + i] u` marked by `markStmt`;
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section window

variable {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)} (T : SpanTree M)

/-- The parent map on numbers. -/
theorem iterate_parentN {upN : ℕ → ℕ} (hup : ∀ v : Fin μ, upN v = T.parent v) (n : ℕ)
    (u : Fin μ) : upN^[n] u = ((T.parent^[n] u : Fin μ) : ℕ) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hup, ih, Function.iterate_succ_apply]

/-- **The marked ancestors in a level window.** -/
theorem anc_window {upN : ℕ → ℕ} (hup : ∀ v : Fin μ, upN v = T.parent v) (x u : Fin μ)
    {lbot ltop : ℕ} (hx : lbot ≤ T.level x ∧ T.level x ≤ ltop) :
    (lbot ≤ min (T.level u) ltop ∧ ∃ i, i < min (T.level u) ltop + 1 - lbot ∧
      (x : ℕ) = upN^[T.level u - min (T.level u) ltop + i] u) ↔ T.IsAnc x u := by
  constructor
  · rintro ⟨-, i, -, hi⟩
    rw [iterate_parentN T hup] at hi
    exact ⟨_, (Fin.ext hi).symm⟩
  · rintro ⟨n, hn⟩
    -- `x` is the ancestor `lu - level x` levels up
    have hlev := T.level_iterate_parent n u
    rw [hn] at hlev
    have hx' : T.parent^[T.level u - T.level x] u = x := by
      by_cases hnl : n ≤ T.level u
      · rw [show T.level u - T.level x = n by omega, hn]
      · have h1 : T.parent^[n] u = T.root := T.iterate_parent_eq_root (by omega)
        have h2 : T.parent^[T.level u - T.level x] u = T.root :=
          T.iterate_parent_eq_root (by rw [hn] at h1; subst h1; rwo [T.level_root])
        rw [h2, ← h1, hn]
    have hxu : T.level x ≤ T.level u := by
      have := T.level_iterate_parent (T.level u - T.level x) u
      rwo [hx'] at this
    refine ⟨by omega, min (T.level u) ltop - T.level x, by omega, ?_⟩
    rw [iterate_parentN T hup, show T.level u - min (T.level u) ltop +
      (min (T.level u) ltop - T.level x) = T.level u - T.level x by omega, hx']

end window

/-! ## The three passes -/

section passes

variable {W : ℕ}

/-- One pass in the slot layout: its effect on `ACT`, `POS` and the rest. -/
theorem pass_spec {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {sel : ℕ → Prop}
    {lo hi e : ℕ} (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (_hloe : lo ≤ e)
    (hit : ∀ i, lo ≤ i → i < hi → m (S.bTMP + i) < S.μ)
    (hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m (S.bTMP + i) = m (S.bTMP + i') →
      i = i')
    (hle : e + cntS sel lo hi ≤ hi) :
    (∀ i, lo ≤ i → i < hi → sel i →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).1 (S.bACT + (e + cntS sel lo i)) =
        m (S.bTMP + i)) ∧
    (∀ i, lo ≤ i → i < hi → sel i →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).1 (S.bPOS + m (S.bTMP + i)) =
        e + cntS sel lo i) ∧
    (∀ a, ¬ (S.bACT + e ≤ a ∧ a < S.bACT + (e + cntS sel lo hi)) →
      (∀ i, lo ≤ i → i < hi → sel i → a ≠ S.bPOS + m (S.bTMP + i)) →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).1 a = m a) ∧
    (passMem m sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).2 = e + cntS sel lo hi := by
  have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hTMP
  have hj : lo + (hi - lo) = hi := by omega
  have hdAP : ∀ i, lo ≤ i → i < lo + (hi - lo) → ∀ p, e ≤ p →
      p < e + cntS sel lo (lo + (hi - lo)) → S.bPOS + m (S.bTMP + i) ≠ S.bACT + p := by
    intro i h1 h2 p h3 h4
    rw [hj] at h4
    have := hit i h1 (by omega)
    omega
  refine ⟨fun i h1 h2 hs => passMem_act (hi - lo) hdAP i h1 (by omega) hs,
    fun i h1 h2 hs => passMem_pos (hi - lo) hdAP
      (fun a b c d e' f => hinj a b c (by omega) e' (by omega)) i h1 (by omega) hs,
    fun a h1 h2 => passMem_keep (hi - lo) (by rwx [hj])
      (fun i a' b c => h2 i a' (by omega) c), by rw [passMem_ptr_eq, hj]⟩

/-- **The three passes**: each class lands in its range of `ACT`, the positions of its items are
recorded, nothing else changes. -/
theorem passes_spec {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {lo hi f : ℕ}
    (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m (S.bTMP + i) < S.μ)
    (hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m (S.bTMP + i) = m (S.bTMP + i') →
      i = i')
    (hsum : cntS (SelI m S f f) lo hi + cntS (SelI m S (2 * S.N + m (S.bFP + f)) f) lo hi +
      cntS (SelI m S (S.N + f) f) lo hi ≤ hi - lo) :
    let s0 := SelI m S f f
    let s1 := SelI m S (2 * S.N + m (S.bFP + f)) f
    let s2 := SelI m S (S.N + f) f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    (∀ i, lo ≤ i → i < hi → s0 i →
      (passC m S lo hi f).1 (S.bACT + (lo + cntS s0 lo i)) = m (S.bTMP + i)) ∧
    (∀ i, lo ≤ i → i < hi → s1 i →
      (passC m S lo hi f).1 (S.bACT + (e1 + cntS s1 lo i)) = m (S.bTMP + i)) ∧
    (∀ i, lo ≤ i → i < hi → s2 i →
      (passC m S lo hi f).1 (S.bACT + (e2 + cntS s2 lo i)) = m (S.bTMP + i)) ∧
    (∀ a, ¬ (S.bACT + lo ≤ a ∧ a < S.bACT + e3) →
      (∀ i, lo ≤ i → i < hi → (s0 i ∨ s1 i ∨ s2 i) → a ≠ S.bPOS + m (S.bTMP + i)) →
      (passC m S lo hi f).1 a = m a) ∧
    (passC m S lo hi f).2 = e3 ∧
    ((∀ i t t', lo ≤ i → i < hi → ((t = 0 ∧ s0 i) ∨ (t = 1 ∧ s1 i) ∨ (t = 2 ∧ s2 i)) →
      ((t' = 0 ∧ s0 i) ∨ (t' = 1 ∧ s1 i) ∨ (t' = 2 ∧ s2 i)) → t = t') →
      (∀ i, lo ≤ i → i < hi → s0 i →
        (passC m S lo hi f).1 (S.bPOS + m (S.bTMP + i)) = lo + cntS s0 lo i) ∧
      (∀ i, lo ≤ i → i < hi → s1 i →
        (passC m S lo hi f).1 (S.bPOS + m (S.bTMP + i)) = e1 + cntS s1 lo i) ∧
      (∀ i, lo ≤ i → i < hi → s2 i →
        (passC m S lo hi f).1 (S.bPOS + m (S.bTMP + i)) = e2 + cntS s2 lo i)) := by
  intro s0 s1 s2 e1 e2 e3
  have hsum' : cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := hsum
  have he1 : e1 = lo + cntS s0 lo hi := rfl
  have he2 : e2 = e1 + cntS s1 lo hi := rfl
  have he3 : e3 = e2 + cntS s2 lo hi := rfl
  clear_value e1 e2 e3
  have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hTMP
  -- pass A
  obtain ⟨a1, a2, a3, a4⟩ := pass_spec (sel := s0) (e := lo) hL (m := m) hlh hhi le_rfl hit hinj
    (by omega)
  have hA1 : (passA m S lo hi f).1 = (passMem m s0 S.bACT S.bPOS S.bTMP lo lo (hi - lo)).1 := rfl
  have hA2 : (passA m S lo hi f).2 = e1 := by
    show (passMem m s0 S.bACT S.bPOS S.bTMP lo lo (hi - lo)).2 = e1; rw [a4, he1]
  -- `TMP` is untouched
  have tA : ∀ i, lo ≤ i → i < hi → (passA m S lo hi f).1 (S.bTMP + i) = m (S.bTMP + i) := by
    intro i h1 h2
    rw [hA1]
    refine a3 _ (by omega) (fun i' b c d => ?_)
    have := hit i' b c; omega
  obtain ⟨b1, b2, b3, b4⟩ := pass_spec (sel := s1) (e := e1) hL (m := (passA m S lo hi f).1) hlh hhi
    (by omega) (fun i h1 h2 => by rw [tA i h1 h2]; exact hit i h1 h2)
    (fun i i' h1 h2 h3 h4 h => hinj i i' h1 h2 h3 h4 (by rwx [← tA i h1 h2, ← tA i' h3 h4]))
    (by omega)
  have hB1 : (passB m S lo hi f).1 =
      (passMem (passA m S lo hi f).1 s1 S.bACT S.bPOS S.bTMP lo e1 (hi - lo)).1 := by
    unfold passB; rw [hA2]
  have hB2 : (passB m S lo hi f).2 = e2 := by unfold passB; rw [hA2, b4, he2]
  have tB : ∀ i, lo ≤ i → i < hi → (passB m S lo hi f).1 (S.bTMP + i) = m (S.bTMP + i) := by
    intro i h1 h2
    rw [hB1, b3 _ (by omega) (fun i' b c d => ?_), tA i h1 h2]
    rw [tA i' b c]; have := hit i' b c; omega
  obtain ⟨c1, c2, c3, c4⟩ := pass_spec (sel := s2) (e := e2) hL (m := (passB m S lo hi f).1) hlh hhi
    (by omega) (fun i h1 h2 => by rw [tB i h1 h2]; exact hit i h1 h2)
    (fun i i' h1 h2 h3 h4 h => hinj i i' h1 h2 h3 h4 (by rwx [← tB i h1 h2, ← tB i' h3 h4]))
    (by omega)
  have hC1 : (passC m S lo hi f).1 =
      (passMem (passB m S lo hi f).1 s2 S.bACT S.bPOS S.bTMP lo e2 (hi - lo)).1 := by
    unfold passC; rw [hB2]
  have hC2 : (passC m S lo hi f).2 = e3 := by unfold passC; rw [hB2, c4, he3]
  have hr0 : ∀ i, lo ≤ i → i < hi → cntS s0 lo i ≤ cntS s0 lo hi := fun i _ h =>
    cntS_mono (by omega)
  have hr1 : ∀ i, lo ≤ i → i < hi → cntS s1 lo i ≤ cntS s1 lo hi := fun i _ h =>
    cntS_mono (by omega)
  have hlt : ∀ (sel : ℕ → Prop) i, lo ≤ i → i < hi → sel i → cntS sel lo i < cntS sel lo hi :=
    fun sel i h1 h2 h3 => cntS_lt h1 h2 h3
  refine ⟨fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_, fun a h1 h2 => ?_,
    hC2, fun huniq => ⟨fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_⟩⟩
  · have := hlt s0 i h1 h2 hs
    rw [hC1, c3 _ (by omega) (fun i' b c d => by rw [tB i' b c]; have := hit i' b c; omega), hB1,
      b3 _ (by omega) (fun i' b c d => by rw [tA i' b c]; have := hit i' b c; omega), hA1,
      a1 i h1 h2 hs]
  · have := hlt s1 i h1 h2 hs
    rw [hC1, c3 _ (by omega) (fun i' b c d => by rw [tB i' b c]; have := hit i' b c; omega), hB1,
      b1 i h1 h2 hs, tA i h1 h2]
  · rw [hC1, c1 i h1 h2 hs, tB i h1 h2]
  · rw [hC1, c3 a (by omega) (fun i b c d => by rw [tB i b c]; exact h2 i b c (Or.inr (Or.inr d))),
      hB1, b3 a (by omega) (fun i b c d => by rw [tA i b c]; exact h2 i b c (Or.inr (Or.inl d))),
      hA1, a3 a (by omega) (fun i b c d => h2 i b c (Or.inl d))]
  · have hn1 : ¬ s1 i := fun h => absurd (huniq i 0 1 h1 h2 (Or.inl ⟨rfl, hs⟩)
      (Or.inr (Or.inl ⟨rfl, h⟩))) (by omega)
    have hn2 : ¬ s2 i := fun h => absurd (huniq i 0 2 h1 h2 (Or.inl ⟨rfl, hs⟩)
      (Or.inr (Or.inr ⟨rfl, h⟩))) (by omega)
    have hv := hit i h1 h2
    rw [hC1, c3 _ (by omega) (fun i' b c d => by
        rw [tB i' b c]; intro h
        have := hinj i i' h1 h2 b c (by omega)
        subst this; exact hn2 d), hB1,
      b3 _ (by omega) (fun i' b c d => by
        rw [tA i' b c]; intro h
        have := hinj i i' h1 h2 b c (by omega)
        subst this; exact hn1 d), hA1, a2 i h1 h2 hs]
  · have hn2 : ¬ s2 i := fun h => absurd (huniq i 1 2 h1 h2 (Or.inr (Or.inl ⟨rfl, hs⟩))
      (Or.inr (Or.inr ⟨rfl, h⟩))) (by omega)
    have hv := hit i h1 h2
    rw [hC1, c3 _ (by omega) (fun i' b c d => by
        rw [tB i' b c]; intro h
        have := hinj i i' h1 h2 b c (by omega)
        subst this; exact hn2 d), hB1, ← tA i h1 h2, b2 i h1 h2 hs]
  · rw [hC1, ← tB i h1 h2, c2 i h1 h2 hs]

end passes

end

end Chazelle.Core.Cluster
