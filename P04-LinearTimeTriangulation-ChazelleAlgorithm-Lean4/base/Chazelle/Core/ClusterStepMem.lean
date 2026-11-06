module

public import Chazelle.Core.ClusterSplitStep

/-!
# WP-I, part 37: the memory after the passes and the release of the separator

* `cntS3_le`: three pairwise exclusive selections select at most the whole segment;
* `stepMem`: the memory after the three class passes and `sepMem`, region by region.
-/

namespace Chazelle.Core.Cluster

open Machine

@[expose] public section

open Classical in
/-- Three pairwise exclusive selections select at most the positions of the segment. -/
theorem cntS3_le {s0 s1 s2 : ℕ → Prop} {lo hi : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → ¬ (s0 i ∧ s1 i) ∧ ¬ (s0 i ∧ s2 i) ∧ ¬ (s1 i ∧ s2 i)) :
    cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := by
  classical
  unfold cntS
  have d01 : Disjoint ((Finset.Ico lo hi).filter s0) ((Finset.Ico lo hi).filter s1) := by
    rw [Finset.disjoint_left]
    intro i h0 h1
    obtain ⟨hi0, a0⟩ := Finset.mem_filter.mp h0
    obtain ⟨-, a1⟩ := Finset.mem_filter.mp h1
    obtain ⟨b1, b2⟩ := Finset.mem_Ico.mp hi0
    exact (h i b1 b2).1 ⟨a0, a1⟩
  have d2 : Disjoint ((Finset.Ico lo hi).filter s0 ∪ (Finset.Ico lo hi).filter s1)
      ((Finset.Ico lo hi).filter s2) := by
    rw [Finset.disjoint_left]
    intro i h01 h2
    obtain ⟨hi2, a2⟩ := Finset.mem_filter.mp h2
    obtain ⟨b1, b2⟩ := Finset.mem_Ico.mp hi2
    rcases Finset.mem_union.mp h01 with h0 | h1
    · exact (h i b1 b2).2.1 ⟨(Finset.mem_filter.mp h0).2, a2⟩
    · exact (h i b1 b2).2.2 ⟨(Finset.mem_filter.mp h1).2, a2⟩
  rw [← Finset.card_union_of_disjoint d01, ← Finset.card_union_of_disjoint d2, ← Nat.card_Ico]
  refine Finset.card_le_card (fun i hi' => ?_)
  rcases Finset.mem_union.mp hi' with h01 | h2
  · rcases Finset.mem_union.mp h01 with h0 | h1
    · exact (Finset.mem_filter.mp h0).1
    · exact (Finset.mem_filter.mp h1).1
  · exact (Finset.mem_filter.mp h2).1

/-- The stack does not read above its top. -/
theorem stkList_congr {m m' : ℕ → ℕ} {b : ℕ} (n : ℕ)
    (h : ∀ x, b ≤ x → x < b + 2 * n → m' x = m x) : stkList m' b n = stkList m b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stkList]
    rw [h _ (by omega) (by omega), h _ (by omega) (by omega),
      ih (fun x hx hx' => h x hx (by omega))]

/-- The pushed entry, if any. -/
def optSeg (s a b : ℕ) : List (ℕ × ℕ) := if s < b - a then [(a, b)] else []

/-- **One push** on the stored stack. -/
theorem pushF_stk {bS s a b : ℕ} {q : (ℕ → ℕ) × ℕ} {L : List (ℕ × ℕ)}
    (hL : L = stkList q.1 bS L.length) (htp : q.2 = 2 * L.length) :
    optSeg s a b ++ L = stkList (pushF bS s a b q).1 bS (optSeg s a b ++ L).length ∧
      (pushF bS s a b q).2 = 2 * (optSeg s a b ++ L).length ∧
      ∀ x, (x < bS + q.2 ∨ bS + 2 * (optSeg s a b ++ L).length ≤ x) →
        (pushF bS s a b q).1 x = q.1 x := by
  unfold pushF optSeg
  by_cases hs : s < b - a
  · simp only [ite_eq_left hs, List.singleton_append, List.length_cons]
    refine ⟨?_, by rw [htp]; ring, fun x hx => ?_⟩
    · simp only [stkList]
      have e1 : upd (upd q.1 (bS + q.2) a) (bS + q.2 + 1) b (bS + 2 * L.length) = a := by
        rw [upd_apply, upd_apply, ite_eq_right (by omega), ite_eq_left (by omega)]
      have e2 : upd (upd q.1 (bS + q.2) a) (bS + q.2 + 1) b (bS + 2 * L.length + 1) = b := by
        rw [upd_apply, ite_eq_left (by omega)]
      rw [e1, e2]
      congr 1
      rw [stkList_congr _ (fun x _ hx => by rw [upd_apply, upd_apply, ite_eq_right (by omega),
        ite_eq_right (by omega)])]
      exact hL
    · rw [upd_apply, upd_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [ite_eq_right hs, List.nil_append]
    refine ⟨hL, htp, ?_⟩; simp

section

variable {W : ℕ}

open Classical in
/-- **The memory after the passes and the release of the separator.** -/
theorem stepMem {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m m2 : ℕ → ℕ} {lo hi f : ℕ}
    {mk : ℕ → Prop} (hlh : lo ≤ hi) (hhi : hi ≤ S.μ)
    (hact : ∀ i, lo ≤ i → i < hi → m (S.bACT + i) < S.μ)
    (hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m (S.bACT + i) = m (S.bACT + i') →
      i = i')
    (h2tmp : ∀ i, lo ≤ i → i < hi → m2 (S.bTMP + i) = m (S.bACT + i))
    (h2df : ∀ i, lo ≤ i → i < hi → (m2 (S.bDF + m (S.bACT + i)) = 1 ↔ mk i))
    (hsum : cntS (SelI m2 S f f) lo hi + cntS (SelI m2 S (2 * S.N + m2 (S.bFP + f)) f) lo hi +
      cntS (SelI m2 S (S.N + f) f) lo hi ≤ hi - lo)
    (huniq : ∀ i, lo ≤ i → i < hi → ¬ (SelI m2 S f f i ∧ SelI m2 S (2 * S.N + m2 (S.bFP + f)) f i) ∧
      ¬ (SelI m2 S f f i ∧ SelI m2 S (S.N + f) f i) ∧
      ¬ (SelI m2 S (2 * S.N + m2 (S.bFP + f)) f i ∧ SelI m2 S (S.N + f) f i))
    (hsmk : ∀ i, lo ≤ i → i < hi → (SelI m2 S f f i ∨ SelI m2 S (2 * S.N + m2 (S.bFP + f)) f i ∨
      SelI m2 S (S.N + f) f i) → ¬ mk i) :
    let s0 := SelI m2 S f f
    let s1 := SelI m2 S (2 * S.N + m2 (S.bFP + f)) f
    let s2 := SelI m2 S (S.N + f) f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    let mS := sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo (hi - lo)
    (∀ x, ¬ (S.bACT + lo ≤ x ∧ x < S.bACT + e3) → ¬ (S.bPOS ≤ x ∧ x < S.bPOS + S.μ) →
      mS x = m2 x) ∧
    (∀ i, lo ≤ i → i < hi → s0 i → mS (S.bACT + (lo + cntS s0 lo i)) = m (S.bACT + i)) ∧
    (∀ i, lo ≤ i → i < hi → s1 i → mS (S.bACT + (e1 + cntS s1 lo i)) = m (S.bACT + i)) ∧
    (∀ i, lo ≤ i → i < hi → s2 i → mS (S.bACT + (e2 + cntS s2 lo i)) = m (S.bACT + i)) ∧
    (∀ i, lo ≤ i → i < hi → mk i → mS (S.bPOS + m (S.bACT + i)) = S.μ) ∧
    (∀ i, lo ≤ i → i < hi → s0 i → mS (S.bPOS + m (S.bACT + i)) = lo + cntS s0 lo i) ∧
    (∀ i, lo ≤ i → i < hi → s1 i → mS (S.bPOS + m (S.bACT + i)) = e1 + cntS s1 lo i) ∧
    (∀ i, lo ≤ i → i < hi → s2 i → mS (S.bPOS + m (S.bACT + i)) = e2 + cntS s2 lo i) ∧
    (∀ w, w < S.μ → (∀ i, lo ≤ i → i < hi → m (S.bACT + i) ≠ w) →
      mS (S.bPOS + w) = m2 (S.bPOS + w)) ∧
    (passC m2 S lo hi f).2 = e3 := by
  intro s0 s1 s2 e1 e2 e3 mS
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU
  have hit : ∀ i, lo ≤ i → i < hi → m2 (S.bTMP + i) < S.μ := fun i a b => by
    rw [h2tmp i a b]; exact hact i a b
  have hinj2 : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m2 (S.bTMP + i) = m2 (S.bTMP + i') →
      i = i' := fun i i' a b c d e => hinj i i' a b c d (by rw [← h2tmp i a b, ← h2tmp i' c d]; exact e)
  obtain ⟨A1, A2, A3, A4, A5, A6⟩ := passes_spec hL (f := f) hlh hhi hit hinj2 hsum
  have hu : ∀ i t t', lo ≤ i → i < hi → ((t = 0 ∧ s0 i) ∨ (t = 1 ∧ s1 i) ∨ (t = 2 ∧ s2 i)) →
      ((t' = 0 ∧ s0 i) ∨ (t' = 1 ∧ s1 i) ∨ (t' = 2 ∧ s2 i)) → t = t' := by
    intro i t t' a b h1 h2
    obtain ⟨u1, u2, u3⟩ := huniq i a b
    rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
      rcases h2 with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;> first | rfl | tauto
  obtain ⟨P0, P1, P2⟩ := A6 hu
  set mP := (passC m2 S lo hi f).1 with hmP
  -- `TMP` and the marks are untouched by the passes
  have hPt : ∀ i, lo ≤ i → i < hi → mP (S.bTMP + i) = m (S.bACT + i) := by
    intro i a b
    rw [A4 _ (by omega) (fun i' c d _ => by have := hit i' c d; omega)]
    exact h2tmp i a b
  have hPd : ∀ i, lo ≤ i → i < hi → mP (S.bDF + m (S.bACT + i)) = m2 (S.bDF + m (S.bACT + i)) := by
    intro i a b
    have := hact i a b
    exact A4 _ (by omega) (fun i' c d _ => by have := hit i' c d; omega)
  -- the release condition
  have hrel : ∀ x, (∃ i, lo ≤ i ∧ i < lo + (hi - lo) ∧ mP (S.bDF + mP (S.bTMP + i)) = 1 ∧
      x = S.bPOS + mP (S.bTMP + i)) ↔ ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m (S.bACT + i) := by
    intro x
    constructor
    · rintro ⟨i, a, b, c, d⟩
      rw [hPt i a (by omega)] at c d
      rw [hPd i a (by omega)] at c
      exact ⟨i, a, by omega, (h2df i a (by omega)).mp c, d⟩
    · rintro ⟨i, a, b, c, d⟩
      refine ⟨i, a, by omega, ?_, by rw [hPt i a b]; exact d⟩
      rw [hPt i a b, hPd i a b]; exact (h2df i a b).mpr c
  have hmS : ∀ x, mS x = if ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m (S.bACT + i)
      then S.μ else mP x := by
    intro x
    show sepMem mP S.bTMP S.bPOS S.bDF S.μ lo (hi - lo) x = _
    rw [sepMem_apply]
    by_cases h : ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m (S.bACT + i)
    · rw [ite_eq_left ((hrel x).mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((hrel x).mp h')), ite_eq_right h]
  have hnoPOS : ∀ x, ¬ (S.bPOS ≤ x ∧ x < S.bPOS + S.μ) →
      ¬ ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m (S.bACT + i) := by
    rintro x hx ⟨i, a, b, -, rfl⟩
    have := hact i a b; omega
  have hnotmk : ∀ i, lo ≤ i → i < hi → (s0 i ∨ s1 i ∨ s2 i) →
      ¬ ∃ i', lo ≤ i' ∧ i' < hi ∧ mk i' ∧ S.bPOS + m (S.bACT + i) = S.bPOS + m (S.bACT + i') := by
    rintro i a b hs ⟨i', c, d, e, g⟩
    have := hinj i i' a b c d (by omega)
    subst this
    exact hsmk i a b hs e
  refine ⟨fun x h1 h2 => ?_, fun i a b h => ?_, fun i a b h => ?_, fun i a b h => ?_,
    fun i a b h => ?_, fun i a b h => ?_, fun i a b h => ?_, fun i a b h => ?_,
    fun w hw hn => ?_, A5⟩
  · rw [hmS, ite_eq_right (hnoPOS x h2)]
    exact A4 x h1 (fun i c d _ => by have := hit i c d; omega)
  · have := cntS_lt a b h (i' := hi)
    have hs' : cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := hsum
    rw [hmS, ite_eq_right (hnoPOS _ (by omega))]; rw [A1 i a b h, h2tmp i a b]
  · have := cntS_lt a b h (i' := hi)
    have hs' : cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := hsum
    rw [hmS, ite_eq_right (hnoPOS _ (by omega))]; rw [A2 i a b h, h2tmp i a b]
  · have := cntS_lt a b h (i' := hi)
    have hs' : cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := hsum
    rw [hmS, ite_eq_right (hnoPOS _ (by omega))]; rw [A3 i a b h, h2tmp i a b]
  · rw [hmS, ite_eq_left ⟨i, a, b, h, rfl⟩]
  · rw [hmS, ite_eq_right (hnotmk i a b (Or.inl h)), ← h2tmp i a b, P0 i a b h]
  · rw [hmS, ite_eq_right (hnotmk i a b (Or.inr (Or.inl h))), ← h2tmp i a b, P1 i a b h]
  · rw [hmS, ite_eq_right (hnotmk i a b (Or.inr (Or.inr h))), ← h2tmp i a b, P2 i a b h]
  · rw [hmS, ite_eq_right (by rintro ⟨i, a, b, -, e⟩; exact hn i a b (by omega))]
    refine A4 _ (by omega) (fun i c d _ => ?_)
    rw [h2tmp i c d]
    intro e
    exact hn i c d (by omega)

end

end

end Chazelle.Core.Cluster
