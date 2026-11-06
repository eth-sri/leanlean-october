module

public import Chazelle.Core.ClusterStepInv
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-I, part 39: one split step preserves the driver invariant

`dinv_split`: after the marks, the copy, the three passes, the release of the separator and the
pushes, the memory satisfies `DInv` for the new stack (the large classes on top of the rest), the
new finished segments (the small nonempty classes), the new separator set (with the marked items
of the segment) and one more split; the static slots are unchanged and the size potential pays
for the segment.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The class boundaries `a ≤ b ≤ c ≤ d`. -/
def e4 (a b c d : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

theorem mem_optSeg {s a b : ℕ} {q : ℕ × ℕ} : q ∈ optSeg s a b ↔ q = (a, b) ∧ s < b - a := by
  unfold optSeg
  split_ifs with h
  · simp [h]
  · simp [h]

theorem sum_optSeg (g : ℕ × ℕ → ℕ) (s a b : ℕ) : ((optSeg s a b).map g).sum ≤ g (a, b) := by
  unfold optSeg; split_ifs <;> simp

section step

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}

open Classical in
/-- **One split step preserves the driver invariant.** -/
theorem dinv_split {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List (ℕ × ℕ)}
    {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp tp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m ((lo, hi) :: rest) fin D nsp) (htp : tp = 2 * rest.length)
    (hk : 0 < k) {lbot ltop : ℕ}
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items (fun i => m (S.bACT + i)) (lo, hi) →
      lbot ≤ T.level x ∧ T.level x ≤ ltop) (f : Fin N)
    (hgood : Good C (delta first a)
      (liftP (μ := μ) (F := F) (items (fun i => m (S.bACT + i)) (lo, hi))) f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C (delta first a)
      (liftP (μ := μ) (F := F) (items (fun i => m (S.bACT + i)) (lo, hi))) g)
    {m2 : ℕ → ℕ} (hm2 : m2 = copyF (marksF m S lo hi lbot ltop upT f) S lo hi) :
    let s0 := SelI m2 S f f
    let s1 := SelI m2 S (2 * S.N + m2 (S.bFP + f)) f
    let s2 := SelI m2 S (S.N + f) f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    let q := pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2 (pushF S.bSTK S.s lo e1
      (sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo (hi - lo), tp)))
    cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo ∧
    ∃ news fin' D', DInv M T k c S q.1 (news ++ rest) fin' D' (nsp + 1) ∧
      q.2 = 2 * (news ++ rest).length ∧ StaticEq A0 U m q.1 ∧
      (news.map (fun p => len p * Nat.size (len p))).sum + (hi - lo) ≤
        (hi - lo) * Nat.size (hi - lo) := by
  intro s0 s1 s2 e1 e2 e3 q
  have hq : q = pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2 (pushF S.bSTK S.s lo e1
      (sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo (hi - lo), tp))) := rfl
  have hs0 : s0 = SelI m2 S f f := rfl
  have hs1 : s1 = SelI m2 S (2 * S.N + m2 (S.bFP + f)) f := rfl
  have hs2 : s2 = SelI m2 S (S.N + f) f := rfl
  have he1 : e1 = lo + cntS s0 lo hi := rfl
  have he2 : e2 = e1 + cntS s1 lo hi := rfl
  have he3 : e3 = e2 + cntS s2 lo hi := rfl
  clear_value q e3 e2 e1
  -- the facts of the segment
  have hL := hSF.lay
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU
  have := hL.hSTK; have := hL.hFIRST; have := hL.hFPRE; have := hL.hNU
  have hμ := hSF.hμ; have hN := hSF.hN
  have hlv : Lv ((lo, hi) :: rest) fin (lo, hi) := Or.inl List.mem_cons_self
  have hhi : hi ≤ μ := hD.rng _ hlv
  have hlh : lo ≤ hi := hD.sinv.wf _ hlv
  have hbig : S.s < hi - lo := hD.sinv.big _ List.mem_cons_self
  have hmem : ∀ i, lo ≤ i → i < hi →
      m (S.bACT + i) ∈ items (fun i => m (S.bACT + i)) (lo, hi) :=
    fun i i1 i2 => mem_items.mpr ⟨i, i1, i2, rfl⟩
  have hactμ : ∀ i, lo ≤ i → i < hi → m (S.bACT + i) < μ :=
    fun i i1 i2 => hD.sinv.lt _ hlv _ (hmem i i1 i2)
  have hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi →
      m (S.bACT + i) = m (S.bACT + i') → i = i' := by
    intro i i' a b c d e
    exact hD.sinv.inj _ hlv (by simp [a, b]) (by simp [c, d]) e
  have hnD : ∀ i, lo ≤ i → i < hi → m (S.bACT + i) ∉ D :=
    fun i i1 i2 => (hD.sinv.off _ hlv _ (hmem i i1 i2)).1
  have hlen0 : ((lo, hi) :: rest).length ≤ μ := hD.sinv.length_le
  simp only [List.length_cons] at hlen0
  -- the memory after the marks and the copy
  obtain ⟨h2o, h2tmp, h2d, h2fp⟩ := m2_facts hSF hD hwin f
  rw [← hm2] at h2o h2tmp h2d h2fp
  obtain ⟨Sel0, Sel1, Sel2⟩ := sel_iff hSF hD hwin f
  rw [← hm2] at Sel0 Sel1 Sel2
  obtain ⟨Ccov, Cuniq, Chalf, Cedge⟩ := cls_facts hSF hD hgood hch
  -- the class predicates
  set Q : ℕ → ℕ → Prop := fun t i => QC m S T a f t (m (S.bACT + i)) with hQ
  have hQ0 : ∀ i, lo ≤ i → i < hi → (s0 i ↔ Q 0 i) := Sel0
  have hQ1 : ∀ i, lo ≤ i → i < hi → (s1 i ↔ Q 1 i) := Sel1
  have hQ2 : ∀ i, lo ≤ i → i < hi → (s2 i ↔ Q 2 i) := Sel2
  have hc0 : ∀ x, x ≤ hi → cntS s0 lo x = cntS (Q 0) lo x :=
    fun x hx => cntS_congr (fun i i1 i2 => hQ0 i i1 (by omega))
  have hc1 : ∀ x, x ≤ hi → cntS s1 lo x = cntS (Q 1) lo x :=
    fun x hx => cntS_congr (fun i i1 i2 => hQ1 i i1 (by omega))
  have hc2 : ∀ x, x ≤ hi → cntS s2 lo x = cntS (Q 2) lo x :=
    fun x hx => cntS_congr (fun i i1 i2 => hQ2 i i1 (by omega))
  have hQmk : ∀ t i, Q t i → ¬ markN T a f (m (S.bACT + i)) := fun t i h => h.1
  have hQu : ∀ i, lo ≤ i → i < hi → ∀ t t', t < 3 → t' < 3 → Q t i → Q t' i → t = t' :=
    fun i i1 i2 t t' ht ht' h h' => Cuniq i i1 i2 t t' ht ht' h h'
  -- the sum of the classes
  have hsum : cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := by
    refine cntS3_le (fun i i1 i2 => ⟨fun ⟨x, y⟩ => ?_, fun ⟨x, y⟩ => ?_, fun ⟨x, y⟩ => ?_⟩)
    · exact absurd (hQu i i1 i2 0 1 (by omega) (by omega) ((hQ0 i i1 i2).mp x) ((hQ1 i i1 i2).mp y))
        (by omega)
    · exact absurd (hQu i i1 i2 0 2 (by omega) (by omega) ((hQ0 i i1 i2).mp x) ((hQ2 i i1 i2).mp y))
        (by omega)
    · exact absurd (hQu i i1 i2 1 2 (by omega) (by omega) ((hQ1 i i1 i2).mp x) ((hQ2 i i1 i2).mp y))
        (by omega)
  refine ⟨hsum, ?_⟩
  -- the boundaries
  set E := e4 lo e1 e2 e3 with hE
  have hE0 : E 0 = lo := rfl
  have hE1 : E 1 = e1 := rfl
  have hE2 : E 2 = e2 := rfl
  have hE3 : E 3 = e3 := rfl
  have hEs : ∀ t, t < 3 → E (t + 1) = E t + cntS (Q t) lo hi := by
    intro t ht
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · rw [hE0, hE1, he1, hc0 hi le_rfl]
    · rw [hE1, hE2, he2, hc1 hi le_rfl]
    · rw [hE2, hE3, he3, hc2 hi le_rfl]
  have he3hi : e3 ≤ hi := by rwo [he3, he2, he1]
  have hEle : ∀ t, t ≤ 3 → lo ≤ E t ∧ E t ≤ e3 := by
    intro t ht
    have := hEs 0 (by omega); have := hEs 1 (by omega); have := hEs 2 (by omega)
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
  -- the memory after the passes and the release
  have h2df : ∀ i, lo ≤ i → i < hi →
      (m2 (S.bDF + m (S.bACT + i)) = 1 ↔ markN T a f (m (S.bACT + i))) := by
    intro i i1 i2
    rw [h2d _ (hactμ i i1 i2)]
    by_cases hmk : markN T a f (m (S.bACT + i))
    · rw [ite_eq_left ⟨hmem i i1 i2, hmk⟩]; simp [hmk]
    · rw [ite_eq_right (fun h => hmk h.2)]
      exact ⟨fun h => absurd ((hD.df _ (hactμ i i1 i2)).mp h) (hnD i i1 i2), fun h => absurd h hmk⟩
  obtain ⟨SM1, SM2, SM3, SM4, SM5, SM6, SM7, SM8, SM9, SM10⟩ := stepMem hL (f := f)
    (mk := fun i => markN T a f (m (S.bACT + i))) hlh (by rwx [hμ])
    (fun i i1 i2 => by rw [hμ]; exact hactμ i i1 i2) hinj h2tmp h2df hsum
    (fun i i1 i2 => ⟨fun ⟨x, y⟩ => absurd (hQu i i1 i2 0 1 (by omega) (by omega) ((hQ0 i i1 i2).mp x)
        ((hQ1 i i1 i2).mp y)) (by omega),
      fun ⟨x, y⟩ => absurd (hQu i i1 i2 0 2 (by omega) (by omega) ((hQ0 i i1 i2).mp x)
        ((hQ2 i i1 i2).mp y)) (by omega),
      fun ⟨x, y⟩ => absurd (hQu i i1 i2 1 2 (by omega) (by omega) ((hQ1 i i1 i2).mp x)
        ((hQ2 i i1 i2).mp y)) (by omega)⟩)
    (fun i i1 i2 h => by
      rcases h with h | h | h
      · exact hQmk 0 i ((hQ0 i i1 i2).mp h)
      · exact hQmk 1 i ((hQ1 i i1 i2).mp h)
      · exact hQmk 2 i ((hQ2 i i1 i2).mp h))
  set mS := sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo (hi - lo) with hmS
  clear_value mS
  have SM1' : ∀ x, ¬ (S.bACT + lo ≤ x ∧ x < S.bACT + e3) → ¬ (S.bPOS ≤ x ∧ x < S.bPOS + S.μ) →
      mS x = m2 x := by
    rw [he3, he2, he1]; exact SM1
  -- uniform statements
  have hA : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      mS (S.bACT + (E t + cntS (Q t) lo i)) = m (S.bACT + i) := by
    intro t ht i i1 i2 h
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · rw [hE0, ← hc0 i (by omega)]; exact SM2 i i1 i2 ((hQ0 i i1 i2).mpr h)
    · rw [hE1, ← hc1 i (by omega), he1]; exact SM3 i i1 i2 ((hQ1 i i1 i2).mpr h)
    · rw [hE2, ← hc2 i (by omega), he2, he1]; exact SM4 i i1 i2 ((hQ2 i i1 i2).mpr h)
  have hP : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      mS (S.bPOS + m (S.bACT + i)) = E t + cntS (Q t) lo i := by
    intro t ht i i1 i2 h
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · rw [hE0, ← hc0 i (by omega)]; exact SM6 i i1 i2 ((hQ0 i i1 i2).mpr h)
    · rw [hE1, ← hc1 i (by omega), he1]; exact SM7 i i1 i2 ((hQ1 i i1 i2).mpr h)
    · rw [hE2, ← hc2 i (by omega), he2, he1]; exact SM8 i i1 i2 ((hQ2 i i1 i2).mpr h)
  have hdec : ∀ t, t < 3 → ∀ x, E t ≤ x → x < E (t + 1) →
      ∃ i, lo ≤ i ∧ i < hi ∧ Q t i ∧ E t + cntS (Q t) lo i = x := by
    intro t ht x h1 h2
    rw [hEs t ht] at h2
    obtain ⟨i, i1, i2, i3, i4⟩ := cntS_surj (sel := Q t) hlh (x - E t) (by omega)
    exact ⟨i, i1, i2, i3, by omega⟩
  have hin : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      E t ≤ E t + cntS (Q t) lo i ∧ E t + cntS (Q t) lo i < E (t + 1) := by
    intro t ht i i1 i2 h
    rw [hEs t ht]
    have := cntS_lt i1 i2 h (i' := hi)
    omega
  have hloc : ∀ x, lo ≤ x → x < e3 → ∃ t, t < 3 ∧ E t ≤ x ∧ x < E (t + 1) := by
    intro x h1 h2
    by_cases c1 : x < E 1
    · exact ⟨0, by omega, by rwx [hE0], c1⟩
    · by_cases c2 : x < E 2
      · exact ⟨1, by omega, by omega, c2⟩
      · exact ⟨2, by omega, by omega, by rwx [hE3]⟩
  -- the pushes
  have hstk0 : rest = stkList m S.bSTK rest.length := by
    have h := hD.stack
    rw [List.length_cons, stkList] at h
    exact (List.cons.inj h).2
  have hrest : rest = stkList mS S.bSTK rest.length := by
    rw [stkList_congr _ (fun x h1 h2 => ?_)]
    · exact hstk0
    · rw [SM1' x (by omega) (by omega), h2o x (by omega) (by omega)]
  have P1 := pushF_stk (bS := S.bSTK) (s := S.s) (a := lo) (b := e1) (q := (mS, tp)) hrest htp
  have P2 := pushF_stk (bS := S.bSTK) (s := S.s) (a := e1) (b := e2) P1.1 P1.2.1
  have P3 := pushF_stk (bS := S.bSTK) (s := S.s) (a := e2) (b := e3) P2.1 P2.2.1
  rw [← hq] at P3
  set news := optSeg S.s e2 e3 ++ optSeg S.s e1 e2 ++ optSeg S.s lo e1 with hnews_def
  have hL3 : optSeg S.s e2 e3 ++ (optSeg S.s e1 e2 ++ (optSeg S.s lo e1 ++ rest)) =
      news ++ rest := by simp only [hnews_def, List.append_assoc]
  rw [hL3] at P3
  have hlo1 : ∀ a b, (optSeg S.s a b).length ≤ 1 := by
    intro a b; unfold optSeg; split_ifs <;> simp
  have hlen1 := hlo1 lo e1; have hlen2 := hlo1 e1 e2; have hlen3 := hlo1 e2 e3
  have hlenN : (news ++ rest).length ≤ rest.length + 3 := by
    sio only [hnews_def, List.length_append]
  have hqS : ∀ x, (x < S.bSTK ∨ S.bSTK + 2 * U ≤ x) → q.1 x = mS x := by
    intro x hx
    have l1 : (optSeg S.s lo e1 ++ rest).length ≤ rest.length + 3 := by
      sio only [List.length_append]
    have l2 : (optSeg S.s e1 e2 ++ (optSeg S.s lo e1 ++ rest)).length ≤ rest.length + 3 := by
      sio only [List.length_append]
    rw [P3.2.2 x (by omega), P2.2.2 x (by omega), P1.2.2 x (by omega)]
  have hact_out : ∀ i, i < μ → (i < lo ∨ e3 ≤ i) → q.1 (S.bACT + i) = m (S.bACT + i) := by
    intro i h1 h2
    rw [hqS _ (Or.inl (by omega)), SM1' _ (by omega) (by omega), h2o _ (by omega) (by omega)]
  have hact_in : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      q.1 (S.bACT + (E t + cntS (Q t) lo i)) = m (S.bACT + i) := by
    intro t ht i i1 i2 h
    have := hin t ht i i1 i2 h
    have := (hEle (t + 1) (by omega)).2
    rw [hqS _ (Or.inl (by omega))]
    exact hA t ht i i1 i2 h
  have hpos' : ∀ w, w < μ → q.1 (S.bPOS + w) = mS (S.bPOS + w) :=
    fun w hw => hqS _ (Or.inl (by omega))
  have hdf' : ∀ y, y < μ → q.1 (S.bDF + y) = m2 (S.bDF + y) := by
    intro y hy
    rw [hqS _ (Or.inr (by omega)), SM1' _ (by omega) (by omega)]
  have hstat : StaticEq A0 U m q.1 := by
    intro x hx
    rw [hqS _ (by omega), SM1' _ (by omega) (by omega), h2o _ (by omega) (by omega)]
  -- the split
  have hdec' : ∀ x, lo ≤ x → x < e3 → ∃ t i, t < 3 ∧ lo ≤ i ∧ i < hi ∧ Q t i ∧
      E t + cntS (Q t) lo i = x ∧ q.1 (S.bACT + x) = m (S.bACT + i) := by
    intro x h1 h2
    obtain ⟨t, ht, hx1, hx2⟩ := hloc x h1 h2
    obtain ⟨i, i1, i2, i3, i4⟩ := hdec t ht x hx1 hx2
    exact ⟨t, i, ht, i1, i2, i3, i4, by rw [← i4]; exact hact_in t ht i i1 i2 i3⟩
  set sep := (items (fun i => m (S.bACT + i)) (lo, hi)).filter (fun v => markN T a f v)
    with hsep
  have hSplit : SplitOK (μ := μ) (k := k) (Adj := AdjN M) (fun i => m (S.bACT + i))
      (fun i => q.1 (S.bACT + i)) (lo, hi) E sep := by
    refine ⟨fun i h hi' => hact_out i hi' (by rcases h with h | h; left; exact h; right; omega),
      le_rfl, fun t ht => by rwo [hEs t ht], he3hi, ?_, Finset.filter_subset _ _,
      ?_, ?_, fun t ht => ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
      obtain ⟨t, i, ht, i1, i2, i3, i4, i5⟩ := hdec' x hx.1 hx.2
      obtain ⟨t', i', ht', j1, j2, j3, j4, j5⟩ := hdec' y hy.1 hy.2
      simp only at hxy
      rw [i5, j5] at hxy
      have := hinj i i' i1 i2 j1 j2 hxy
      subst this
      have := hQu i i1 i2 t t' ht ht' i3 j3
      subst this
      omega
    · intro v hv hs
      obtain ⟨i, i1, i2, rfl⟩ := mem_items.mp hv
      have hmk : ¬ markN T a f (m (S.bACT + i)) := fun h =>
        hs (Finset.mem_filter.mpr ⟨hv, h⟩)
      obtain ⟨t, ht, hQt⟩ := Ccov i i1 i2 hmk
      have := hin t ht i i1 i2 hQt
      exact ⟨t, ht, mem_items.mpr ⟨_, this.1, this.2, hact_in t ht i i1 i2 hQt⟩⟩
    · intro t ht v hv
      obtain ⟨x, h1, h2, rfl⟩ := mem_items.mp hv
      obtain ⟨i, i1, i2, i3, i4⟩ := hdec t ht x h1 h2
      show q.1 (S.bACT + x) ∈ _ ∧ _
      rw [← i4, hact_in t ht i i1 i2 i3]
      exact ⟨hmem i i1 i2, fun hs => hQmk t i i3 (Finset.mem_filter.mp hs).2⟩
    · have hCh : 2 * cntS (Q t) lo hi ≤ hi - lo := Chalf t ht
      unfold len
      simp only
      rw [hEs t ht]
      omega
    · rintro x y ⟨d, hd1, hd2⟩ t t' ht ht' hx hy
      obtain ⟨x', h1, h2, hx'⟩ := mem_items.mp hx
      obtain ⟨y', h3, h4, hy'⟩ := mem_items.mp hy
      obtain ⟨i, i1, i2, i3, i4⟩ := hdec t ht x' h1 h2
      obtain ⟨i', j1, j2, j3, j4⟩ := hdec t' ht' y' h3 h4
      change q.1 (S.bACT + x') = x at hx'
      change q.1 (S.bACT + y') = y at hy'
      rw [← i4, hact_in t ht i i1 i2 i3] at hx'
      rw [← j4, hact_in t' ht' i' j1 j2 j3] at hy'
      refine Cedge d t t' ht ht' ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [hd1, ← hx']; exact hmem i i1 i2
      · have : (M.vert d : ℕ) = m (S.bACT + i) := by rw [hd1, hx']
        rwx [this]
      · rw [hd2, ← hy']; exact hmem i' j1 j2
      · have : (M.head d : ℕ) = m (S.bACT + i') := by rw [hd2, hy']
        rwx [this]
    · have hv0 := hmem lo le_rfl (by omega)
      refine card_mark_le (T := T) (a := a) (ha := ha) f _ (hD.sinv.lt _ hlv) c
        (slabN T c k (m (S.bACT + lo))) k (fun v hv => ?_)
      have hsl := hD.sinv.inslab _ hlv v hv _ hv0
      have e : slabN T c k v = (T.level ⟨v, hD.sinv.lt _ hlv v hv⟩ + c) / k := dite_eq_left _
      rw [← hsl, e]
      exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hk⟩
  -- the new stack entries
  have hnews : ∀ p, p ∈ news ↔ ∃ t, t < 3 ∧ p = scls E t ∧ S.s < len p := by
    intro p
    constructor
    · intro h
      simp only [hnews_def, List.mem_append, mem_optSeg] at h
      rcases h with ((⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩)
      · exact ⟨2, by omega, rfl, h⟩
      · exact ⟨1, by omega, rfl, h⟩
      · exact ⟨0, by omega, rfl, h⟩
    · rintro ⟨t, ht, rfl, h⟩
      simp only [hnews_def, List.mem_append, mem_optSeg]
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inl (Or.inl ⟨rfl, h⟩)
  have hnd : news.Nodup := by
    simp only [hnews_def, optSeg]
    split_ifs <;> simp only [List.nil_append, List.append_nil, List.cons_append,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, Prod.mk.injEq, or_false, not_or, and_true,
      not_false_eq_true] <;> (try constructor) <;> (try constructor) <;>
      omega
  have SI' := SInv.split hD.sinv hSplit hnews hnd hD.rng
  set fin' := fin ∪ ((Finset.range 3).image (scls E)).filter
    (fun q => 0 < len q ∧ len q ≤ S.s) with hfin'
  -- classification of the new live segments
  have hlive : ∀ p', Lv (news ++ rest) fin' p' →
      (Lv ((lo, hi) :: rest) fin p' ∧ p' ≠ (lo, hi)) ∨
        ∃ t, t < 3 ∧ p' = scls E t ∧ 0 < len p' := by
    intro p' hq
    rcases hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨t, ht, rfl, hb⟩ := (hnews _).mp hq
        exact Or.inr ⟨t, ht, rfl, by omega⟩
      · refine Or.inl ⟨Or.inl (List.mem_cons_of_mem _ hq), fun h => ?_⟩
        subst h
        exact (List.nodup_cons.mp hD.sinv.nodup).1 hq
    · rcases Finset.mem_union.mp hq with hq | hq
      · refine Or.inl ⟨Or.inr hq, fun h => ?_⟩
        subst h
        exact hD.sinv.sf _ List.mem_cons_self hq
      · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq1
        exact Or.inr ⟨t, Finset.mem_range.mp ht, rfl, hq2.1⟩
  have hcls_live : ∀ t, t < 3 → 0 < len (scls E t) → Lv (news ++ rest) fin' (scls E t) := by
    intro t ht hl
    by_cases hs : S.s < len (scls E t)
    · exact Or.inl (List.mem_append_left _ ((hnews _).mpr ⟨t, ht, rfl, hs⟩))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩, hl, by omega⟩))
  have hold_pos : ∀ p', Lv ((lo, hi) :: rest) fin p' → p' ≠ (lo, hi) → ∀ i, p'.1 ≤ i →
      i < p'.2 → (i < lo ∨ hi ≤ i) ∧ i < μ := by
    intro p' hp' hne i h1 h2
    have := hD.rng p' hp'
    refine ⟨?_, by omega⟩
    rcases hD.sinv.rdisj p' (lo, hi) hp' hlv hne with h | h | h | h
    · left; sio only at h
    · right; sio only at h
    · omega
    · sio only at h
  -- the keys
  have hkey : ∀ i v, q.1 (S.bACT + i) = v → v < μ →
      keyOf q.1 S.bACT S.bFIRST S.bFPRE i = m (S.bFPRE + m (S.bFIRST + v)) := by
    intro i v h hv
    have hf := hSF.first ⟨v, hv⟩
    simp only at hf
    have hfN : m (S.bFIRST + v) < N := by rw [hf]; exact Fin.isLt _
    unfold keyOf
    rw [h, hstat (S.bFIRST + v) (Or.inl (by omega)), hstat _ (Or.inl (by omega))]
  refine ⟨news, fin', D ∪ sep, ⟨SI', ?_, ?_, ?_, ?_, ?_, P3.1, ?_⟩, P3.2.1, hstat, ?_⟩
  · -- the separator flags
    intro v hv
    rw [hdf' v hv, h2d v hv, Finset.mem_union]
    by_cases hc : v ∈ items (fun i => m (S.bACT + i)) (lo, hi) ∧ markN T a f v
    · rw [ite_eq_left hc]
      exact ⟨fun _ => Or.inr (Finset.mem_filter.mpr hc), fun _ => rfl⟩
    · rw [ite_eq_right hc, hD.df v hv]
      exact ⟨Or.inl, fun h => h.elim id (fun h' => absurd (Finset.mem_filter.mp h') hc)⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hD.Dlt v h
    · exact hD.sinv.lt _ hlv v (Finset.mem_filter.mp h).1
  · -- the positions of the live items
    intro p' hp' i h1 h2
    rcases hlive p' hp' with ⟨hold, hne⟩ | ⟨t, ht, rfl, hlen⟩
    · obtain ⟨hio, hiμ⟩ := hold_pos p' hold hne i h1 h2
      rw [hact_out i hiμ (by omega)]
      have hw : m (S.bACT + i) < μ := hD.sinv.lt p' hold _ (mem_items.mpr ⟨i, h1, h2, rfl⟩)
      have hpi := hD.pos_in p' hold i h1 h2
      rw [hpos' _ hw, SM9 _ (by rwx [hμ]) (fun j j1 j2 e => ?_),
        h2o _ (by omega) (by omega)]
      · exact hpi
      · have := hD.pos_in _ hlv j j1 j2
        rw [e, hpi] at this
        omega
    · obtain ⟨j, j1, j2, j3, j4⟩ := hdec t ht i h1 h2
      rw [← j4, hact_in t ht j j1 j2 j3, hpos' _ (hactμ j j1 j2), hP t ht j j1 j2 j3]
  · -- the positions of all vertices
    intro w hw
    rw [hpos' w hw]
    by_cases hex : ∃ j, lo ≤ j ∧ j < hi ∧ m (S.bACT + j) = w
    · obtain ⟨j, j1, j2, rfl⟩ := hex
      by_cases hmk : markN T a f (m (S.bACT + j))
      · left; rw [SM5 j j1 j2 hmk, hμ]
      · right
        obtain ⟨t, ht, hQt⟩ := Ccov j j1 j2 hmk
        have hi' := hin t ht j j1 j2 hQt
        rw [hP t ht j j1 j2 hQt]
        exact ⟨scls E t, hcls_live t ht (by ufo len scls), hi'.1, hi'.2,
          hact_in t ht j j1 j2 hQt⟩
    · rw [SM9 w (by rwx [hμ]) (fun j j1 j2 e => hex ⟨j, j1, j2, e⟩),
        h2o _ (by omega) (by omega)]
      rcases hD.pos_out w hw with h | ⟨p'', hp'', h1, h2, h3⟩
      · exact Or.inl h
      · right
        have hne : p'' ≠ (lo, hi) := by
          rintro rfl
          exact hex ⟨_, h1, h2, h3⟩
        have hlv' : Lv (news ++ rest) fin' p'' := by
          rcases hp'' with h | h
          · rcases List.mem_cons.mp h with h | h
            · exact absurd h hne
            · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr (Finset.mem_union_left _ h)
        obtain ⟨hio, hiμ⟩ := hold_pos p'' hp'' hne _ h1 h2
        exact ⟨p'', hlv', h1, h2, by rwx [hact_out _ hiμ (by omega)]⟩
  · -- the stack entries are sorted
    intro p' hp' i i' h1 h2 h3
    rcases List.mem_append.mp hp' with hn | hr
    · obtain ⟨t, ht, rfl, -⟩ := (hnews _).mp hn
      change E t ≤ i at h1
      change i' < E (t + 1) at h3
      obtain ⟨j, j1, j2, j3, j4⟩ := hdec t ht i h1 (by omega)
      obtain ⟨j', j1', j2', j3', j4'⟩ := hdec t ht i' (by omega) h3
      have hjj : j ≤ j' := by
        by_contra hc
        have := cntS_lt j1' (show j' < j by omega) j3'
        omega
      rw [hkey i _ (by rw [← j4]; exact hact_in t ht j j1 j2 j3) (hactμ j j1 j2),
        hkey i' _ (by rw [← j4']; exact hact_in t ht j' j1' j2' j3') (hactμ j' j1' j2')]
      exact hD.sorted _ List.mem_cons_self j j' j1 hjj j2'
    · have hold : Lv ((lo, hi) :: rest) fin p' := Or.inl (List.mem_cons_of_mem _ hr)
      have hne : p' ≠ (lo, hi) := by
        rintro rfl
        exact (List.nodup_cons.mp hD.sinv.nodup).1 hr
      obtain ⟨hio, hiμ⟩ := hold_pos p' hold hne i h1 (by omega)
      obtain ⟨hio', hiμ'⟩ := hold_pos p' hold hne i' (by omega) h3
      have hw := hD.sinv.lt p' hold _ (mem_items.mpr ⟨i, h1, by omega, rfl⟩)
      have hw' := hD.sinv.lt p' hold _ (mem_items.mpr ⟨i', by omega, h3, rfl⟩)
      rw [hkey i _ (hact_out i hiμ (by omega)) hw, hkey i' _ (hact_out i' hiμ' (by omega)) hw']
      exact hD.sorted p' (List.mem_cons_of_mem _ hr) i i' h1 h2 h3
  · -- the ranges
    intro p' hp'
    rcases hlive p' hp' with ⟨h, -⟩ | ⟨t, ht, rfl, -⟩
    · exact hD.rng _ h
    · have := (hEle (t + 1) (by omega)).2
      show E (t + 1) ≤ μ
      omega
  · -- the size potential
    have hsum3 : (news.map (fun p => len p * Nat.size (len p))).sum ≤
        len (e2, e3) * Nat.size (len (e2, e3)) + len (e1, e2) * Nat.size (len (e1, e2)) +
          len (lo, e1) * Nat.size (len (lo, e1)) := by
      simp only [hnews_def, List.map_append, List.sum_append]
      have := sum_optSeg (fun p => len p * Nat.size (len p)) S.s e2 e3
      have := sum_optSeg (fun p => len p * Nat.size (len p)) S.s e1 e2
      have := sum_optSeg (fun p => len p * Nat.size (len p)) S.s lo e1
      omega
    have hpot := split_size_pot (fun t => len (scls E t)) (hi - lo) (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      show 0 + (e1 - lo) + (e2 - e1) + (e3 - e2) ≤ hi - lo
      omega) (fun t ht => by
      have hCh : 2 * cntS (Q t) lo hi ≤ hi - lo := Chalf t ht
      show 2 * (E (t + 1) - E t) ≤ hi - lo
      rwo [hEs t ht])
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hpot
    have e0 : scls E 0 = (lo, e1) := rfl
    have e1' : scls E 1 = (e1, e2) := rfl
    have e2' : scls E 2 = (e2, e3) := rfl
    rw [e0, e1', e2'] at hpot
    omega

end step

end

end Chazelle.Core.Cluster
