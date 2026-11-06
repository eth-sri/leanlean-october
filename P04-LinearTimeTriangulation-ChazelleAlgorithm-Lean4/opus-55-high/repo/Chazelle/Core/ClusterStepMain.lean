module

public import Chazelle.MacT
public import Chazelle.Core.ClusterSplitRam
public import Chazelle.Core.ClusterPrimal
public import Chazelle.Core.ClusterEulerRam
public import Chazelle.Core.NFDecompBfs
public import Mathlib.Tactic.IntervalCases

namespace Chazelle.Core.Cluster
open Chazelle.Separator Chazelle.Separator.CombMap
@[expose] public section
def e4 (a b c d : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d
theorem mem_optSeg {s a b : ℕ} {q : ℕ × ℕ} : q ∈ optSeg s a b ↔ q = ztvk ∧ s < b - a := by
  unfold optSeg
  grind
theorem sum_optSeg (g : ℕ × ℕ → ℕ) (s a b : ℕ) : ((optSeg s a b).map g).sum ≤ g ztvk := by
  unfold optSeg; grind
section step
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}
open Classical in
/-- **One split step preserves the driver invariant.** -/
theorem dinv_split {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List ztw}
    {fin : Finset ztw} {D : Finset ℕ} {nsp tp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m (ztdz :: rest) fin D nsp) (htp : tp = 2 * rest.length)
    (hk : 0 < k) {lbot ltop : ℕ}
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items ztwjj ztdz →
      lbot ≤ T.level x ∧ T.level x ≤ ltop) (f : Fin N)
    (hgood : Good C ztdhe
      (liftP (μ := μ) (F := F) ztbamd) f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C ztdhe
      (liftP (μ := μ) (F := F) ztbamd) g)
    {m2 : ℕ → ℕ} (hm2 : m2 = copyF ztftg S lo hi) :
    let s0 := SelI m2 S f f
    let s1 := SelI m2 S ztwmt f
    let s2 := SelI m2 S ztbpq f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    let q := pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2 (pushF S.bSTK S.s lo e1
      (sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo ztcw, tp)))
    cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo ∧
    ∃ news fin' D', DInv M T k c S q.1 ztcny fin' D' ztodu ∧
      q.2 = 2 * (news ++ rest).length ∧ StaticEq A0 U m q.1 ∧
      (news.map ztbep).sum + ztcw ≤
        ztcw * Nat.size ztcw := by
  intro s0 s1 s2 e1 e2 e3 q
  have hq : q = pushF S.bSTK S.s e2 e3 _ := rfl
  have hs0 : s0 = SelI m2 S f f := rfl
  have hs1 : s1 = SelI m2 S _ f := rfl
  have hs2 : s2 = SelI m2 S _ f := rfl
  zudda

  clear_value q e3 e2 e1
  -- the facts of the segment
  zuglp
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU
  have := hL.hSTK; have := hL.hFIRST; have := hL.hFPRE; have := hL.hNU
  zuhfx
  zuerh
  zukcj
  have hlh : lo ≤ hi := hD.sinv.wf _ hlv
  zuhyc
  have hmem : ∀ i, lo ≤ i → i < hi →
      m _ ∈ items ztwjj ztdz :=
    fun i i1 i2 => mem_items.mpr ztoou
  have hactμ : ztieh :=
    fun i i1 i2 => hD.sinv.lt _ hlv _ ztlpt
  have hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi →
      m ztde = m ztjme → i = i' := by
    intro i i' a b c d e
    exact hD.sinv.inj _ hlv by_grind by_grind e
  have hnD : ∀ i, lo ≤ i → i < hi → m _ ∉ D :=
    fun i i1 i2 => (hD.sinv.off _ hlv _ ztlpt).1
  zufvh

  -- the memory after the marks and the copy
  obtain ⟨h2o, h2tmp, h2d, h2fp⟩ := m2_facts hSF hD hwin f
  rw [← hm2] at h2o h2tmp h2d h2fp
  obtain ⟨Sel0, Sel1, Sel2⟩ := sel_iff hSF hD hwin f
  rw [← hm2] at Sel0 Sel1 Sel2
  obtain ⟨Ccov, Cuniq, Chalf, Cedge⟩ := cls_facts hSF hD hgood hch
  -- the class predicates
  set Q : ℕ → ℕ → Prop := fun t i => QC m S T a f t ztwsd with hQ
  have hQ0 : ∀ i, lo ≤ i → i < hi → (s0 i ↔ Q 0 i) := by_omega
  have hQ1 : ∀ i, lo ≤ i → i < hi → (s1 i ↔ Q 1 i) := by_omega
  have hQ2 : ∀ i, lo ≤ i → i < hi → (s2 i ↔ Q 2 i) := by_omega
  have hc0 : ∀ x, x ≤ hi → cntS s0 lo x = cntS _ lo x :=
    fun x hx => cntS_congr (fun i i1 i2 => hQ0 i i1 by_omega)
  have hc1 : ∀ x, x ≤ hi → cntS s1 lo x = cntS _ lo x :=
    fun x hx => cntS_congr (fun i i1 i2 => hQ1 i i1 by_omega)
  have hc2 : ∀ x, x ≤ hi → cntS s2 lo x = cntS _ lo x :=
    fun x hx => cntS_congr (fun i i1 i2 => hQ2 i i1 by_omega)
  have hQmk : ∀ t i, Q t i → ¬ markN T a f _ := fun t i h => h.1
  have hQu : ∀ i, lo ≤ i → i < hi → ∀ t t', t < 3 → t' < 3 → Q t i → Q t' i → t = t' :=
    by omega
  -- the sum of the classes
  have hsum : ztym := by
    refine cntS3_le (fun i i1 i2 => ⟨fun ⟨x, y⟩ => ?_, fun ⟨x, y⟩ => ?_, fun ⟨x, y⟩ => ?_⟩)
    · exact absurd (hQu i i1 i2 0 1 by_omega by_omega ztdxv ztlzk)
        by_omega
    · exact absurd (hQu i i1 i2 0 2 by_omega by_omega ztdxv ztdxw)
        by_omega
    · exact absurd (hQu i i1 i2 1 2 by_omega by_omega ztlzj ztdxw)
        by_omega
  refine ⟨hsum, ?_⟩
  -- the boundaries
  set E := e4 lo e1 e2 e3 with hE
  have hE0 : E 0 = lo := rfl
  have hE1 : E 1 = e1 := rfl
  have hE2 : E 2 = e2 := rfl
  have hE3 : E 3 = e3 := rfl
  have hEs : ∀ t, t < 3 → E ztbx = E t + cntS ztdyt lo hi := by
    zucj
    zublm
    · rw [hE0, hE1, he1, hc0 hi le_rfl]
    · rw [hE1, hE2, he2, hc1 hi le_rfl]
    · rw [hE2, hE3, he3, hc2 hi le_rfl]
  have he3hi : e3 ≤ hi := by_omega
  have hEle : ∀ t, t ≤ 3 → lo ≤ E t ∧ E t ≤ e3 := by
    zucj
    have := hEs 0 by_omega; have := hEs 1 by_omega; have := hEs 2 by_omega
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
  -- the memory after the passes and the release
  have h2df : ∀ i, lo ≤ i → i < hi →
      (m2 ztxnb = 1 ↔ markN T a f ztwsd) := by
    intro i i1 i2
    rw [h2d _ ztrrq]
    by_cases hmk : markN T a f ztwsd
    · rw [ite_eq_left ⟨hmem i i1 i2, hmk⟩]; simp [hmk]
    · rw [ite_eq_right (fun h => hmk h.2)]
      exact ⟨fun h => absurd ((hD.df _ ztrrq).mp h) (hnD i i1 i2), fun h => absurd h hmk⟩
  obtain ⟨SM1, SM2, SM3, SM4, SM5, SM6, SM7, SM8, SM9, SM10⟩ := stepMem hL (f := f)
    (mk := fun i => markN T a f ztwsd) hlh by_omega
    (fun i i1 i2 => by zvnhc; exact hactμ i i1 i2) hinj h2tmp h2df hsum
    (fun i i1 i2 => ⟨fun ⟨x, y⟩ => absurd (hQu i i1 i2 0 1 by_omega by_omega ztdxv
        ztlzk) by_omega,
      fun ⟨x, y⟩ => absurd (hQu i i1 i2 0 2 by_omega by_omega ztdxv
        ztdxw) by_omega,
      fun ⟨x, y⟩ => absurd (hQu i i1 i2 1 2 by_omega by_omega ztlzj
        ztdxw) by_omega⟩)
    (fun i i1 i2 h => by
      zude
      · exact hQmk 0 i ((hQ0 i i1 i2).mp h)
      · exact hQmk 1 i ((hQ1 i i1 i2).mp h)
      · exact hQmk 2 i ((hQ2 i i1 i2).mp h))
  set mS := sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo ztcw with hmS
  clear_value mS
  have SM1' : ∀ x, ¬ ztjmf → ¬ ztclw →
      mS x = m2 x := by
    rw [he3, he2, he1]; omega
  -- uniform statements
  have hA : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      mS ztxvw = m ztde := by
    zucxg
    zublm
    · zunuv; exact SM2 i i1 i2 ztlzi
    · zunoa; exact SM3 i i1 i2 ztlzl
    · zunjo; exact SM4 i i1 i2 ztlzm
  have hP : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      mS ztwxy = E t + cntS ztdyt lo i := by
    zucxg
    zublm
    · zunuv; exact SM6 i i1 i2 ztlzi
    · zunoa; exact SM7 i i1 i2 ztlzl
    · zunjo; exact SM8 i i1 i2 ztlzm
  have hdec : ∀ t, t < 3 → ∀ x, E t ≤ x → x < E ztbx →
      ∃ i, lo ≤ i ∧ i < hi ∧ Q t i ∧ E t + cntS ztdyt lo i = x := by
    intro t ht x h1 h2
    rw [hEs t ht] at h2
    obtain ⟨i, i1, i2, i3, i4⟩ := cntS_surj (sel := Q t) hlh (x - E t) by_omega
    exact ⟨i, i1, i2, i3, by_omega⟩
  have hin : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      E t ≤ E t + cntS ztdyt lo i ∧ E t + cntS ztdyt lo i < E ztbx := by
    zucxg
    zuksk
    have := cntS_lt i1 i2 h
    omega
  have hloc : ∀ x, lo ≤ x → x < e3 → ∃ t, t < 3 ∧ E t ≤ x ∧ x < E ztbx := by
    zuchi
    by_cases c1 : x < E 1
    · exact ⟨0, by_omega, by_omega, c1⟩
    · by_cases c2 : x < E 2
      · exact ⟨1, by_omega, by_omega, c2⟩
      · exact ⟨2, by_omega, by_omega, by rw [hE3]; exact h2⟩
  -- the pushes
  have hstk0 : rest = stkList m S.bSTK rest.length := by
    have h := hD.stack
    rw [List.length_cons, stkList] at h
    exact (List.cons.inj h).2
  have hrest : rest = stkList mS S.bSTK rest.length := by
    rw [stkList_congr _ (fun x h1 h2 => ?_)]
    · omega
    · rw [SM1' x by_omega by_omega, h2o x by_omega by_omega]
  have P1 := pushF_stk (s := S.s) (a := lo) (b := e1) (q := (mS, tp)) hrest htp
  have P2 := pushF_stk (s := S.s) (a := e1) (b := e2) P1.1 P1.2.1
  have P3 := pushF_stk (s := S.s) (a := e2) (b := e3) P2.1 P2.2.1
  rw [← hq] at P3
  set news := optSeg S.s e2 e3 ++ optSeg S.s e1 e2 ++ optSeg S.s lo e1 with hnews_def
  have hL3 : optSeg S.s e2 e3 ++ (optSeg S.s e1 e2 ++ ztodx) =
      news ++ rest := by simp only [hnews_def, List.append_assoc]
  rw [hL3] at P3
  have hlo1 : ∀ a b, (optSeg S.s a b).length ≤ 1 := by
    intro a b; unfold optSeg; split_ifs <;> simp
  have hlen1 := hlo1 lo e1; have hlen2 := hlo1 e1 e2; have hlen3 := hlo1 e2 e3
  have hlenN : (news ++ rest).length ≤ rest.length + 3 := by
    simp only [hnews_def, List.length_append]; omega
  have hqS : ∀ x, (x < S.bSTK ∨ S.bSTK + 2 * U ≤ x) → q.1 x = mS x := by
    zuh
    have l1 : (optSeg S.s lo e1 ++ rest).length ≤ rest.length + 3 := by
      zufaz
    have l2 : (optSeg S.s e1 e2 ++ ztodx).length ≤ rest.length + 3 := by
      zufaz
    rw [P3.2.2 x by_omega, P2.2.2 x by_omega, P1.2.2 x by_omega]
  have hact_out : ∀ i, i < μ → (i < lo ∨ e3 ≤ i) → q.1 ztde = m ztde := by
    zusx
    zudun
  have hact_in : ∀ t, t < 3 → ∀ i, lo ≤ i → i < hi → Q t i →
      q.1 ztxvw = m ztde := by
    zucxg
    have := hin t ht i i1 i2 h
    have := (hEle ztbx by_omega).2
    rw [hqS _ by_omega]
    exact hA t ht i i1 i2 h
  have hpos' : ∀ w, w < μ → q.1 _ = mS zteob :=
    fun w hw => hqS _ by_omega
  have hdf' : ∀ y, y < μ → q.1 ztjmi = m2 ztjmi := by
    zusy
    rw [hqS _ by_omega, SM1' _ by_omega by_omega]
  have hstat : StaticEq A0 U m q.1 := by
    zuh
    zudun
  -- the split
  have hdec' : ∀ x, lo ≤ x → x < e3 → ∃ t i, t < 3 ∧ lo ≤ i ∧ i < hi ∧ Q t i ∧
      E t + cntS ztdyt lo i = x ∧ q.1 (S.bACT + x) = m ztde := by
    zuchi
    obtain ⟨t, ht, hx1, hx2⟩ := hloc x h1 h2
    obtain ⟨i, i1, i2, i3, i4⟩ := hdec t ht x hx1 hx2
    exact ⟨t, i, ht, i1, i2, i3, i4, by rw [← i4]; exact hact_in t ht i i1 i2 i3⟩
  set sep := (items ztwjj ztdz).filter ztmjy
    with hsep
  have hSplit : SplitOK (μ := μ) (k := k) (Adj := AdjN M) ztwjj
      (fun i => q.1 ztde) ztdz E sep := by
    refine ⟨fun i h hi' => hact_out i hi' by_omega,
      le_rfl, fun t ht => by rw [hEs t ht]; omega, he3hi, ?_, Finset.filter_subset _ _,
      ?_, ?_, fun t ht => ?_, ?_, ?_⟩
    · zuvc
      zugzc
      obtain ⟨t, i, ht, i1, i2, i3, i4, i5⟩ := hdec' x hx.1 hx.2
      obtain ⟨t', i', ht', j1, j2, j3, j4, j5⟩ := hdec' y hy.1 hy.2
      zumpu
      rw [i5, j5] at hxy
      have := hinj i i' i1 i2 j1 j2 hxy
      zumo
      have := hQu i i1 i2 t t' ht ht' i3 j3
      zumo
      omega
    · intro v hv hs
      obtain ⟨i, i1, i2, rfl⟩ := mem_items.mp hv
      have hmk : ¬ markN T a f _ := fun h =>
        hs (Finset.mem_filter.mpr ⟨hv, h⟩)
      obtain ⟨t, ht, hQt⟩ := Ccov i i1 i2 hmk
      have := hin t ht i i1 i2 hQt
      exact ⟨t, ht, mem_items.mpr ⟨_, this.1, this.2, hact_in t ht i i1 i2 hQt⟩⟩
    · intro t ht v hv
      obtain ⟨x, h1, h2, rfl⟩ := mem_items.mp hv
      obtain ⟨i, i1, i2, i3, i4⟩ := hdec t ht x h1 h2
      show q.1 _ ∈ _ ∧ _
      rw [← i4, hact_in t ht i i1 i2 i3]
      exact ⟨hmem i i1 i2, fun hs => hQmk t i i3 (Finset.mem_filter.mp hs).2⟩
    · zuhwp
      unfold len
      zubi
      zuksk
      omega
    · rintro x y ⟨d, hd1, hd2⟩ t t' ht ht' hx hy
      obtain ⟨x', h1, h2, hx'⟩ := mem_items.mp hx
      obtain ⟨y', h3, h4, hy'⟩ := mem_items.mp hy
      obtain ⟨i, i1, i2, i3, i4⟩ := hdec t ht x' h1 h2
      obtain ⟨i', j1, j2, j3, j4⟩ := hdec t' ht' y' h3 h4
      change q.1 _ = x at hx'
      change q.1 _ = y at hy'
      rw [← i4, hact_in t ht i i1 i2 i3] at hx'
      rw [← j4, hact_in t' ht' i' j1 j2 j3] at hy'
      refine Cedge d t t' ht ht' ztcp ztcp
      · rw [hd1, ← hx']; exact hmem i i1 i2
      · have : (M.vert d : ℕ) = m ztde := by_omega
        zvmwk; exact i3
      · rw [hd2, ← hy']; exact hmem i' j1 j2
      · have : (M.head d : ℕ) = m ztjme := by_omega
        zvmwk; exact j3
    · have hv0 := hmem lo le_rfl by_omega
      refine card_mark_le (ha := ha) f _ zttmd c
        (slabN T c k (m zttcc)) k ztest
      have hsl := hD.sinv.inslab _ hlv v hv _ hv0
      have e : slabN T c k v = (T.level ⟨v, hD.sinv.lt _ hlv v hv⟩ + c) / k := dite_eq_left _
      rw [← hsl, e]
      exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hk⟩
  -- the new stack entries
  have hnews : ∀ p, p ∈ news ↔ ∃ t, t < 3 ∧ p = scls E t ∧ S.s < len p := by
    zukjq
    constructor
    · zuq
      simp only [hnews_def, List.mem_append, mem_optSeg] at h
      rcases h with ((⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩)
      · exact ⟨2, by_omega, rfl, h⟩
      · exact ⟨1, by_omega, rfl, h⟩
      · exact ⟨0, by_omega, rfl, h⟩
    · rintro ⟨t, ht, rfl, h⟩
      simp only [hnews_def, List.mem_append, mem_optSeg]
      zublm
      · exact Or.inr ztcfr
      · exact Or.inl ztxvs
      · exact Or.inl ztyhv
  have hnd : news.Nodup := by
    simp only [hnews_def, optSeg]
    split_ifs <;> simp only [List.nil_append, List.append_nil, List.cons_append,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, Prod.mk.injEq, or_false, not_or, and_true,
      not_false_eq_true] <;> (try constructor) <;> (try constructor) <;>
      omega
  have SI' := SInv.split hD.sinv hSplit hnews hnd hD.rng
  set fin' := fin ∪ ((Finset.range 3).image _).filter
    (fun q => 0 < len q ∧ len q ≤ S.s) with hfin'
  -- classification of the new live segments
  have hlive : ∀ p', Lv ztcny fin' p' →
      (Lv (ztdz :: rest) fin p' ∧ p' ≠ ztdz) ∨
        ∃ t, t < 3 ∧ p' = scls E t ∧ 0 < len p' := by
    intro p' hq
    zubht
    · zucyk
      · obtain ⟨t, ht, rfl, hb⟩ := (hnews _).mp hq
        exact Or.inr ⟨t, ht, rfl, by_omega⟩
      · refine Or.inl ⟨Or.inl ztnmm, fun h => ?_⟩
        zubst
        exact (List.nodup_cons.mp hD.sinv.nodup).1 hq
    · zujci
      · refine Or.inl ztomf
        zubst
        exact hD.sinv.sf _ List.mem_cons_self hq
      · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        zufzd
        exact Or.inr ⟨t, Finset.mem_range.mp ht, rfl, hq2.1⟩
  have hcls_live : ∀ t, t < 3 → 0 < len ztket → Lv ztcny fin' ztket := by
    intro t ht hl
    by_cases hs : S.s < len ztket
    · exact Or.inl (List.mem_append_left _ ((hnews _).mpr ⟨t, ht, rfl, hs⟩))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩, hl, by_omega⟩))
  have hold_pos : ∀ p', Lv (ztdz :: rest) fin p' → p' ≠ ztdz → ∀ i, p'.1 ≤ i →
      i < p'.2 → (i < lo ∨ hi ≤ i) ∧ i < μ := by
    intro p' hp' hne i h1 h2
    have := hD.rng p' hp'
    refine ztdiv
    rcases hD.sinv.rdisj p' ztdz hp' hlv hne with h | h | h | h
    · omega
    · omega
    · omega
    omega
  -- the keys
  have hkey : ∀ i v, q.1 ztde = v → v < μ →
      keyOf q.1 S.bACT S.bFIRST S.bFPRE i = m ztzkf := by
    intro i v h hv
    have hf := hSF.first ztbbl
    zumpr
    have hfN : m ztbgv < N := by_omega
    unfold keyOf
    rw [h, hstat ztbgv by_omega, hstat _ by_omega]
  refine ⟨news, fin', D ∪ sep, ⟨SI', ?_, ?_, ?_, ?_, ?_, P3.1, ?_⟩, P3.2.1, hstat, ?_⟩
  · -- the separator flags
    zuml
    rw [hdf' v hv, h2d v hv, Finset.mem_union]
    by_cases hc : v ∈ items ztwjj ztdz ∧ markN T a f v
    · zulpw
      exact ⟨fun _ => Or.inr (Finset.mem_filter.mpr hc), by_omega⟩
    · rw [ite_eq_right hc, hD.df v hv]
      exact ⟨Or.inl, fun h => h.elim id (fun h' => absurd (Finset.mem_filter.mp h') hc)⟩
  · zuml
    rcases Finset.mem_union.mp hv with h | h
    · exact hD.Dlt v h
    · exact hD.sinv.lt _ hlv v (Finset.mem_filter.mp h).1
  · -- the positions of the live items
    intro p' hp' i h1 h2
    rcases hlive p' hp' with ⟨hold, hne⟩ | ⟨t, ht, rfl, hlen⟩
    · obtain ⟨hio, hiμ⟩ := hold_pos p' hold hne i h1 h2
      rw [hact_out i hiμ by_omega]
      have hw : m _ < μ := hD.sinv.lt p' hold _ ztbaii
      have hpi := hD.pos_in p' hold i h1 h2
      rw [hpos' _ hw, SM9 _ by_omega (fun j j1 j2 e => ?_),
        h2o _ by_omega by_omega]
      · omega
      · have := hD.pos_in _ hlv j j1 j2
        rw [e, hpi] at this
        omega
    · obtain ⟨j, j1, j2, j3, j4⟩ := hdec t ht i h1 h2
      rw [← j4, hact_in t ht j j1 j2 j3, hpos' _ ztrrr, hP t ht j j1 j2 j3]
  · -- the positions of all vertices
    zucdk
    rw [hpos' w hw]
    by_cases hex : ∃ j, lo ≤ j ∧ j < hi ∧ m zttcb = w
    · obtain ⟨j, j1, j2, rfl⟩ := hex
      by_cases hmk : markN T a f (m zttcb)
      · left; rw [SM5 j j1 j2 hmk, hμ]
      · right
        obtain ⟨t, ht, hQt⟩ := Ccov j j1 j2 hmk
        have hi' := hin t ht j j1 j2 hQt
        rw [hP t ht j j1 j2 hQt]
        exact ⟨scls E t, hcls_live t ht (by unfold len scls; omega), hi'.1, hi'.2,
          hact_in t ht j j1 j2 hQt⟩
    · rw [SM9 w by_omega (fun j j1 j2 e => hex ⟨j, j1, j2, e⟩),
        h2o _ by_omega by_omega]
      rcases hD.pos_out w hw with h | ⟨p'', hp'', h1, h2, h3⟩
      · omega
      · right
        have hne : p'' ≠ ztdz := by
          zunq
          exact hex ⟨_, h1, h2, h3⟩
        have hlv' : Lv ztcny fin' p'' := by
          rcases hp'' with h | h
          · rcases List.mem_cons.mp h with h | h
            · exact absurd h hne
            · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr (Finset.mem_union_left _ h)
        obtain ⟨hio, hiμ⟩ := hold_pos p'' hp'' hne _ h1 h2
        exact ⟨p'', hlv', h1, h2, by rw [hact_out _ hiμ by_omega]; exact h3⟩
  · -- the stack entries are sorted
    intro p' hp' i i' h1 h2 h3
    rcases List.mem_append.mp hp' with hn | hr
    · obtain ⟨t, ht, rfl, -⟩ := (hnews _).mp hn
      change E t ≤ i at h1
      change i' < E _ at h3
      obtain ⟨j, j1, j2, j3, j4⟩ := hdec t ht i h1 by_omega
      obtain ⟨j', j1', j2', j3', j4'⟩ := hdec t ht i' by_omega h3
      have hjj : j ≤ j' := by
        zukr
        have := cntS_lt j1' (show j' < j by omega) j3'
        omega
      rw [hkey i _ (by rw [← j4]; exact hact_in t ht j j1 j2 j3) ztrrr,
        hkey i' _ (by rw [← j4']; exact hact_in t ht j' j1' j2' j3') (hactμ j' j1' j2')]
      exact hD.sorted _ List.mem_cons_self j j' j1 hjj j2'
    · have hold : Lv (ztdz :: rest) fin p' := Or.inl ztszm
      have hne : p' ≠ ztdz := by
        zunq
        exact (List.nodup_cons.mp hD.sinv.nodup).1 hr
      obtain ⟨hio, hiμ⟩ := hold_pos p' hold hne i h1 by_omega
      obtain ⟨hio', hiμ'⟩ := hold_pos p' hold hne i' by_omega h3
      have hw := hD.sinv.lt p' hold _ (mem_items.mpr ⟨i, h1, by_omega, rfl⟩)
      have hw' := hD.sinv.lt p' hold _ (mem_items.mpr ⟨i', by_omega, h3, rfl⟩)
      rw [hkey i _ (hact_out i hiμ by_omega) hw, hkey i' _ (hact_out i' hiμ' by_omega) hw']
      exact hD.sorted p' ztszm i i' h1 h2 h3
  · -- the ranges
    intro p' hp'
    rcases hlive p' hp' with ⟨h, -⟩ | ⟨t, ht, rfl, -⟩
    · exact hD.rng _ h
    · have := (hEle ztbx by_omega).2
      show E _ ≤ μ
      omega
  · -- the size potential
    have hsum3 : (news.map ztbep).sum ≤
        len ztnxv * Nat.size (len ztnxv) + len ztnxu * Nat.size (len ztnxu) +
          len ztocy * Nat.size (len ztocy) := by
      simp only [hnews_def, List.map_append, List.sum_append]
      have := sum_optSeg ztbep S.s e2 e3
      have := sum_optSeg ztbep S.s e1 e2
      have := sum_optSeg ztbep S.s lo e1
      omega
    have hpot := split_size_pot (fun t => len ztket) _ (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      show 0 + (e1 - lo) + (e2 - e1) + (e3 - e2) ≤ hi - lo
      omega) (fun t ht => by
      zuhwp
      show 2 * (E _ - E t) ≤ hi - lo
      rw [hEs t ht]; omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hpot
    have e0 : scls E 0 = ztocy := rfl
    have e1' : scls E 1 = ztnxu := rfl
    have e2' : scls E 2 = ztnxv := rfl
    rw [e0, e1', e2'] at hpot
    omega
end step
open Machine Machine.Stmt Programs
theorem cntIn_congr {κ κ' : ℕ → ℕ} {lo hi a b : ℕ} (h : ∀ i, lo ≤ i → i < hi → κ' i = κ i) :
    cntIn κ' lo hi a b = cntIn κ lo hi a b := by
  zuluh
  zucr
  grind
theorem SS.Regs.of_frame2 {S : SS} {c c' : Config} (h : S.Regs c)
    (hr : ∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → c'.nreg r = c.nreg r) : S.Regs c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ ztbmk by_omega by_omega]; assumption)

/-- Pop the top entry: `tp := tp - 2`, `lo := STK[tp]`, `hi := STK[tp + 1]`. -/
def popB : Stmt := block [.subN 130701 130701 130001, .subN 130701 130701 130001,
  .addN 130702 130700 130701, .loadN 130300 130702, .addN 130702 130702 130001,
  .loadN 130301 130702]

/-- One iteration of the split driver. -/
def splitBody : Stmt := .seq popB (.seq medB (.seq climbStmt splitTail))

/-- The constant part of the cost of one iteration. -/
def splitC (L k : ℕ) : ℕ := (34 * L + 34) * zttz + 36 * L + 36 * k + 340
section proofs
variable {P : Polygon} {W : ℕ}
theorem popB_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c) {tp : ℕ}
    (htp : c.nreg 130701 = tp + 2) (hwS : S.bSTK + tp + 1 ≤ W) :
    ∃ c' k, Exec P W popB c c' k ∧ k = 6 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130701 = tp ∧ c'.nreg 130300 = c.nmem (S.bSTK + tp) ∧
      c'.nreg 130301 = c.nmem (S.bSTK + tp + 1) ∧
      (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130300 → r ≠ 130301 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 := hR.one; have hs := hR.rSTK
  unfold popB
  exec_block
  all_goals try (config_simp; simp only [htp, h1, hs]; omega)
  refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, fun r a b c d => ?_, rfl, rfl, rfl⟩
  · config_simp; omega
  · config_simp; grind
  · config_simp; grind
  · zuty
end proofs
section body
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {P : Polygon} {W : ℕ}
variable {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
/-- The keys of the items of a segment are preorders. -/
theorem SFacts.key_eq
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m) {i : ℕ}
    (hv : m ztde < μ) :
    keyOf m S.bACT S.bFIRST S.bFPRE i = preE (m ztwuk) ∧
      m ztwuk < N := by
  have hf := hSF.first ztufw
  zumpr
  have hN : ztbasc := by_omega
  exact ⟨by unfold keyOf; rw [hSF.pre _ hN], hN⟩

/-- The good test in memory is the good test of the preorder tree. -/
theorem SFacts.gdF_iff
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m) {lo hi : ℕ}
    (hlt : ∀ i, lo ≤ i → i < hi → m ztde < μ) {z : ℕ} (hz : z < N) :
    GdF m S.bACT S.bFIRST S.bFPRE S.bFSZ lo hi z ↔
      BTree.GdN preE ztuo ztbanf
        lo hi z := by
  unfold GdF BTree.GdN
  rw [hSF.pre z hz, hSF.sz z hz,
    cntIn_congr (fun i h1 h2 => (hSF.key_eq by_simp_all).1)]
open Classical in
/-- **One iteration of the split driver.** -/
theorem splitBody_exec {cf : Config} (hw : WordsBounded W cf)
    (hR : S.Regs cf) (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W cf.nmem)
    {lo hi : ℕ} {rest : List ztw} {fin : Finset ztw} {D : Finset ℕ} {nsp : ℕ}
    (hD : DInv M T k c S cf.nmem (ztdz :: rest) fin D nsp)
    (htp : cf.nreg 130701 = 2 * rest.length + 2) (hnsp : cf.nreg 130704 = nsp)
    (hk : 0 < k) (hs : 0 < S.s) :
    ∃ cf' K, Exec P W splitBody cf cf' K ∧ K + 2 ≤ 119 * ztcw + splitC S.L k ∧
      WordsBounded W cf' ∧ S.Regs cf' ∧
      (∃ news fin' D', DInv M T k c S cf'.nmem ztcny fin' D' ztodu ∧
        cf'.nreg 130701 = 2 * (news ++ rest).length ∧
        (news.map ztbep).sum + ztcw ≤
          ztcw * Nat.size ztcw) ∧
      cf'.nreg 130704 = nsp + 1 ∧ StaticEq A0 U cf.nmem cf'.nmem ∧
      ztfjp ∧
      cf'.rreg = cf.rreg ∧ cf'.rmem = cf.rmem ∧ cf'.output = cf.output := by
  zuglp
  have := hL.hFIRST; have := hL.hLEV; have := hL.hPV; have := hL.hFP; have := hL.hATT
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ; have := hL.hFPRE
  have := hL.hLBOT; have := hL.hLTOP; have := hL.hHALF; have := hL.hPOW; have := hL.hUPT
  have := hL.hUP; have := hL.hμU; have := hL.hNU; have := hL.hLU; have := hL.hVERT
  have := hL.hOPP; have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hSTK
  have := hL.hDF; have := hL.hW
  zuhfx
  have hpb := hSF.pow_big; have hpU := hSF.pow_U
  have hLU : S.L * S.N ≤ S.L * U := Nat.mul_le_mul_left _ by_omega
  generalize hm_def : cf.nmem = m at hSF hD
  zuerh
  zukcj
  have hlh := hD.sinv.wf _ hlv
  zuhyc
  zufvh

  have hmem : ∀ i, lo ≤ i → i < hi →
      m _ ∈ items ztwjj ztdz :=
    fun i i1 i2 => mem_items.mpr ztoou
  have hactμ : ztieh :=
    fun i i1 i2 => hD.sinv.lt _ hlv _ ztlpt
  -- the stack top
  have hstk := hD.stack
  rw [List.length_cons, stkList] at hstk
  obtain ⟨htop, -⟩ := List.cons.inj hstk
  obtain ⟨hlo_eq, hhi_eq⟩ := Prod.mk.inj htop
  -- pop
  obtain ⟨c1, k1, x1, hk1, hw1, hm1, htp1, hlo1, hhi1, hr1, hrr1, hrm1, ho1⟩ :=
    popB_exec (P := P) hw hR (tp := 2 * rest.length) htp by_omega
  rw [hm_def, ← hlo_eq] at hlo1
  rw [hm_def, ← hhi_eq] at hhi1
  rw [hm_def] at hm1
  have hfr1 : ∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → c1.nreg r = cf.nreg r :=
    fun r h1 h2 h3 => hr1 r h2 zthfu zthfu
      zthfu
  have hR1 := hR.of_frame2 hfr1
  -- the median and the window
  have hhalf : m _ = ztcw / 2 := hSF.half _ by_omega
  zukdq
  have hmedv := hactμ _ hmed.1 hmed.2
  have hlov := hactμ lo le_rfl by_omega
  have hlev0 := hSF.lev ztkiw
  have hlevlt := hSF.lev_lt ztkiw
  simp only at hlev0 hlevlt
  obtain ⟨c2, k2, x2, hk2, hw2, hm2, hW2, hy2, hb2, ht2, hlo2, hhi2, hr2, hrr2, hrm2, ho2⟩ :=
    medB_exec (P := P) hw1 hR1 hlo1 hhi1 by_omega
      by_grind
      by_grind
      by_omega by_grind ztlhw ztlhw
  zvmxz at hy2 hb2 ht2
  rw [hhalf, show ztcw / 2 + lo = lo + ztcw / 2 by omega] at hy2
  zuliz
  set y := m (S.bFIRST + m _) with hy_def
  set lbot := m (S.bLBOT + m _) with hlbot
  set ltop := m (S.bLTOP + m _) with hltop
  have hm2' : c2.nmem = m := by_grind
  -- the climb
  have hCtx : ClimbCtx c2 lo hi S.bACT S.bFIRST S.bFPRE S.bPOW S.L S.bFSZ S.bUP S.L S.N :=
    ⟨hR2.one, hR2.zero, hlo2, hhi2, hR2.cACT, hR2.cFIRST, hR2.cFPRE, hR2.cPOW, hR2.cLP, hW2,
      hR2.cFSZ, hR2.cUP, hR2.cUPE, hR2.cN, hR2.cL⟩
  have hkey : ∀ i, lo ≤ i → i < hi →
      keyOf m S.bACT S.bFIRST S.bFPRE i = preE _ ∧
        m _ < N := fun i i1 i2 => hSF.key_eq by_grind
  zumde
  have hupN : ∀ g, g < N → R.up g < N := by
    zubrf
    rw [hSF.R_up ⟨g, hg⟩]; omega
  have hupit : ∀ n g, g < N → R.up^[n] g < N := by
    intro n; induction n with
    | zero => intro g hg; exact hg
    | succ n ih => intro g hg; rw [Function.iterate_succ_apply]; exact by_grind
  have hCM : ClimbMem c2.nmem W lo hi S.bACT S.bFIRST S.bFPRE S.bPOW S.L S.bFSZ S.bUP S.L S.N
      R.up := by
    rw [hm2']
    refine ⟨hD.sorted _ List.mem_cons_self, hlh, hSF.pow, by_omega, by_omega, by_omega,
      by omega, fun i i1 i2 => ?_, fun z hz => ?_, by_omega, fun g hg => ?_,
      fun j hj g hg => ?_, by_omega⟩
    · have := hkey i i1 i2; have := hactμ i i1 i2; omega
    · have := hcp.prsz z hz; omega
    · grind
    · rw [hN] at hg ⊢; exact hSF.up_tab j hj g hg
  have hyN : y < N := by_grind
  have hRn := hSF.R_n
  have hroot : GdF c2.nmem S.bACT S.bFIRST S.bFPRE S.bFSZ lo hi (R.up^[2 ^ S.L] y) := by
    have hyR : y < R.n := by_omega
    have hpos := (hSF.R_ok.pos_spec hyR).1
    rw [BTree.iterate_up_root hSF.R_ok hyR by_omega, hm2', hSF.R_root,
      hSF.gdF_iff by_omega by_omega, ← hSF.R_root]
    exact BTree.good_root hSF.R_ok hSF.R_pre
      (fun i i1 i2 => ⟨by_grind, rfl⟩) by_omega
  obtain ⟨c3, k3, x3, hk3, hm3, hr3, hrr3, hrm3, ho3, hf3, hres3⟩ :=
    climbStmt_exec (P := P) hw2 hCtx hCM hy2 by_omega hSF.L_pos hroot
  rw [hm2'] at hres3
  have hm3' : c3.nmem = m := by_grind
  have hfr3 : ∀ r, ¬ SplitRG r → c3.nreg r = c2.nreg r := fun r h => hr3 r (fun h' => h (by
    unfold ClimbRG GoodRG at h'; unfold SplitRG; omega))
  have hR3 := hR2.of_frame hfr3
  set f := c3.nreg 130344 with hf_def
  have hfN : f < N := by_omega
  -- the centroid
  have hgd : ∀ z, z < N → (GdF m S.bACT S.bFIRST S.bFPRE S.bFSZ lo hi z ↔
      BTree.GdN preE ztuo (fun i => preE _)
        lo hi z) := fun z hz => hSF.gdF_iff by_omega hz
  have hsorted : Sorted ztbanf lo hi := by
    zukjl
    have := hD.sorted _ List.mem_cons_self i i' h1 h2 h3
    rw [(hkey i h1 by_omega).1, (hkey i' by_omega h3).1] at this
    omega
  have hres' : (BTree.GdN preE ztuo
        ztbakf lo hi
        (ztwuw ztbasq) ∧
        f = ztwuw ztbasq) ∨
      ∃ x n, R.up^[n] (ztwuw (ztwjj
          ztwno)) = x ∧
        ¬ BTree.GdN preE ztuo
          ztbakf lo hi x ∧
        BTree.GdN preE ztuo
          ztbakf lo hi
          ztqcf ∧ f = R.up x := by
    rcases hres3 with ⟨hg, he⟩ | ⟨x, n, hx, hng, hg, he⟩
    · exact Or.inl ⟨(hgd y hyN).mp hg, he⟩
    · have hxN : x < N := by rw [← hx]; exact hupit n y hyN
      exact Or.inr ⟨x, n, hx, fun h => hng ((hgd x hxN).mpr h),
        (hgd _ by_omega).mp hg, he⟩
  obtain ⟨hgood, hch⟩ := centroid_typed hSF.R_ok hSF.R_n hSF.R_up
    (by rw [hSF.R_root, hSF.r0]) hSF.R_pre
    (firstN := fun v => m _) hSF.first (hD.sinv.inj _ hlv) zttmd
    hsorted hfN hres' by_omega
  -- the window
  have hwin : ∀ x : Fin μ, (x : ℕ) ∈ items ztwjj ztdz →
      lbot ≤ T.level x ∧ T.level x ≤ ltop := by
    zuh
    have hsl := hD.sinv.inslab _ hlv _ hx _ (hmem lo le_rfl by_omega)
    have := hSF.win ztkiw x hsl
    zuhlq

  have hwk : ltop + 1 - lbot ≤ k := by
    have := hSF.win_k ztkiw
    zuhlq

  -- the invariant after the split
  obtain ⟨hsum, news, fin', D', hD', hq2, hstat, hpot⟩ := dinv_split hSF hD
    (tp := 2 * rest.length) rfl hk hwin ztkla hgood hch rfl
  -- the tail
  have hnspW : nsp + 1 ≤ W := by
    have h2 := hD.sinv.pot2
    have : nsp ≤ nsp * S.s := Nat.le_mul_of_pos_right _ hs
    omega
  obtain ⟨c4, k4, x4, hk4, hw4, hq4, hnsp4, hr4, hrr4, hrm4, ho4⟩ :=
    splitTail_exec (P := P) x3.wb_right hR3 hL (lo := lo) (hi := hi) (lbot := lbot) (ltop := ltop)
      (f := f) (tp := 2 * rest.length) (nsp := nsp) (up := upT)
      ztbut
      ztbut
      ztbut
      ztbut rfl
      (by rw [hr3 _ ztiis, hr2 _ ztbmk]; omega)
      (by rw [hr3 _ ztiis, hr2 _ ztbmk,
        hr1 _ by_omega by_omega by_omega by_omega]; omega)
      hlh by_omega by_omega
      (by rw [hm3']; exact hSF.markMem)
      (fun d hd => by
        rw [hm3', hSF.vert ⟨d, by_omega⟩, hμ]; omega)
      (by rw [hm3', hSF.opp ztkla, hN]; omega)
      (by rw [hm3', hSF.att ztkla, hN]; omega)
      ztntv
      (by rw [hm3', hSF.fp ztkla, hN]; omega)
      (fun v hv => by
        have := hSF.first ⟨v, by_omega⟩
        zugzu
        rw [hm3', this, hN]; omega)
      (fun i i1 i2 => by rw [hm3', hμ]; exact hactμ i i1 i2)
      ztntv
      by_omega hnspW
  rw [hm3'] at hq4
  refine ⟨c4, k1 + ztbqj, .seq x1 (.seq x2 (.seq x3 x4)), ?_, hw4, ?_,
    ⟨news, fin', D', ?_, ?_, hpot⟩, hnsp4, ?_, ?_, ?_, ?_, ?_⟩
  · unfold splitC
    omega
  · refine hR.of_frame2 ztnzk
    zucjt
  · have e : c4.nmem = (pushF S.bSTK S.s _ _ _).1 :=
      congrArg Prod.fst hq4
    zubuu
  · have e := congrArg Prod.snd hq4
    zujpc
    zubuu
  · have e := congrArg Prod.fst hq4
    zujpc
    zubuu
  · zuete
    zucjt
  · rw [hrr4, hrr3, hrr2, hrr1]
  · rw [hrm4, hrm3, hrm2, hrm1]
  · rw [ho4, ho3, ho2, ho1]
end body
def driverStmt : Stmt := .whileLtN 130009 130701 splitBody

/-- The size potential of a list of segments. -/
def segPot (l : List ztw) : ℕ := (l.map ztbep).sum
section body
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {P : Polygon} {W : ℕ}
variable {S : SS} {m : ℕ → ℕ} {stk : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}
omit [Fintype F] [DecidableEq F] in
/-- The number of splits is at most `2 μ / s`. -/
theorem DInv.nsp_le
 (hD : DInv M T k c S m stk fin D nsp) (hs : 0 < S.s) :
    nsp ≤ 2 * μ / S.s := by
  rw [Nat.le_div_iff_mul_le hs]
  have := hD.sinv.pot2
  omega
omit [Fintype F] [DecidableEq F] in
/-- The stack in memory is the list of the invariant. -/
theorem DInv.stk_eq
 (hD : DInv M T k c S m stk fin D nsp) :
    stkList m S.bSTK (2 * stk.length / 2) = stk := by
  rw [show 2 * stk.length / 2 = stk.length by omega]
  exact hD.stack.symm

/-- **The split driver.** -/
theorem driver_exec {A0 U : ℕ} {cf : Config} (hw : WordsBounded W cf)
    (hR : S.Regs cf) (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W cf.nmem)
    {stk : List ztw} {fin : Finset ztw} {D : Finset ℕ} {nsp : ℕ}
    (hD : DInv M T k c S cf.nmem stk fin D nsp)
    (htp : cf.nreg 130701 = 2 * stk.length) (hnsp : cf.nreg 130704 = nsp)
    (hk : 0 < k) (hs : 0 < S.s) :
    ∃ cf' K, Exec P W driverStmt cf cf' K ∧
      K ≤ 120 * segPot stk + splitC S.L k * (2 * μ / S.s - nsp) + 2 ∧
      WordsBounded W cf' ∧ S.Regs cf' ∧
      (∃ fin' D' nsp', DInv M T k c S cf'.nmem [] fin' D' nsp') ∧
      cf'.nreg 130701 = 0 ∧ StaticEq A0 U cf.nmem cf'.nmem ∧
      ztfjp ∧
      cf'.rreg = cf.rreg ∧ cf'.rmem = cf.rmem ∧ cf'.output = cf.output := by
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ S.Regs c' ∧
    StaticEq A0 U cf.nmem c'.nmem ∧
    (∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → c'.nreg r = cf.nreg r) ∧
    c'.rreg = cf.rreg ∧ c'.rmem = cf.rmem ∧ c'.output = cf.output ∧
    ∃ stk' fin' D' nsp', DInv M T k c S c'.nmem stk' fin' D' nsp' ∧
      c'.nreg 130701 = 2 * stk'.length ∧ c'.nreg 130704 = nsp'
  let Φ : Config → ℕ := fun c' =>
    120 * segPot (stkList c'.nmem S.bSTK (c'.nreg 130701 / 2)) +
      splitC S.L k * (2 * μ / S.s - c'.nreg 130704)
  have hΦ : ∀ c' stk' fin' D' nsp', DInv M T k c S c'.nmem stk' fin' D' nsp' →
      c'.nreg 130701 = 2 * stk'.length → c'.nreg 130704 = nsp' →
      Φ c' = 120 * segPot stk' + splitC S.L k * (2 * μ / S.s - nsp') := by
    intro c' stk' fin' D' nsp' h1 h2 h3
    simp only [Φ]
    rw [h2, h3, h1.stk_eq]
  obtain ⟨cf', K, e, ⟨hw', hR', hst', hfr', hrr', hrm', ho', stk', fin', D', nsp', hD', htp',
      hnsp'⟩, htest, hK⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 130009) (b := 130701)
    (body := splitBody) I Φ ztbms (fun c1 hI1 htest => by
      obtain ⟨hw1, hR1, hst1, hfr1, hrr1, hrm1, ho1, stk1, fin1, D1, nsp1, hD1, htp1, hnsp1⟩ := hI1
      have hSF1 := hSF.of_static hst1
      rw [hR1.zero, htp1] at htest
      obtain ⟨⟨lo, hi⟩, rest, rfl⟩ : ∃ p rest, stk1 = p :: rest := by
        cases stk1 with
        | nil => simp at htest
        | cons p rest => exact ⟨p, rest, rfl⟩
      obtain ⟨c2, K2, e2, hK2, hw2, hR2, ⟨news, fin2, D2, hD2, htp2, hpot2⟩, hnsp2, hst2, hfr2,
          hrr2, hrm2, ho2⟩ := splitBody_exec (P := P) hw1 hR1 hSF1 hD1
        by_omega hnsp1 hk hs
      refine ⟨c2, K2, e2, ⟨hw2, hR2, hst1.trans hst2, fun r a b d => (hfr2 r a b d).trans
        (hfr1 r a b d), hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1, news ++ rest, fin2, D2,
        nsp1 + 1, hD2, htp2, hnsp2⟩, ?_⟩
      rw [hΦ c2 _ _ _ _ hD2 htp2 hnsp2, hΦ c1 _ _ _ _ hD1 htp1 hnsp1]
      have hle := hD2.nsp_le hs
      unfold segPot
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      unfold len at hpot2 ⊢
      simp only at hpot2 ⊢
      have hmul : splitC S.L k * (2 * μ / S.s - nsp1) =
          splitC S.L k * ztjfk + splitC S.L k := by
        rw [show 2 * μ / S.s - nsp1 = ztjfk + 1 by omega, Nat.mul_add,
          Nat.mul_one]
      omega)
    ⟨hw, hR, StaticEq.refl _ _ _, fun _ _ _ _ => rfl, rfl, rfl, rfl, stk, fin, D, nsp, hD, htp,
      hnsp⟩
  rw [hR'.zero, htp'] at htest
  have hnil : stk' = [] := by
    simp_all
  subst hnil
  refine ⟨cf', K, e, ?_, hw', hR', ⟨fin', D', nsp', hD'⟩, by_omega, hst', hfr', hrr',
    hrm', ho'⟩
  grind
end body
end
end Chazelle.Core.Cluster
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap
@[expose] public section
theorem inputFacts {m : ℕ → ℕ} {A B μ E : ℕ}
    (h : Robust A m (fun m' => PlanarMapAt m' B μ E)) :
    ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F) (M : CombMap ztemr F ztzbw),
      M.Planar ∧ MapArrays m ztqtg ztbaif ztbaic μ ztdsj M ∧ 0 < μ ∧ 0 < E ∧
      μ ≤ 2 * E ∧ B + 2 < A ∧ m B + 2 * E ≤ A ∧ m ztvf + 2 * E ≤ A ∧ m zthb + 2 * E ≤ A := by
  obtain ⟨F, i1, i2, M, hM, hA⟩ := PlanarMapAt.exists_arrays h.holds
  -- the map has a dart and a vertex
  have hEuler := hM.2
  have hN : 0 < 2 * E := by
    zuccr
    have hE0 : 2 * E = 0 := by_omega
    have hV : Fintype.card ztemr = 0 := by
      zumlf
      exact ⟨fun v => by
        obtain ⟨d, -⟩ := M.vert_surj v
        exact absurd d.2 by_omega⟩
    have hF : Fintype.card F = 0 := by
      zumlf
      exact ⟨fun g => by
        obtain ⟨d, -⟩ := M.face_surj g
        exact absurd d.2 by_omega⟩
    have hE : M.numE = 0 := by
      unfold CombMap.numE
      simp_all
    unfold CombMap.euler at hEuler
    omega
  have hμ : ztrzr := (M.vert ztkik).pos
  have hμN : μ ≤ 2 * E := by
    have := Fintype.card_le_of_surjective M.vert M.vert_surj
    simp_all
  -- the bases lie below `A`
  have hbase : B + 2 < A := by
    zukr
    obtain ⟨i, hi, hiA⟩ : ∃ i, i ≤ 2 ∧ A ≤ B + i := ⟨2, le_rfl, by_omega⟩
    set Z := B + A + 3
    zugym
    let m' : ℕ → ℕ := fun a => if a = B + i then Z else if Z ≤ a then X else m a
    obtain ⟨F', _, _, M', -, hA'⟩ := PlanarMapAt.exists_arrays (h m' (fun a ha => by
      grind))
    have e1 : m' ztjgq = Z := by_grind
    have e2 : m' (Z + 0) = X := by_grind
    zuiet
    · have := hA'.opp hN
      grind
    · have := hA'.rot hN
      grind
    · have := hA'.vert hN
      grind
  -- the arrays lie below `A`
  have harr : ∀ i, i ≤ 2 → m ztjgq + 2 * E ≤ A := by
    zug
    zukr
    set d := 2 * E - 1
    zugym
    let m' : ℕ → ℕ := fun a => if a = m ztjgq + d then X else m a
    obtain ⟨F', _, _, M', -, hA'⟩ := PlanarMapAt.exists_arrays (h m' (fun a ha => by
      grind))
    have eB : ∀ j, j ≤ 2 → m' ztelw = m ztelw := fun j hj => by
      grind
    have e2 : m' (m ztjgq + d) = X := by_grind
    have hd : d < 2 * E := by_omega
    zuiet
    · have := hA'.opp hd
      grind
    · have := hA'.rot hd
      grind
    · have := hA'.vert hd
      grind
  exact ⟨F, i1, i2, M, hM, hA, hμ, by_omega, hμN, hbase, by simpa using harr 0 by_omega,
    harr 1 by_omega, harr 2 le_rfl⟩

/-! ## The global values -/

/-- The input values of the algorithm. -/
structure GV where
  B : ℕ
  μ : ℕ
  E : ℕ
  k : ℕ
  A0 : ℕ
  bO : ℕ
  bR : ℕ
  bV : ℕ
namespace GV
variable (g : GV)

/-- The number of darts. -/
def N : ℕ := 2 * g.E
/-- The slab width. -/
def k' : ℕ := min g.k g.μ
/-- The cluster size. -/
def s : ℕ := min zttla g.μ
/-- The table length. -/
def L : ℕ := Nat.clog 2 ztgju
/-- The slot size. -/
def U : ℕ := g.N + g.μ + 2 ^ g.L + 3
/-- The base of slot `j`. -/
def base (j : ℕ) : ℕ := g.A0 + j * g.U
/-- The end of the allocated area. -/
def END : ℕ := g.A0 + 54 * g.U + 2 * ztesx
end GV

/-- The global registers hold the global values. -/
structure GR (g : GV) (c : Config) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rB : c.nreg 130010 = g.B
  rμ : c.nreg 130011 = g.μ
  rE : c.nreg 130012 = g.E
  rk : c.nreg 130013 = g.k
  rN : c.nreg 130014 = g.N
  rk' : c.nreg 130015 = g.k'
  rs : c.nreg 130016 = g.s
  rL : c.nreg 130017 = g.L
  rP : c.nreg 130018 = 2 ^ g.L
  rU : c.nreg 130019 = g.U
  rA0 : c.nreg 130020 = g.A0
  rO : c.nreg 130021 = g.bO
  rR : c.nreg 130022 = g.bR
  rV : c.nreg 130023 = g.bV
  rLU : c.nreg 130026 = g.L * g.U
  rbase : ∀ j, j ≤ 54 → c.nreg ztsrb = g.base j
  rUP : c.nreg 130085 = g.A0 + 54 * g.U + g.L * g.U
  rEND : c.nreg 130086 = g.END

/-- The global registers. -/
def GRReg (r : ℕ) : Prop := r = 130001 ∨ r = 130009 ∨ (130010 ≤ r ∧ r ≤ 130089)
theorem GR.frame {g : GV} {c c' : Config} (h : GR g c)
    (hr : ∀ r, GRReg r → c'.nreg r = c.nreg r) : GR g c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_,
    ?_⟩
  all_goals first
    | (zunlu; assumption)
    | (zunlu; exact h18 j hj)
open Equiv
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
omit [Fintype F] [DecidableEq F] in
/-- **The star arrays encode the dual of the star map.** -/
theorem star_dual_enc {opp fp fpi : ℕ → ℕ} (hopp : ∀ d : Fin N, opp d = M.opp d)
    (hfp : ∀ d : Fin N, fp d = M.fperm d) (hfpi : ∀ d : Fin N, fpi d = (M.fperm⁻¹ d : Fin N))
    {G : Env} (hGN : G.N = 3 * N) (hGnv : G.nv = N)
    (hSO : ∀ d, d < N → G.opp d = opp d ∧ G.opp ztfoh = 2 * N + d ∧ G.opp ztdkl = N + d)
    (hSR : ∀ d, d < N → G.rot d = 2 * N + fp d ∧ G.rot ztfoh = d ∧
      G.rot ztdkl = N + fpi d)
    (hSF : ∀ d, d < N → G.vert d = d ∧ G.vert ztfoh = d ∧ G.vert ztdkl = fpi d)
    (hSFi : ∀ d, d < N → G.first d = d) :
    EnvEnc G (star M).dual ztgja ztqml := by
  refine ⟨fun v => by_omega, fun v w h => Fin.ext h, fun u hu => ⟨⟨u, by_omega⟩, rfl⟩,
    fun x => by rw [hGN]; exact enc_lt x, fun x y h => enc_inj h, fun e he => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_, fun v => ⟨.inl v, by rw [hSFi v v.2]; rfl, rfl⟩⟩
  · rw [hGN] at he
    by_cases h1 : e < N
    · exact ⟨.inl ⟨e, h1⟩, rfl⟩
    · by_cases h2 : e < 2 * N
      · exact ⟨.inr (.inl ⟨e - N, by_omega⟩), by simp only [enc]; omega⟩
      · exact ⟨.inr (.inr ⟨e - 2 * N, by_omega⟩), by simp only [enc]; omega⟩
  · zuim
    · show G.opp d = enc N (starOpp M ztbrs)
      rw [(hSO d d.2).1, hopp]; rfl
    · show G.opp ztfoh = enc N (starOpp M ztxfu)
      rw [(hSO d d.2).2.1]; rfl
    · show G.opp ztdkl = enc N (starOpp M ztcsa)
      rw [(hSO d d.2).2.2]; rfl
  · zuim
    · show G.rot d = enc N ((star M).fperm ztbrs)
      rw [(hSR d d.2).1, star_fperm_inl, hfp]; rfl
    · show G.rot ztfoh = enc N ((star M).fperm ztxfu)
      rw [(hSR d d.2).2.1, star_fperm_inl_inr]; rfl
    · show G.rot ztdkl = enc N ((star M).fperm ztcsa)
      rw [(hSR d d.2).2.2, star_fperm_inr_inr, hfpi]; rfl
  · zuim
    · show G.vert d = ((starFace M ztbrs : Fin N) : ℕ)
      simp_all
    · show G.vert ztfoh = ((starFace M ztxfu : Fin N) : ℕ)
      simp_all
    · show G.vert ztdkl = ((starFace M ztcsa : Fin N) : ℕ)
      simp_all
variable {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
variable (d : Fin N)
omit [Fintype F] [DecidableEq F] in
theorem starTree_isTreeDart_inl :
    (starTree T a ha).IsTreeDart ztbrs ↔ T.IsTreeDart d := by
  constructor
  · zubsh

    · have hv : ztsmt := fun h' => hy by_simp_all
      refine ⟨v, hv, ?_⟩
      zuy
      · left; exact Sum.inl_injective h
      · right; exact Sum.inl_injective h
    tauto
  · rintro ⟨v, hv, h⟩
    refine ⟨.inl v, fun h' => hv (Sum.inl_injective h'), ?_⟩
    tauto
omit [Fintype F] [DecidableEq F] in
theorem starTree_isTreeDart_inl_inr :
    (starTree T a ha).IsTreeDart ztxfu ↔ d = a ztcci := by
  constructor
  · zubsh

    · tauto
    · zuy
      · have : ztutg := by
          have := congrArg (fun x : Fin N ⊕ Fin N ⊕ Fin N => match x with
            | .inr (.inl e) => e | _ => d) h
          tauto
        simp_all
      · cases h
  · zuq
    refine ⟨.inr ztcci, by_simp, Or.inl ?_⟩
    tauto
omit [Fintype F] [DecidableEq F] in
theorem starTree_isTreeDart_inr_inr :
    (starTree T a ha).IsTreeDart ztcsa ↔ d = a ztcci := by
  constructor
  · zubsh

    · tauto
    · zuy
      · cases h
      · have : ztutg := by
          have := congrArg (fun x : Fin N ⊕ Fin N ⊕ Fin N => match x with
            | .inr (.inr e) => e | _ => d) h
          tauto
        simp_all
  · zuq
    refine ⟨.inr ztcci, by_simp, Or.inr ?_⟩
    tauto
omit [Fintype F] [DecidableEq F] in
/-- **The attachment from a representative array.** -/
theorem att_fun {att : ℕ → ℕ} (hlt : ∀ d : Fin N, att d < N)
    (hface : ∀ d : Fin N, ∀ h : att d < N, M.face ⟨att d, h⟩ = M.face d)
    (hconst : ∀ d e : Fin N, M.face d = M.face e → att d = att e) :
    ∃ (a : F → Fin N) (_ha : ∀ g, M.face ztbkl = g), ∀ d : Fin N, (a ztcci : ℕ) = att d := by
  classical
  let rep : F → Fin N := fun g => Classical.choose (M.face_surj g)
  have hrep : ∀ g, M.face ztwcs = g := fun g => Classical.choose_spec (M.face_surj g)
  refine ⟨fun g => ⟨att ztwcs, hlt _⟩, fun g => ?_, fun d => ?_⟩
  · simp_all
  · grind
end
end Chazelle.Core.Cluster
section
set_option hygiene false
local macro "zqbep" : tactic => `(tactic| (zumwj; grind))
local macro "zqbeq" : tactic => `(tactic| (zumwj; unfold AttRG at hr; grind))
set_option hygiene true

/-!
# WP-I, part 25: face permutation, tree flags and face representatives on the RAM

* `fpStmt`: `FP[d] := ROT[OPP[d]]` (the face permutation), `fpStmt_exec`;
* `teStmt`: the tree-dart flags `TE[d] = 1` iff `d = PAR[v]` or `d = OPP[PAR[v]]` for some
  `1 ≤ v < μ`, else `0`; `teStmt_exec`;
* `attStmt`: the face representatives `ATT[e]` = the least dart of the face of `e`, by walking
  every face cycle once from its least dart; `attStmt_exec`.
* `face_orbit`: the darts of a face are the face-permutation iterates of any of its darts.

Registers: `fpStmt` `130520` (`ROT`), `130521` (`OPP`), `130522` (`FP`), `130523` (`N`), scratch
`130524 … 130526`; `teStmt` `130540` (`PAR`), `130541` (`OPP`), `130542` (`TE`), `130543` (`μ`),
`130544` (`N`), scratch `130545 … 130547` (and the fill registers `130150 … 130154`);
`attStmt` `130530` (`FP`), `130531` (`ATT`), `130532` (`N`), scratch `130533 … 130537` (and the fill
registers).
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs Chazelle.Separator
@[expose] public section
section orbit
variable {μ N : ℕ} {F : Type*} {M : CombMap (Fin μ) F (Fin N)}
variable {fp : ℕ → ℕ}
theorem iterate_fp (hfp : ∀ d : Fin N, fp d = M.fperm d) (n : ℕ) (d : Fin N) :
    fp^[n] d = ((M.fperm ^ n) d : Fin N) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hfp, ih, pow_succ, Equiv.Perm.mul_apply]
theorem fp_injOn (hfp : ∀ d : Fin N, fp d = M.fperm d) : InjOn fp N := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · have := hfp ztfxa; simp_all
  · have h1 := hfp ztfxa; have h2 := hfp zthnw
    zufct
    zvmza at hxy
    have := M.fperm.injective (Fin.ext hxy)
    simp_all

/-- **The darts of a face are the iterates of the face permutation below the period.** -/
theorem face_orbit [Finite ztjiv] {fp : ℕ → ℕ} (hfp : ∀ d : Fin N, fp d = M.fperm d)
    (d e : Fin N) :
    M.face e = M.face d ↔ ∃ i, i < per fp N d ∧ fp^[i] d = e := by
  constructor
  · zuq
    have hsc := M.sameCycle_of_face d e h.symm
    zuicz
    obtain ⟨j, hj, hjn⟩ := exists_lt_per_of_iterate (fp_injOn hfp) d.2 n
    refine ztdqs
    rw [← hjn, iterate_fp hfp]
    tauto
  · rintro ⟨i, -, hi⟩
    have : (M.fperm ^ i) d = e := Fin.ext (by rw [← iterate_fp hfp]; exact hi)
    zuhnz
    clear this hi
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, M.face_fperm_apply, ih]
end orbit

/-! ## The face permutation -/

/-- One dart: `FP[d] := ROT[OPP[d]]`. -/
def fpBody : Stmt := block [.addN 130525 130521 130524, .loadN 130526 130525,
  .addN 130525 130520 130526, .loadN 130526 130525, .addN 130525 130522 130524,
  .storeN 130525 130526, .addN 130524 130524 130001]

/-- **The face permutation array.** -/
def fpStmt : Stmt := .seq (.instr (.constN 130524 0)) (.whileLtN 130524 130523 fpBody)

/-- The scratch registers of `fpStmt`. -/
def FpRG (r : ℕ) : Prop := 130524 ≤ r ∧ r ≤ 130526
section fp
variable {P : Polygon} {W : ℕ}

/-- **The face permutation**: `FP[d] = ROT[OPP[d]]` for `d < N`. -/
theorem fpStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bR bO bF N : ℕ} (hR : c.nreg 130520 = bR) (hO : c.nreg 130521 = bO)
    (hF : c.nreg 130522 = bF) (hN : c.nreg 130523 = N) (hwO : bO + N ≤ W) (hwF : bF + N ≤ W)
    (hdO : bF + N ≤ bO ∨ bO + N ≤ bF)
    (hRw : ∀ d, d < N → bR + c.nmem ztbtt ≤ W ∧
      (bR + c.nmem ztbtt < bF ∨ bF + N ≤ bR + c.nmem ztbtt)) :
    ∃ c' k, Exec P W fpStmt c c' k ∧ k ≤ 9 * N + 3 ∧ WordsBounded W c' ∧
      PFr FpRG (fun a => bF ≤ a ∧ a < bF + N) c c' ∧
      ∀ d, d < N → c'.nmem (bF + d) = c.nmem ztzkm := by
  have e0 := Exec.constN (P := P) hw 130524 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130524 0 }
  have hf1 : PFr FpRG (fun a => bF + 0 ≤ a ∧ a < bF + N) c c1 :=
    PFr.nreg ztffw (fun r hr => by
      zumwj; unfold FpRG at hr; grind)
  obtain ⟨c', k, e, hk, hw', -, hf', hI⟩ := mapLoop (P := P) (W := W) (ri := 130524)
    (rn := 130523) (body := fpBody) (Rg := FpRG) by_tauto
    zteqk (bOut := bF) (n := N) (j₀ := 0) (B := 7)
    (fun d => c.nmem ztzkm) e0.wb_right
    by_rfl
    by_tauto ztbg
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      zulkb
      have r0 := hf12.1
      have rR := (r0 130520 zteqk).trans hR
      have rO := (r0 130521 zteqk).trans hO
      have rF := (r0 130522 zteqk).trans hF
      have r1 := (r0 130001 zteqk).trans hone
      have mO : c2.nmem _ = c.nmem zthdq := hf12.2.2.2.2 _ by_omega
      obtain ⟨hwr, hdr⟩ := hRw j hjn
      have mR : c2.nmem _ = c.nmem (bR + c.nmem zthdq) :=
        hf12.2.2.2.2 _ by_omega
      unfold fpBody
      exec_block
      · omega
      · simp_all
      · config_simp; omega
      · config_simp; omega
      · zumkg
        · zumwj; unfold FpRG at hr; grind
        simp_all)
  refine ⟨c', 1 + k, .seq e0 e, by_omega, hw', ?_, by_simp_all⟩
  exact (hf1.trans hf').mono by_simp_all
    by_omega
end fp

/-! ## Tree-dart flags -/

/-- One vertex: `TE[PAR[v]] := 1`, `TE[OPP[PAR[v]]] := 1`, `v := v + 1`. -/
def teBody : Stmt := block [.addN 130546 130540 130545, .loadN 130547 130546,
  .addN 130546 130541 130547, .loadN 130548 130546, .addN 130546 130542 130547,
  .storeN 130546 130001, .addN 130546 130542 130548, .storeN 130546 130001,
  .addN 130545 130545 130001]

/-- **The tree-dart flags.** -/
def teStmt : Stmt := .seq zthsr
  (.seq fillStmt (.seq (.instr (.copyN 130545 130001)) (.whileLtN 130545 130543 teBody)))

/-- The registers written by `teStmt`. -/
def TeRG (r : ℕ) : Prop := (130545 ≤ r ∧ r ≤ 130548) ∨ ztbxr

/-- The tree darts: `PAR[v]` and `OPP[PAR[v]]` for `1 ≤ v < j`. -/
def TeSet (m : ℕ → ℕ) (bPar bO j d : ℕ) : Prop :=
  ∃ v, 1 ≤ v ∧ v < j ∧ (d = m zthdt ∨ d = m (bO + m zthdt))
section te
variable {P : Polygon} {W : ℕ}

/-- **The tree-dart flags**: `TE[d] = 1` on the tree darts, `0` elsewhere. -/
theorem teStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bPar bO bT μ N : ℕ} (hPar : c.nreg 130540 = bPar)
    (hO : c.nreg 130541 = bO) (hT : c.nreg 130542 = bT) (hμ : c.nreg 130543 = μ)
    (hN : c.nreg 130544 = N) (hμ1 : 1 ≤ μ) (hwP : bPar + μ ≤ W) (hwT : bT + N ≤ W)
    (hNW : N + 1 ≤ W)
    (hdP : bT + N ≤ bPar ∨ bPar + μ ≤ bT) (hdO : bT + N ≤ bO ∨ bO + N ≤ bT)
    (hparN : ∀ v, 1 ≤ v → v < μ → c.nmem zthdt < N ∧ bO + c.nmem zthdt ≤ W ∧
      c.nmem (bO + c.nmem zthdt) < N) :
    ∃ c' k, Exec P W teStmt c c' k ∧ k ≤ 5 * N + 11 * μ + 10 ∧ WordsBounded W c' ∧
      PFr TeRG ztbty c c' ∧
      ∀ d, d < N → (c'.nmem ztjoi = 1 ∧ TeSet c.nmem bPar bO μ d) ∨
        (c'.nmem ztjoi = 0 ∧ ¬ TeSet c.nmem bPar bO μ d) := by
  classical
  -- the fill
  obtain ⟨c1, k1, e1, hk1, hw1, h150, h151, h152, hr1⟩ : ∃ c1 k1, Exec P W
      zthsr c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130150 = bT ∧ c1.nreg 130151 = N ∧
      c1.nreg 130152 = 0 ∧ PFr TeRG ztbty c c1 := by
    exec_block
    refine ⟨rfl, by_omega, by_simp_all, by_simp_all,
      by simp_all, PFr.nreg ztffw ztez⟩
    zufpm
  have hone1 : ztpmk := (hr1.1 _ ztchh).trans hone
  obtain ⟨c2, k2, e2, hk2, hf2, hfill⟩ := fillStmt_exec (P := P) e1.wb_right hone1
    by_omega by_omega
  zubig

  have hr2 : PFr TeRG ztbty c c2 :=
    hr1.trans (hf2.mono (fun r hr => by unfold FillScr at hr; unfold TeRG; omega)
      by_simp_all)
  have e3 := Exec.copyN (P := P) e2.wb_right 130545 130001
  set c3 := { c2 with nreg := upd c2.nreg 130545 _ }
  have hr3 : PFr TeRG ztbty c c3 :=
    PFr.nreg hr2 (fun r hr => by
      zumwj; unfold TeRG at hr; grind)
  have hone3 : ztpmn := (hr3.1 _ ztchh).trans hone
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI⟩ := forN
    (fun j c4 => WordsBounded W c4 ∧ c4.nreg 130545 = j ∧ c4.nreg 130543 = μ ∧
      PFr TeRG ztbty c c4 ∧ 1 ≤ j ∧
      ∀ d, d < N → (c4.nmem ztjoi = 1 ∧ TeSet c.nmem bPar bO j d) ∨
        (c4.nmem ztjoi = 0 ∧ ¬ TeSet c.nmem bPar bO j d))
    μ 9 ztywe
    (fun j c4 hj ⟨hw4, hi4, hn4, hf4, hj1, hI4⟩ => by
      zumfn
      have rP := (r0 130540 ztchh).trans hPar
      have rO := (r0 130541 ztchh).trans hO
      have rT := (r0 130542 ztchh).trans hT
      have r1 := (r0 130001 ztchh).trans hone
      obtain ⟨hpN, hwo, hoN⟩ := hparN j hj1 hj
      have mP : c4.nmem _ = c.nmem zttgh := hf4.2.2.2.2 _ by_omega
      set p := c.nmem zttgh
      have mO : c4.nmem _ = c.nmem zttgc := hf4.2.2.2.2 _ by_omega
      set o := c.nmem zttgc
      obtain ⟨c5, k5, e5, hk5, hw5, h5n, h5r, h5m, h5rr, h5rm, h5o⟩ : ∃ c5 k5,
          Exec P W teBody c4 c5 k5 ∧ k5 = 9 ∧ WordsBounded W c5 ∧ c5.nreg 130545 = j + 1 ∧
          (∀ r, ¬ TeRG r → c5.nreg r = c4.nreg r) ∧
          c5.nmem = upd (upd c4.nmem (bT + p) 1) (bT + o) 1 ∧
          c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output := by
        unfold teBody
        exec_block
        all_goals try (config_simp; simp only [rT, rO, rP, hi4, mP, mO, r1]; omega)
        refine ⟨rfl, by_omega, by_simp_all, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
        · zufpm
        simp_all
      refine ⟨c5, k5, e5, by_omega, hw5, h5n, by rw [h5r _ ztchh, hn4],
        ⟨by_simp_all, h5rr.trans hf4.2.1, h5rm.trans hf4.2.2.1,
          h5o.trans hf4.2.2.2.1, fun a ha => ?_⟩, by_omega, fun d hd => ?_⟩
      · rw [h5m, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
        exact hf4.2.2.2.2 a ha
      · have hnew : TeSet c.nmem bPar bO ztl d ↔ TeSet c.nmem bPar bO j d ∨
            d = p ∨ d = o := by
          constructor
          · rintro ⟨v, hv1, hv2, hv3⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hv2 with hv | rfl
            · exact Or.inl ⟨v, hv1, hv, hv3⟩
            grind
          · rintro (⟨v, hv1, hv2, hv3⟩ | h | h)
            · exact ⟨v, hv1, by_omega, hv3⟩
            · exact ⟨j, hj1, by_omega, Or.inl h⟩
            · exact ⟨j, hj1, by_omega, Or.inr h⟩
        rw [h5m, Machine.upd_apply, Machine.upd_apply]
        grind) ⟨e3.wb_right, by
      tauto,
      by show upd c2.nreg 130545 (c2.nreg 130001) 130543 = μ
         rw [Machine.upd_other _ _ _ by_omega, hr2.1 _ ztchh, hμ],
      hr3, le_rfl, fun d hd => Or.inr ⟨by
          grind, fun ⟨v, hv1, hv2, _⟩ => by_omega⟩⟩ hμ1
  zultc
  refine ⟨c', 3 + ztocd, .seq e1 ztgwz, by_omega, hw', hf', hI.2⟩
end te

/-! ## Face representatives -/
section orb
variable {f : ℕ → ℕ} {N : ℕ}

/-- `e` is on the cycle of `d`. -/
def Orb (f : ℕ → ℕ) (d e : ℕ) : Prop := ∃ i, f^[i] d = e
theorem orb_refl (d : ℕ) : Orb f d d := ztkil
theorem Orb.trans {a b c : ℕ} (h1 : Orb f a b) (h2 : Orb f b c) : Orb f a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨j + i, by zunri⟩
theorem Orb.symm (hf : InjOn f N) {a b : ℕ} (ha : a < N) (h : Orb f a b) : Orb f b a := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, hj, hij⟩ := exists_lt_per_of_iterate hf ha i
  refine ⟨per f N a - j, ?_⟩
  rw [hij, ← Function.iterate_add_apply, show per f N a - j + j = per f N a by omega,
    iterate_per hf ha]
theorem Orb.lt (hf : InjOn f N) {a b : ℕ} (ha : a < N) (h : Orb f a b) : b < N := by
  obtain ⟨i, rfl⟩ := h; exact hf.iterate_lt i ha
open Classical in
/-- The least dart of the cycle of `e`. -/
noncomputable def minOrb (f : ℕ → ℕ) (e : ℕ) : ℕ := Nat.find (ztlvs : ∃ d, Orb f d e)
theorem minOrb_orb (e : ℕ) : Orb f (minOrb f e) e := by
  classical
  exact Nat.find_spec (ztlvs : ∃ d, Orb f d e)
theorem minOrb_le (e : ℕ) : minOrb f e ≤ e := by
  classical
  exact Nat.find_min' (ztlvs : ∃ d, Orb f d e) (orb_refl e)
theorem minOrb_min {d e : ℕ} (h : Orb f d e) : minOrb f e ≤ d := by
  classical
  exact Nat.find_min' by_grind h

/-- Darts on one cycle have the same least dart. -/
theorem minOrb_eq (hf : InjOn f N) {d e : ℕ} (hd : d < N) (h : Orb f d e) :
    minOrb f e = minOrb f d := by
  have he := h.lt hf hd
  have h1 := minOrb_orb (f := f) e
  have h2 := minOrb_orb (f := f) d
  have hme : minOrb f e < N := lt_of_le_of_lt (minOrb_le e) he
  have hmd : minOrb f d < N := lt_of_le_of_lt (minOrb_le d) hd
  zudmc
  · exact minOrb_min (h2.trans h)
  · exact minOrb_min (h1.trans (h.symm hf hd))
end orb

/-- One step of the walk: `ATT[e] := d`, `e := FP[e]`, `cont := (e ≠ d)`. -/
def walkBody : Stmt := .seq (block [.addN 130536 130531 130534, .storeN 130536 130533,
    .addN 130536 130530 130534, .loadN 130534 130536, .constN 130535 0])
  (.ifLtN 130534 130533 ztfev
    ztyzo)

/-- The walk around the cycle of `d`. -/
def walkS : Stmt := .seq ztkrr
  (.whileLtN 130009 130535 walkBody)

/-- One dart of the outer loop: walk its cycle unless it is visited. -/
def attOuter : Stmt := .seq ztjoq
  (.seq (.ifLtN 130537 130532 .skip walkS) (.instr (.addN 130533 130533 130001)))

/-- **The face representatives.** -/
def attStmt : Stmt := .seq (block [.copyN 130150 130531, .copyN 130151 130532,
    .copyN 130152 130532])
  (.seq fillStmt (.seq (.instr (.constN 130533 0)) (.whileLtN 130533 130532 attOuter)))

/-- The registers written by `attStmt`. -/
def AttRG (r : ℕ) : Prop := (130533 ≤ r ∧ r ≤ 130537) ∨ ztbxr

/-- The unvisited cells. -/
def unv (m : ℕ → ℕ) (bA N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun x => m ztctu = N)).card
section att
variable {P : Polygon} {W : ℕ}
theorem unv_le (m : ℕ → ℕ) (bA N : ℕ) : unv m bA N ≤ N := by
  unfold unv
  grind

/-- Setting a cell with `N` to `d < N` decreases the unvisited count. -/
theorem unv_upd {m : ℕ → ℕ} {bA N x d : ℕ} (hx : x < N) (hmx : m ztctu = N) (hd : d < N) :
    unv (upd m ztctu d) bA N + 1 = unv m bA N := by
  unfold unv
  have : (Finset.range N).filter (fun y => m zttfw = N) =
      insert x ((Finset.range N).filter (fun y => upd m ztctu d zttfw = N)) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, Finset.mem_range,
      Machine.upd_apply]
    grind
  rw [this, Finset.card_insert_of_notMem]
  rw [Finset.mem_filter, Machine.upd_same]
  grind

/-- The context of the walk. -/
structure WalkCtx (c : Config) (bF bA N : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rF : c.nreg 130530 = bF
  rA : c.nreg 130531 = bA
  rN : c.nreg 130532 = N
theorem WalkCtx.of_frame {c c' : Config} {bF bA N : ℕ} (h : WalkCtx c bF bA N)
    (hr : ∀ r, ¬ AttRG r → c'.nreg r = c.nreg r) : WalkCtx c' bF bA N := by
  zubrk
  refine ztln <;> (rw [hr _ ztjqq]; assumption)
open Classical in
/-- **The walk around the cycle of `d`**: afterwards `ATT[x] = d` on the cycle, unchanged
elsewhere; cost plus `12` times the unvisited count does not grow beyond `12` times the old
count plus `6`. -/
theorem walkS_exec {c : Config} (hw : WordsBounded W c) {bF bA N d : ℕ}
    (hC : WalkCtx c bF bA N) (hd : c.nreg 130533 = d) (hdN : d < N)
    {f : ℕ → ℕ} (hf : InjOn f N) (hfm : ∀ x, x < N → c.nmem zttfz = f x)
    (hwA : bA + N ≤ W) (hwF : bF + N ≤ W) (hdisj : bA + N ≤ bF ∨ bF + N ≤ bA)
    (hfresh : ∀ i, i < per f N d → c.nmem ztmco = N) :
    ∃ c' k, Exec P W walkS c c' k ∧ k + 12 * unv c'.nmem bA N ≤ 12 * unv c.nmem bA N + 6 ∧
      WordsBounded W c' ∧ c'.nreg 130533 = d ∧
      PFr AttRG ztbbx c c' ∧
      ∀ x, x < N → c'.nmem ztctu = if Orb f d x then d else c.nmem ztctu := by
  classical
  have hper := per_pos hf hdN
  -- the start
  obtain ⟨c1, k1, e1, hk1, hw1, h1e, h1c, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      ztkrr c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nreg 130534 = d ∧ c1.nreg 130535 = 1 ∧
      (∀ r, r ≠ 130534 → r ≠ 130535 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, by_omega, by_simp_all, by config_simp; exact hC.one,
      fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp_all
  -- the loop
  obtain ⟨c', k, e, ⟨hw', j, hj, hej, hcj, hdj, hf', hmj⟩, htest, hk⟩ := whileLtN_pot (b := 130535)
    (fun c2 => WordsBounded W c2 ∧ ∃ j, j ≤ per f N d ∧ c2.nreg 130534 = f^[j] d ∧
      (c2.nreg 130535 = if j < per f N d then 1 else 0) ∧ c2.nreg 130533 = d ∧
      PFr AttRG ztbbx c c2 ∧
      ∀ x, x < N → c2.nmem ztctu =
        if ∃ i, i < j ∧ f^[i] d = x then d else c.nmem ztctu)
    (fun c2 => 12 * unv c2.nmem bA N) ztjvr
    (fun c2 ⟨hw2, j, hj, hej, hcj, hdj, hf2, hm2⟩ htest => by
      have hC2 := hC.of_frame hf2.1
      rw [hC2.zero, hcj] at htest
      have hjp : j < per f N d := by
        grind
      set e := f^[j] d
      have heN : e < N := hf.iterate_lt j hdN
      have hme : c2.nmem zttfv = N := by
        rw [hm2 e heN, ite_eq_right]
        · grind
        · zuecn
          exact absurd (iterate_inj_of_lt_per hf hdN by_omega hjp hie) by_omega
      have hfe : c2.nmem (bF + e) = f e := by
        zuede
      set e' := f e
      have he' : e' = f^[j + 1] d := by
        simp only [e', e]; zuocm
      -- the straight-line part
      obtain ⟨c3, k3, e3, hk3, hw3, h3e, h3c, h3d, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3,
          Exec P W (block [.addN 130536 130531 130534, .storeN 130536 130533,
            .addN 130536 130530 130534, .loadN 130534 130536, .constN 130535 0]) c2 c3 k3 ∧
          k3 = 5 ∧ WordsBounded W c3 ∧ c3.nreg 130534 = e' ∧ c3.nreg 130535 = 0 ∧
          c3.nreg 130533 = d ∧ (∀ r, ¬ AttRG r → c3.nreg r = c2.nreg r) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧
          c3.nmem = upd c2.nmem zttfv d := by
        exec_block
        all_goals first | omega | (config_simp; simp only [hC2.rA, hC2.rF, hej]; omega) | skip
        refine ⟨rfl, by_omega, ?_, by config_simp, by_tauto, fun r hr => ?_, rfl,
          rfl, rfl, ?_⟩
        · config_simp
          simp only [hC2.rA, hC2.rF, hej, hdj]
          zubc
          omega
        · zqbeq
        · config_simp; simp only [hC2.rA, hej, hdj]
      have hone3 := (h3r _ ztjqq).trans hC2.one
      -- the test `e' ≠ d`
      have hnext : (j + 1 < per f N d) ↔ e' ≠ d := by
        rw [he']
        constructor
        · intro h; exact iterate_ne_of_lt_per hf hdN by_omega h
        · zuq
          zudxc
          exact h (by rw [show j + 1 = per f N d by omega]; exact iterate_per hf hdN)
      obtain ⟨c4, k4, e4, hk4, h4e, h4c, h4d, h4r, hrr4, hrm4, ho4, hm4⟩ : ∃ c4 k4,
          Exec P W (.ifLtN 130534 130533 ztfev
            ztyzo) c3 c4 k4 ∧
          k4 ≤ 4 ∧ c4.nreg 130534 = e' ∧
          (c4.nreg 130535 = if j + 1 < per f N d then 1 else 0) ∧ c4.nreg 130533 = d ∧
          (∀ r, ¬ AttRG r → c4.nreg r = c3.nreg r) ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧
          c4.output = c3.output ∧ c4.nmem = c3.nmem := by
        by_cases h1 : c3.nreg 130534 < c3.nreg 130533
        · zuffi
          refine ⟨_, _, .ifLtN_true h1 ec, by_omega, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
            rfl⟩
          · zqbep
          · zuioy

          · zqbep
          · zqbep
        · by_cases h2 : c3.nreg 130533 < c3.nreg 130534
          · zuffi
            refine ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 ec), by_omega, ?_, ?_, ?_,
              fun r hr => ?_, rfl, rfl, rfl, rfl⟩
            · zqbep
            · zuioy

            · zqbep
            · zqbep
          · refine ⟨c3, _, .ifLtN_false h1 ztzro, by_omega, h3e, ?_, h3d,
              by omega, rfl, rfl, rfl, rfl⟩
            grind
      subst hk3
      refine ⟨c4, 5 + k4, .seq e3 e4, ⟨e4.wb_right, j + 1, by_omega, by_omega, h4c, h4d,
        ⟨fun r hr => (h4r r hr).trans ((h3r r hr).trans (hf2.1 r hr)),
          hrr4.trans (hrr3.trans hf2.2.1), hrm4.trans (hrm3.trans hf2.2.2.1),
          ho4.trans (ho3.trans hf2.2.2.2.1), fun a ha => ?_⟩, fun x hx => ?_⟩, ?_⟩
      · rw [hm4, hm3, Machine.upd_other _ _ _ by_omega]; exact hf2.2.2.2.2 a ha
      · zuedf
        by_cases hxe : bA + x = bA + e
        · rw [ite_eq_left hxe, ite_eq_left by_grind]
        · rw [ite_eq_right hxe, hm2 x hx]
          by_cases hex : ∃ i, i < j ∧ f^[i] d = x
          · obtain ⟨i, hi, hix⟩ := hex
            rw [ite_eq_left by_grind, ite_eq_left by_grind]
          grind
      · rw [hm4, hm3]
        have := unv_upd heN hme hdN
        omega)
    ⟨hw1, 0, Nat.zero_le _, by_simp_all, by_simp_all, by
      simp_all,
      ⟨fun r hr => h1r r ztnvb ztnvb, hrr1,
        hrm1, ho1, by_simp_all⟩,
      by simp_all⟩
  zulhp
  rw [hC'.zero, hcj] at htest
  have hjp : j = per f N d := by
    grind
  subst hjp
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hdj, hf', fun x hx => ?_⟩
  · grind
  · rw [hmj x hx]
    zucr
    apply propext
    constructor
    · rintro ⟨i, -, hi⟩; exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      obtain ⟨i', hi', hii⟩ := exists_lt_per_of_iterate hf hdN i
      grind
open Classical in
/-- **The face representatives**: afterwards `ATT[x]` is the least dart on the cycle of `x` under
`f x = FP[x]` (an injection of `[0, N)`), for all `x < N`. -/
theorem attStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bF bA N : ℕ} (hF : c.nreg 130530 = bF)
    (hA : c.nreg 130531 = bA) (hN : c.nreg 130532 = N) {f : ℕ → ℕ} (hf : InjOn f N)
    (hfm : ∀ x, x < N → c.nmem zttfz = f x)
    (hwA : bA + N ≤ W) (hwF : bF + N ≤ W) (hNW : N + 1 ≤ W)
    (hdisj : bA + N ≤ bF ∨ bF + N ≤ bA) :
    ∃ c' k, Exec P W attStmt c c' k ∧ k ≤ 40 * N + 12 ∧ WordsBounded W c' ∧
      PFr AttRG ztbbx c c' ∧
      ∀ x, x < N → c'.nmem ztctu = minOrb f x := by
  -- the fill with `N`
  obtain ⟨c1, k1, e1, hk1, hw1, h150, h151, h152, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130150 130531, .copyN 130151 130532, .copyN 130152 130532]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130150 = bA ∧ c1.nreg 130151 = N ∧
      c1.nreg 130152 = N ∧ PFr AttRG ztbbx c c1 := by
    exec_block
    refine ⟨rfl, by_omega, by_simp_all, by_simp_all,
      by simp_all, PFr.nreg ztffw ztez⟩
    zqbeq
  have hone1 := (hr1.1 _ ztjqq).trans hone
  obtain ⟨c2, k2, e2, hk2, hf2, hfill⟩ := fillStmt_exec (P := P) e1.wb_right hone1
    by_omega by_omega
  zubig

  have hr2 :=
    hr1.trans (hf2.mono (fun r hr => by unfold FillScr at hr; unfold AttRG; omega)
      by_simp_all)
  have e3 := Exec.constN (P := P) e2.wb_right 130533 0 by_omega
  set c3 := { c2 with nreg := upd c2.nreg 130533 0 }
  have hr3 : PFr AttRG ztbbx c c3 :=
    PFr.nreg hr2 (fun r hr => by
      zumwj; unfold AttRG at hr; grind)
  have hC : WalkCtx c bF bA N := ⟨hone, hzero, hF, hA, hN⟩
  -- the outer loop
  obtain ⟨c', k, e, ⟨hw', d, hd, hdN, hf', hI⟩, htest, hk⟩ := whileLtN_pot (P := P) (W := W)
    (a := 130533) (b := 130532) (body := attOuter)
    (fun c4 => WordsBounded W c4 ∧ ∃ d, c4.nreg 130533 = d ∧ d ≤ N ∧
      PFr AttRG ztbbx c c4 ∧
      ∀ x, x < N → c4.nmem ztctu = if minOrb f x < d then minOrb f x else N)
    (fun c4 => 12 * unv c4.nmem bA N + 20 * (N - c4.nreg 130533)) (fun c4 h => h.1)
    (fun c4 ⟨hw4, d, hd4, hdN, hf4, hI4⟩ htest => by
      have hC4 := hC.of_frame hf4.1
      rw [hd4, hC4.rN] at htest
      have hmd : minOrb f d ≤ d := minOrb_le d
      obtain ⟨c5, k5, e5, hk5, hw5, h5v, h5d, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
          ztjoq c4 c5 k5 ∧ k5 = 2 ∧
          WordsBounded W c5 ∧ c5.nreg 130537 = c4.nmem (bA + d) ∧ c5.nreg 130533 = d ∧
          (∀ r, ¬ AttRG r → c5.nreg r = c4.nreg r) ∧ c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧
          c5.output = c4.output ∧ c5.nmem = c4.nmem := by
        exec_block
        · zuohz; omega
        · refine ⟨rfl, by_omega, by config_simp; zuohz, by_simp_all,
            fun r hr => ?_, rfl, rfl, rfl, rfl⟩
          zqbeq
      zulhs
      have hf5 : PFr AttRG ztbbx c c5 :=
        ⟨fun r hr => (h5r r hr).trans (hf4.1 r hr), hrr5.trans hf4.2.1, hrm5.trans hf4.2.2.1,
          ho5.trans hf4.2.2.2.1, fun a ha => by rw [hm5]; exact hf4.2.2.2.2 a ha⟩
      by_cases hvis : c5.nreg 130537 < c5.nreg 130532
      · -- visited: skip
        have hlt : minOrb f d < d := by
          zuexq

        have e6 := Exec.addN (P := P) hw5 130533 130533 130001 (by
          rw [h5d, hC5.one]; omega)
        refine ⟨_, k5 + ztpsh, .seq e5 (.seq (.ifLtN_true hvis (.skip hw5)) e6),
          ⟨e6.wb_right, d + 1, by simp [h5d, hC5.one], by_omega, PFr.nreg hf5 (fun r hr => by
            zumwj; unfold AttRG at hr; grind),
            fun x hx => ?_⟩, ?_⟩
        · show c5.nmem _ = _
          rw [hm5, hI4 x hx]
          by_cases hx1 : minOrb f x < d
          · grind
          · have hne : ztskm := by
              zuq
              have horb := h ▸ minOrb_orb x
              have := minOrb_eq hf htest horb
              omega
            grind
        · simp only [Machine.upd_same, h5d, hC5.one, hm5]
          omega
      · -- a new cycle: walk
        have hmdd : minOrb f d = d := by
          zuexq

        have hfresh : ∀ i, i < per f N d → c5.nmem ztmco = N := by
          zug
          have hxN := hf.iterate_lt i htest
          rw [hm5, hI4 _ hxN, minOrb_eq hf htest ⟨i, rfl⟩, hmdd, ite_eq_right by_omega]
        obtain ⟨c6, k6, e6, hk6, hw6, h6d, hf6, hm6⟩ := walkS_exec hw5 hC5 h5d htest hf
          (fun x hx => by rw [hm5, hf4.2.2.2.2 _ by_omega]; simp_all) hwA hwF hdisj
          hfresh
        have hC6 := hC5.of_frame hf6.1
        have e7 := Exec.addN (P := P) hw6 130533 130533 130001 (by
          rw [h6d, hC6.one]; omega)
        refine ⟨_, k5 + (k6 + 2 + 1), .seq e5 (.seq (.ifLtN_false hvis e6) e7),
          ⟨e7.wb_right, d + 1, by simp [h6d, hC6.one], by_omega,
            PFr.nreg (hf5.trans hf6) (fun r hr => by
              zumwj; unfold AttRG at hr; grind),
            fun x hx => ?_⟩, ?_⟩
        · show c6.nmem _ = _
          rw [hm6 x hx]
          by_cases horb : Orb f d x
          · rw [ite_eq_left horb, minOrb_eq hf htest horb, hmdd, ite_eq_left by_omega]
          · rw [ite_eq_right horb, hm5, hI4 x hx]
            have hne : ztskm := fun h => horb (h ▸ minOrb_orb x)
            grind
        · simp only [Machine.upd_same, h6d, hC6.one]
          grind)
    ⟨e3.wb_right, 0, by_rfl, Nat.zero_le _, hr3, fun x hx => by
      grind⟩
  zulhp
  rw [hd, hC'.rN] at htest
  have hdN' : d = N := by_omega
  rw [hdN'] at hI
  zultc
  refine ⟨c', 3 + ztocd, .seq e1 ztgwz, ?_, hw', hf', fun x hx => ?_⟩
  · have : 12 * unv c3.nmem bA N ≤ 12 * N := Nat.mul_le_mul_left _ (unv_le _ _ _)
    omega
  · rw [hI x hx, ite_eq_left (lt_of_le_of_lt (minOrb_le x) hx)]
end att
end
end Chazelle.Core.Cluster
end
section
set_option hygiene false
local macro "zqbjt" : tactic => `(tactic| rw [hf8 _ by_omega by_omega, hf7 _ by_omega by_omega, hf6 _ by_omega])
local macro "zqbju" : tactic => `(tactic| (all_goals try (config_simp; omega)))
set_option hygiene true

/-!
# WP-I, part 43: the setup program

`setupStmt` computes the global values of `GV` in the global registers (see
`ClusterSetup.lean`) without touching memory; `setupStmt_exec`.
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
def setupA : Stmt := block [.copyN 130010 130000, .copyN 130011 130001, .copyN 130012 130002,
  .copyN 130013 130003, .constN 130001 1, .constN 130009 0, .addN 130014 130012 130012,
  .loadN 130021 130010, .addN 130090 130010 130001, .loadN 130022 130090,
  .addN 130090 130090 130001, .loadN 130023 130090, .copyN 130020 9999]

/-- `k' := min k μ`. -/
def kminS : Stmt := .ifLtN 130013 130011 (.instr (.copyN 130015 130013))
  (.instr (.copyN 130015 130011))

/-- One step of `s := min (k' k') μ`. -/
def sBody : Stmt := .seq (.instr (.addN 130016 130016 130015))
  (.seq (.ifLtN 130011 130016 (.instr (.copyN 130016 130011)) .skip)
    (.instr (.addN 130091 130091 130001)))

/-- `s := min (k' k') μ` by clamped additions. -/
def sS : Stmt := .seq ztkqq (.whileLtN 130091 130015 sBody)

/-- One doubling. -/
def LBody : Stmt := block [.addN 130018 130018 130018, .addN 130017 130017 130001]

/-- `L := clog₂ (N + μ + 1)`, `P := 2 ^ L`. -/
def LS : Stmt := .seq (block [.constN 130017 0, .constN 130018 1, .addN 130092 130014 130011,
  .addN 130092 130092 130001]) (.whileLtN 130018 130092 LBody)

/-- `U := N + μ + P + 3`. -/
def UB : Stmt := block [.addN 130019 130014 130011, .addN 130019 130019 130018,
  .constN 130093 3, .addN 130019 130019 130093]

/-- The slot bases. -/
def basesB : Stmt := block [
  .copyN 130030 130020,
  .addN 130031 130030 130019,
  .addN 130032 130031 130019,
  .addN 130033 130032 130019,
  .addN 130034 130033 130019,
  .addN 130035 130034 130019,
  .addN 130036 130035 130019,
  .addN 130037 130036 130019,
  .addN 130038 130037 130019,
  .addN 130039 130038 130019,
  .addN 130040 130039 130019,
  .addN 130041 130040 130019,
  .addN 130042 130041 130019,
  .addN 130043 130042 130019,
  .addN 130044 130043 130019,
  .addN 130045 130044 130019,
  .addN 130046 130045 130019,
  .addN 130047 130046 130019,
  .addN 130048 130047 130019,
  .addN 130049 130048 130019,
  .addN 130050 130049 130019,
  .addN 130051 130050 130019,
  .addN 130052 130051 130019,
  .addN 130053 130052 130019,
  .addN 130054 130053 130019,
  .addN 130055 130054 130019,
  .addN 130056 130055 130019,
  .addN 130057 130056 130019,
  .addN 130058 130057 130019,
  .addN 130059 130058 130019,
  .addN 130060 130059 130019,
  .addN 130061 130060 130019,
  .addN 130062 130061 130019,
  .addN 130063 130062 130019,
  .addN 130064 130063 130019,
  .addN 130065 130064 130019,
  .addN 130066 130065 130019,
  .addN 130067 130066 130019,
  .addN 130068 130067 130019,
  .addN 130069 130068 130019,
  .addN 130070 130069 130019,
  .addN 130071 130070 130019,
  .addN 130072 130071 130019,
  .addN 130073 130072 130019,
  .addN 130074 130073 130019,
  .addN 130075 130074 130019,
  .addN 130076 130075 130019,
  .addN 130077 130076 130019,
  .addN 130078 130077 130019,
  .addN 130079 130078 130019,
  .addN 130080 130079 130019,
  .addN 130081 130080 130019,
  .addN 130082 130081 130019,
  .addN 130083 130082 130019,
  .addN 130084 130083 130019]

/-- One step of `L U`. -/
def LUBody : Stmt := block [.addN 130026 130026 130019, .addN 130094 130094 130001]

/-- `L U` by repeated addition. -/
def LUS : Stmt := .seq ztkqr (.whileLtN 130094 130017 LUBody)

/-- The tables. -/
def endB : Stmt := block [.addN 130085 130084 130026, .addN 130086 130085 130026]

/-- **The setup.** -/
def setupStmt : Stmt := .seq setupA (.seq kminS (.seq sS (.seq LS (.seq UB (.seq basesB
  (.seq LUS endB))))))

/-- The registers written by the setup. -/
def SetRG (r : ℕ) : Prop := r = 130001 ∨ r = 130009 ∨ (130010 ≤ r ∧ r ≤ 130099)
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 2000000 in
theorem setupA_exec (hw : WordsBounded W c) (hB2 : c.nreg 130000 + 2 ≤ W)
    (hE : c.nreg 130002 + c.nreg 130002 ≤ W) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W setupA c c' k ∧ k = 13 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130010 = c.nreg 130000 ∧ c'.nreg 130011 = c.nreg 130001 ∧
      c'.nreg 130012 = c.nreg 130002 ∧ c'.nreg 130013 = c.nreg 130003 ∧
      c'.nreg 130001 = 1 ∧ c'.nreg 130009 = 0 ∧
      c'.nreg 130014 = 2 * c.nreg 130002 ∧ c'.nreg 130020 = c.nreg 9999 ∧
      c'.nreg 130021 = c.nmem ztvhn ∧ c'.nreg 130022 = c.nmem ztrll ∧
      c'.nreg 130023 = c.nmem ztrlm ∧
      ztivt ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold setupA
  exec_block
  zqbju
  refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩
  all_goals try (config_simp; done)
  zqbju
  zumrk
  zubi
  repeat (rw [Machine.upd_other _ _ _ by_omega])
theorem kminS_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W kminS c c' k ∧ k ≤ 3 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130015 = min (c.nreg 130013) (c.nreg 130011) ∧
      (∀ r, r ≠ 130015 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold kminS
  by_cases h : c.nreg 130013 < c.nreg 130011
  · have e := Exec.copyN (P := P) hw 130015 130013
    refine ⟨_, 1 + 1, .ifLtN_true h e, by_omega, e.wb_right, rfl, ?_, fun r hr => ?_, rfl, rfl,
      rfl⟩
    · zudbz
    simp_all
  · have e := Exec.copyN (P := P) hw 130015 130011
    refine ⟨_, 1 + 2, .ifLtN_false h e, by_omega, e.wb_right, rfl, ?_, fun r hr => ?_, rfl, rfl,
      rfl⟩
    · simp_all
    simp_all

/-- One clamped addition. -/
theorem sBody_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {j a mu : ℕ} (hj : c.nreg 130091 = j) (hacc : c.nreg 130016 = min ztobw mu)
    (ha : c.nreg 130015 = a) (hmu : c.nreg 130011 = mu) (hW : mu + a ≤ W) (hjW : j + 1 ≤ W) :
    ∃ c' k, Exec P W sBody c c' k ∧ k ≤ 5 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130091 = j + 1 ∧ c'.nreg 130016 = min (ztl * a) mu ∧
      ztdbd ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : min ztobw mu + a ≤ W := by_omega
  have e1 := Exec.addN (P := P) hw 130016 130016 130015 by_omega
  set c1 := { c with nreg := upd c.nreg 130016 (c.nreg 130016 + c.nreg 130015) }
  have hsa : ztl * a = j * a + a := by_ring
  by_cases h : c1.nreg 130011 < c1.nreg 130016
  · have e2 := Exec.copyN (P := P) e1.wb_right 130016 130011
    set c2 := { c1 with nreg := upd c1.nreg 130016 _ }
    have e3 := Exec.addN (P := P) e2.wb_right 130091 130091 130001 (by
      simp only [c2, c1, Machine.upd_other _ _ _ ztkxf,
        Machine.upd_other _ _ _ ztkxb, hj, hone]; omega)
    refine ⟨_, 1 + (ztcse + 1), .seq e1 (.seq ztspi e3), by_omega, e3.wb_right,
      rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · simp [c2, c1, hj, hone]
    · simp only [c1, c2, Machine.upd_same, Machine.upd_other _ _ _
        ztkxe, Machine.upd_other _ _ _
        ztkxd] at h ⊢
      omega
    · simp only [c1, c2, Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
  · have e3 := Exec.addN (P := P) e1.wb_right 130091 130091 130001 (by
      simp only [c1, Machine.upd_other _ _ _ ztkxf,
        Machine.upd_other _ _ _ ztkxb, hj, hone]; omega)
    refine ⟨_, 1 + (ztdeu + 1), .seq e1 (.seq (.ifLtN_false h (.skip e1.wb_right)) e3),
      by omega, e3.wb_right, rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · simp [c1, hj, hone]
    · simp only [c1, Machine.upd_same, Machine.upd_other _ _ _
        ztkxe, Machine.upd_other _ _ _
        ztkxd] at h ⊢
      omega
    · simp only [c1, Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]

/-- `s := min (a a) μ`. -/
theorem sS_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1) {a mu : ℕ}
    (ha : c.nreg 130015 = a) (hmu : c.nreg 130011 = mu) (hW : mu + a + 1 ≤ W) :
    ∃ c' k, Exec P W sS c c' k ∧ k ≤ 7 * a + 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130016 = min (a * a) mu ∧
      ztdbd ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sS
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, h16, h91, hr1, hrr1, hrm1, ho1⟩ :
      ∃ c1 k1, Exec P W ztkqq c c1 k1 ∧ k1 = 2 ∧
        WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130016 = 0 ∧ c1.nreg 130091 = 0 ∧
        (∀ r, r ≠ 130016 → r ≠ 130091 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
        c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try omega
    simp_all
  obtain ⟨c', k, e, hk, hw', hi', hn', h16', hfr', hm', hrr', hrm', ho'⟩ := forN (P := P) (W := W)
    (ri := 130091) (rn := 130015) (body := sBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130091 = j ∧ c'.nreg 130015 = a ∧
      c'.nreg 130016 = min ztobw mu ∧
      ztdbd ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    a 5 zthd
    (fun j c2 hj ⟨hw2, hi2, ha2, hacc2, hfr2, hm2, hrr2, hrm2, ho2⟩ => by
      obtain ⟨c3, k3, e3, hk3, hw3, hm3, hi3, hacc3, hfr3, hrr3, hrm3, ho3⟩ :=
        sBody_exec (P := P) hw2 ((hfr2 _ by_omega by_omega).trans hone) hi2 hacc2 ha2
          ((hfr2 _ by_omega by_omega).trans hmu) by_omega by_omega
      grind)
    (j₀ := 0) ⟨hw1, h91, by_simp_all, by_omega,
      hr1, hm1, hrr1, hrm1, ho1⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by_omega, hw', hm', h16', hfr', hrr', hrm', ho'⟩

/-- `L := clog₂ x`, `P := 2 ^ L` for `x = N + μ + 1`. -/
theorem LS_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1) {x : ℕ}
    (hx : c.nreg 130014 + c.nreg 130011 + 1 = x) (hW : 2 * x ≤ W) :
    ∃ c' k, Exec P W LS c c' k ∧ k ≤ 4 * Nat.clog 2 x + 6 ∧ WordsBounded W c' ∧
      c'.nmem = c.nmem ∧ c'.nreg 130017 = Nat.clog 2 x ∧ c'.nreg 130018 = 2 ^ Nat.clog 2 x ∧
      (∀ r, r ≠ 130017 → r ≠ 130018 → r ≠ 130092 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold LS
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, h17, h18, h92, hr1, hrr1, hrm1, ho1⟩ :
      ∃ c1 k1, Exec P W (block [.constN 130017 0, .constN 130018 1, .addN 130092 130014 130011,
        .addN 130092 130092 130001]) c c1 k1 ∧ k1 = 4 ∧
        WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130017 = 0 ∧ c1.nreg 130018 = 1 ∧
        c1.nreg 130092 = x ∧
        (∀ r, r ≠ 130017 → r ≠ 130018 → r ≠ 130092 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
        c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    zqbju
    simp_all
  have h2 : (1 : ℕ) < 2 := by_omega
  obtain ⟨c', k, e, ⟨hw', j, hj, hp', hjx, hfr', hm', hrr', hrm', ho'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 130018) (b := 130092) (body := LBody)
    (fun c' => WordsBounded W c' ∧ ∃ j, c'.nreg 130017 = j ∧ c'.nreg 130018 = 2 ^ j ∧
      j ≤ Nat.clog 2 x ∧
      (∀ r, r ≠ 130017 → r ≠ 130018 → c'.nreg r = c1.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    (fun c' => 4 * (Nat.clog 2 x - c'.nreg 130017)) ztbms
    (fun c2 ⟨hw2, j, hj2, hp2, hjx2, hfr2, hm2, hrr2, hrm2, ho2⟩ htest => by
      have hx2 : c2.nreg 130092 = x := by_simp_all
      rw [hp2, hx2] at htest
      have hjc := (Nat.lt_clog_iff_pow_lt h2).mpr htest
      zukej
      have hj2p : j < 2 ^ j := Nat.lt_two_pow_self
      unfold LBody
      exec_block
      · omega
      · config_simp; omega
      · refine ⟨⟨by_omega, j + 1, by_simp_all, by config_simp; omega,
          by omega, fun r h1 h2 => ?_, hm2, hrr2, hrm2, ho2⟩, ?_⟩
        · simp_all
        · config_simp; omega)
    ⟨hw1, 0, h17, by_omega, Nat.zero_le _, fun _ _ _ => rfl, hm1, hrr1, hrm1, ho1⟩
  have hx' : c'.nreg 130092 = x := by_simp_all
  rw [hp', hx'] at htest
  have hjx' : Nat.clog 2 x ≤ j := (Nat.clog_le_iff_le_pow h2).mpr by_omega
  have hjeq : j = Nat.clog 2 x := by_omega
  subst hjeq
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hm', hj, hp', fun r h1 h2 h3 => ?_, hrr', hrm', ho'⟩
  · omega
  simp_all

/-- `U`. -/
theorem UB_exec (hw : WordsBounded W c)
    (hW : c.nreg 130014 + c.nreg 130011 + c.nreg 130018 + 3 ≤ W) :
    ∃ c' k, Exec P W UB c c' k ∧ k = 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130019 = c.nreg 130014 + c.nreg 130011 + c.nreg 130018 + 3 ∧
      (∀ r, r ≠ 130019 → r ≠ 130093 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold UB
  exec_block
  zqbju
  simp_all

/-- `L U`. -/
theorem LUS_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1) {L U : ℕ}
    (hL : c.nreg 130017 = L) (hU : c.nreg 130019 = U) (hW : L * U + L + 1 ≤ W) :
    ∃ c' k, Exec P W LUS c c' k ∧ k ≤ 4 * L + 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130026 = L * U ∧
      ztgsi ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold LUS
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, h26, h94, hr1, hrr1, hrm1, ho1⟩ :
      ∃ c1 k1, Exec P W ztkqr c c1 k1 ∧ k1 = 2 ∧
        WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130026 = 0 ∧ c1.nreg 130094 = 0 ∧
        (∀ r, r ≠ 130026 → r ≠ 130094 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
        c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try omega
    simp_all
  obtain ⟨c', k, e, hk, hw', hi', hn', h26', hfr', hm', hrr', hrm', ho'⟩ := forN (P := P) (W := W)
    (ri := 130094) (rn := 130017) (body := LUBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130094 = j ∧ c'.nreg 130017 = L ∧
      c'.nreg 130026 = j * U ∧
      ztgsi ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    L 2 zthd
    (fun j c2 hj ⟨hw2, hi2, hL2, hacc2, hfr2, hm2, hrr2, hrm2, ho2⟩ => by
      have hU2 : c2.nreg 130019 = U := by_simp_all
      zukej
      have hjU : ztl * U ≤ L * U := Nat.mul_le_mul_right _ by_omega
      unfold LUBody
      exec_block
      · grind
      · config_simp; omega
      · refine ⟨le_refl _, by_omega, by_simp_all, by_simp_all,
          by config_simp; grind, fun r h1 h2 => ?_, hm2, hrr2, hrm2, ho2⟩
        simp_all)
    (j₀ := 0) ⟨hw1, h94, by_simp_all, by_omega,
      hr1, hm1, hrr1, hrm1, ho1⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by_omega, hw', hm', h26', hfr', hrr', hrm', ho'⟩

/-- The table bases. -/
theorem endB_exec (hw : WordsBounded W c)
    (hW : c.nreg 130084 + c.nreg 130026 + c.nreg 130026 ≤ W) :
    ∃ c' k, Exec P W endB c c' k ∧ k = 2 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130085 = c.nreg 130084 + c.nreg 130026 ∧
      c'.nreg 130086 = c.nreg 130084 + c.nreg 130026 + c.nreg 130026 ∧
      (∀ r, r ≠ 130085 → r ≠ 130086 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold endB
  exec_block
  zqbju
  simp_all
set_option maxHeartbeats 8000000 in
/-- The slot bases. -/
theorem basesB_exec (hw : WordsBounded W c) {A0 U : ℕ} (hA : c.nreg 130020 = A0)
    (hU : c.nreg 130019 = U) (hW : A0 + 54 * U ≤ W) :
    ∃ c' k, Exec P W basesB c c' k ∧ k = 55 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      (∀ j, j ≤ 54 → c'.nreg ztsrb = A0 + j * U) ∧
      (∀ r, ¬ ztnee → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold basesB
  exec_block
  zqbju
  refine ⟨rfl, by_omega, rfl, fun j hj => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · interval_cases j <;> (config_simp; omega)
  · zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])

/-- The global values read from the entry configuration. -/
def gOf (c : Config) : GV := ⟨c.nreg 130000, c.nreg 130001, c.nreg 130002, c.nreg 130003,
  c.nreg 9999, c.nmem ztvhn, c.nmem ztrll, c.nmem ztrlm⟩
theorem GV.two_pow_L (g : GV) : g.N + g.μ + 1 ≤ 2 ^ g.L :=
  Nat.le_pow_clog by_omega _
theorem GV.U_eq (g : GV) : g.U = g.N + g.μ + 2 ^ g.L + 3 := rfl
theorem GV.U_ge (g : GV) : g.N + g.μ + 3 ≤ g.U := by
  zuoue; simp
theorem GV.P_le_U (g : GV) : 2 ^ g.L ≤ g.U := by
  zuoue; omega
theorem GV.END_eq (g : GV) : g.END = g.A0 + 54 * g.U + 2 * ztesx := rfl
theorem GV.base_eq (g : GV) (j : ℕ) : g.base j = g.A0 + j * g.U := rfl
theorem GV.L_le_U (g : GV) : g.L ≤ g.U := by
  have := Nat.lt_two_pow_self (n := g.L)
  unfold GV.U; omega

/-- **The setup.** -/
theorem setupStmt_exec (hw : WordsBounded W c) (hB2 : c.nreg 130000 + 2 ≤ W)
    (hEND : (gOf c).END ≤ W) :
    ∃ c' k, Exec P W setupStmt c c' k ∧ k ≤ 7 * (gOf c).μ + 8 * (gOf c).L + 100 ∧
      WordsBounded W c' ∧ c'.nmem = c.nmem ∧ GR ztvre c' ∧
      ztivt ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zujmx
  zuiwr
  zuiwk
  have hLUm : g.L * g.U ≥ g.L := Nat.le_mul_of_pos_right _ (by unfold GV.U; omega)
  have hEND' : g.A0 + 54 * g.U + 2 * ztesx ≤ W := hEND
  have hUdef : ztlax := rfl
  have hNdef : ztsip := rfl
  have hk' : ztsiq := min_le_right _ _
  have hk'def : g.k' = min g.k g.μ := rfl
  have hsdef : g.s = min _ g.μ := rfl
  have hLdef : g.L = Nat.clog 2 _ := rfl
  have e0 : g.B = c.nreg 130000 := rfl
  have e1 : g.μ = c.nreg 130001 := rfl
  have e2 : g.E = c.nreg 130002 := rfl
  have e3 : g.k = c.nreg 130003 := rfl
  have e4 : g.A0 = c.nreg 9999 := rfl
  -- inputs
  obtain ⟨c1, k1, x1, hk1, hw1, hm1, r10, r11, r12, r13, r01, r09, r14, r20, r21, r22, r23, hf1,
    hrr1, hrm1, ho1⟩ := setupA_exec (P := P) hw hB2 by_omega by_omega
  -- k'
  obtain ⟨c2, k2, x2, hk2, hw2, hm2, r15, hf2, hrr2, hrm2, ho2⟩ := kminS_exec (P := P) hw1
  have q2 := hf2
  -- s
  obtain ⟨c3, k3, x3, hk3, hw3, hm3, r16, hf3, hrr3, hrm3, ho3⟩ := sS_exec (P := P) hw2
    by_grind (a := g.k') (mu := g.μ)
    by_omega by_grind by_omega
  -- L
  obtain ⟨c4, k4, x4, hk4, hw4, hm4, r17, r18, hf4, hrr4, hrm4, ho4⟩ := LS_exec (P := P) hw3
    by_grind (x := g.N + g.μ + 1)
    by_grind by_omega
  rw [← hLdef] at r17 r18 hk4
  -- U
  obtain ⟨c5, k5, x5, hk5, hw5, hm5, r19, hf5, hrr5, hrm5, ho5⟩ := UB_exec (P := P) hw4
    by_grind
  have hU5 : c5.nreg 130019 = g.U := by
    grind
  -- the bases
  have hA5 : c5.nreg 130020 = g.A0 := by
    grind
  obtain ⟨c6, k6, x6, hk6, hw6, hm6, rb6, hf6, hrr6, hrm6, ho6⟩ := basesB_exec (P := P) hw5 hA5
    hU5 by_omega
  -- L U
  obtain ⟨c7, k7, x7, hk7, hw7, hm7, r26, hf7, hrr7, hrm7, ho7⟩ := LUS_exec (P := P) hw6
    (L := g.L) (U := g.U)
    by_grind
    by_grind
    by_grind by_omega
  obtain ⟨c8, k8, x8, hk8, hw8, hm8, r85, r86, hf8, hrr8, hrm8, ho8⟩ := endB_exec (P := P) hw7
    (by rw [hf7 _ by_omega by_omega, rb6 54 le_rfl, r26]; omega)
  -- the registers at the end
  have back : ∀ r, r ≠ 130085 → r ≠ 130086 → r ≠ 130026 → r ≠ 130094 →
      ¬ ztnee → r ≠ 130019 → r ≠ 130093 → r ≠ 130017 → r ≠ 130018 →
      r ≠ 130092 → r ≠ 130016 → r ≠ 130091 → r ≠ 130015 → c8.nreg r = c1.nreg r := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    rw [hf8 r a1 a2, hf7 r a3 a4, hf6 r a5, hf5 r a6 a7, hf4 r a8 a9 a10, hf3 r a11 a12, q2 r a13]
  refine ⟨c8, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + zttqm))))),
    .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 (.seq x6 (.seq x7 x8)))))), ?_, hw8, ?_, ?_,
    fun r hr => ?_, ?_, ?_, ?_⟩
  · omega
  · grind
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_,
      ?_, ?_⟩
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; omega
    · rw [hf8 _ by_omega by_omega, hf7 _ by_omega by_omega, hf6 _ by_omega,
        hf5 _ by_omega by_omega, hf4 _ by_omega by_omega by_omega,
        hf3 _ by_omega by_omega, r15, r13, r11]; rfl
    · rw [hf8 _ by_omega by_omega, hf7 _ by_omega by_omega, hf6 _ by_omega,
        hf5 _ by_omega by_omega, hf4 _ by_omega by_omega by_omega, r16]; rfl
    · rw [hf8 _ by_omega by_omega, hf7 _ by_omega by_omega, hf6 _ by_omega,
        hf5 _ by_omega by_omega, r17]
    · rw [hf8 _ by_omega by_omega, hf7 _ by_omega by_omega, hf6 _ by_omega,
        hf5 _ by_omega by_omega, r18]
    · zqbjt
      omega
    · zqbjt
      omega
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; exact r21
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; exact r22
    · rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega by_omega by_omega by_omega]; exact r23
    · grind
    · rw [hf8 _ by_omega by_omega, hf7 _ by_omega by_omega, rb6 j hj]; rfl
    · rw [r85, hf7 _ by_omega by_omega, rb6 54 le_rfl, r26]
    · rw [r86, hf7 _ by_omega by_omega, rb6 54 le_rfl, r26]; unfold GV.END; ring
  · zumrk
    rw [back _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega by_omega by_omega by_omega by_omega]
    exact hf1 r ztqgh
  · grind
  · grind
  grind
end proofs
end
end Chazelle.Core.Cluster
end
section
set_option hygiene false
local macro "zqbkf" : tactic => `(tactic| (have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3))
local macro "zqbkg" : tactic => `(tactic| (simp only
                                           unfold StARG at hr
                                           repeat (rw [Machine.upd_other _ _ _ (by omega)])))
local macro "zqbkh" : tactic => `(tactic| refine ⟨rfl, by_omega, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, by_simp_all⟩⟩)
local macro "zqbki" : tactic => `(tactic| (have hU := g.U_ge
                                           have hE := g.END_eq))
local macro "zqbkj" : tactic => `(tactic| rw [hf6.2.2.2.2 _ by_omega, hf5.2.2.2.2 _ by_omega, hf4.2.2.2.2 _ by_omega])
local macro "zqbkk" : tactic => `(tactic| (have hLU := g.L_le_U
                                           have hLμ : ztpow := Nat.mul_le_mul_left _ by_omega))
set_option hygiene true

/-!
# WP-I, part 44: stage A — the first darts, the primal search and the level-ancestor table

After the setup: `ZERO := 0` (slot `1`, `N` cells), `LAB := μ` (slot `2`), `FIRST` (slot `0`),
the primal breadth-first search from vertex `0` (levels in slot `3`, parent darts in slot `4`,
queue in slot `5`), the parent array `PV` (slot `6`) and the table `UPT` of its powers.

* `fillWith`: fill `[b, b + n)` with a value, all three read from registers;
* `primalEnv_enc`: the stored input map with its `first` array encodes `M`.
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap
@[expose] public section
def fillWith (rb rn rv : ℕ) : Stmt :=
  .seq zthss fillStmt

/-- The registers of `fillWith`. -/
def FillRG (r : ℕ) : Prop := 130150 ≤ r ∧ r ≤ 130154
section proofs
variable {P : Polygon} {W : ℕ}
theorem fillWith_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {rb rn rv b n x : ℕ} (hb : c.nreg rb = b) (hn : c.nreg rn = n) (hx : c.nreg rv = x)
    (_hrb : ¬ FillRG rb) (hrn : ¬ FillRG rn) (hrv : ¬ FillRG rv)
    (hwb : b + n ≤ W) (hwn : n + 1 ≤ W) :
    ∃ c' k, Exec P W (fillWith rb rn rv) c c' k ∧ k ≤ 5 * n + 6 ∧ WordsBounded W c' ∧
      PFr FillRG ztecd c c' ∧ ∀ i, i < n → c'.nmem ztbcn = x := by
  unfold fillWith
  unfold FillRG at _hrb hrn hrv
  obtain ⟨c3, k3, e3, hk3, hw3, r150, r151, r152, hone3, hf3⟩ : ∃ c3 k3, Exec P W
      zthss c c3 k3 ∧ k3 = 3 ∧
      WordsBounded W c3 ∧ c3.nreg 130150 = b ∧ c3.nreg 130151 = n ∧ c3.nreg 130152 = x ∧
      c3.nreg 130001 = 1 ∧ PFr FillRG ztecd c c3 := by
    exec_block
    zqbkh
    all_goals (zumwj; (try unfold FillRG at hr); split_ifs <;> omega)
  obtain ⟨c', k, e, hk, hf', hv⟩ := fillStmt_exec (P := P) hw3 hone3
    by_omega by_omega
  rw [r150, r151] at hf'
  rw [r150, r151, r152] at hv
  rw [r151] at hk
  have hf'' : PFr FillRG ztecd c3 c' :=
    hf'.mono (fun r h => by unfold FillScr at h; unfold FillRG; omega) by_omega
  exact ⟨c', k3 + k, .seq e3 e, by_omega, e.wb_right, hf3.trans hf'', hv⟩
end proofs

/-! ## The input map as a rotation system -/
section enc
variable {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)}

/-- **The stored input map encodes `M`.** -/
theorem primalEnv_enc {m : ℕ → ℕ} {bO bR bV bF bDB bVB : ℕ}
    (h : MapArrays m bO bR bV μ N M) (hF : ∀ u, u < μ → m ztdts < N ∧ m ztzko = u) :
    EnvEnc (primalEnv m bO bR bV bF bDB bVB μ N) M ztgjr ztgiy := by
  refine ⟨fun v => v.2, fun v w h => Fin.ext h, fun u hu => ⟨⟨u, hu⟩, rfl⟩, fun d => d.2,
    fun d e h => Fin.ext h, fun e he => ⟨⟨e, he⟩, rfl⟩, fun d => ?_, fun d => ?_, fun d => ?_,
    fun v => ?_⟩
  · show view m bO N d = _
    rw [view_lt d.2, h.opp d.2]
  · show view m bR N d = _
    zuinc
  · show view m bV N d = _
    rw [view_lt d.2, h.vert d.2]
  · obtain ⟨h1, h2⟩ := hF v v.2
    refine ⟨⟨m _, h1⟩, by show view m bF μ v = _; zunuu, ?_⟩
    zulvn
    rw [← h.vert h1]; exact h2
end enc

/-! ## The phases -/

/-- The first darts. -/
def firstP : Stmt := .seq zthst
  firstStmt

/-- The primal search from `0` with label `0`. -/
def bfsP : Stmt := .seq (block [.copyN 130100 130021, .copyN 130101 130022, .copyN 130102 130023,
  .copyN 130103 130030, .copyN 130104 130031, .copyN 130105 130031, .copyN 130106 130032,
  .copyN 130107 130033, .copyN 130108 130034, .copyN 130109 130035, .copyN 130110 130011,
  .constN 130111 0, .constN 130112 0]) bfsStmt

/-- The parent array `PV` (slot `6`). -/
def parP : Stmt := .seq (block [.copyN 130500 130023, .copyN 130501 130034, .copyN 130502 130036,
  .copyN 130503 130011]) parStmt

/-- The level-ancestor table `UPT`. -/
def upP : Stmt := .seq (block [.copyN 130510 130036, .copyN 130511 130084, .copyN 130512 130011,
  .copyN 130513 130017]) upStmt

/-- **Stage A.** -/
def stageA : Stmt := .seq (fillWith 130031 130014 130009) (.seq (fillWith 130032 130011 130011)
  (.seq firstP (.seq bfsP (.seq parP upP))))

/-- The registers written by stage A. -/
def StARG (r : ℕ) : Prop := ztnef ∨ ztbxr ∨
  (130221 ≤ r ∧ r ≤ 130226) ∨ (130500 ≤ r ∧ r ≤ 130519)

/-- The primal parent as a function on `ℕ`. -/
def upTf {μ N : ℕ} {F : Type} {M : CombMap ztemr F ztjiv} (T : SpanTree M) : ℕ → ℕ :=
  fun y => if h : y < μ then (T.parent ⟨y, h⟩ : ℕ) else 0
section phases
variable {P : Polygon} {W : ℕ}
variable {g : GV} {c : Config}
theorem firstP_exec (hw : WordsBounded W c) (hG : GR g c)
    (hvlt : ∀ d, d < g.N → c.nmem ztnzw < g.μ)
    (hsurj : ∀ u, u < g.μ → ∃ d, d < g.N ∧ c.nmem ztnzw = u)
    (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W firstP c c' k ∧ k ≤ 7 * g.N + 6 ∧ WordsBounded W c' ∧
      PFr StARG zthww c c' ∧
      ∀ u, u < g.μ → c'.nmem ztrk < g.N ∧ c.nmem (g.bV + c'.nmem ztrk) = u := by
  zueqs
  have hEND := g.END_eq
  have hb0 : g.base 0 = g.A0 := by rw [g.base_eq]; ring
  have hb00 := hG.rbase 0 by_omega
  unfold firstP
  obtain ⟨c1, k1, e1, hk1, hw1, r1, r2, r3, hone1, hf1⟩ : ∃ c1 k1, Exec P W
      zthst c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130221 = g.bV ∧ c1.nreg 130222 = g.base 0 ∧
      c1.nreg 130223 = g.N ∧ c1.nreg 130001 = 1 ∧
      PFr StARG zthww c c1 := by
    exec_block
    zqbkh
    · config_simp; exact hG.rV
    · simp_all
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · zumwj; unfold StARG at hr; grind
  obtain ⟨c', k, e, hk, hf', hI⟩ := firstStmt_exec (P := P) hw1 hone1 (bV := g.bV)
    (bF := g.base 0) (N := g.N) r1 r2 r3
    (nv := g.μ) (fun d hd => by zuoig; simp_all)
    (fun u hu => by
      obtain ⟨d, hd, hdu⟩ := hsurj u hu
      exact ⟨d, hd, by zuoig; omega⟩)
    by_omega by_omega by_omega by_omega
  refine ⟨c', k1 + k, .seq e1 e, by_omega, e.wb_right,
    hf1.trans (hf'.mono (fun r h => by unfold FirstRG at h; unfold StARG; omega) by_omega),
    fun u hu => ztbjy⟩
  have := (hI u hu).2
  rw [hf1.2.2.2.2 _ by_grind] at this
  omega

/-- The layout of the primal search. -/
def primalLay (g : GV) : Lay := ⟨g.bO, g.bR, g.bV, g.base 0, g.base 1, g.base 1, g.base 2,
  g.base 3, g.base 4, g.base 5, g.μ, g.N⟩
theorem primalLay_good (hμ : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0)
    (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    (primalLay g).Good W := by
  zqbki
  zqbkf
  have b4 := g.base_eq 4; have b5 := g.base_eq 5
  refine ztbij
  all_goals simp only [primalLay, Disj] at *
  · grind
  zuiqs
open Classical in
theorem bfsP_exec {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M) (hM : M.Connected) (hμ : 0 < g.μ)
    (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0)
    (hfirst : ∀ u, u < g.μ → c.nmem ztrk < g.N ∧
      c.nmem ztzlw = u)
    (hzero : ∀ d, d < g.N → c.nmem ztefe = 0)
    (hlab : ∀ v, v < g.μ → c.nmem ztdol = g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W bfsP c c' k ∧ k ≤ 70 * g.μ + 50 * g.N + 30 ∧ WordsBounded W c' ∧
      PFr StARG ztisl c c' ∧
      ∃ T : SpanTree M, (T.root : ℕ) = 0 ∧ (∀ v : Fin g.μ, c'.nmem ztjc = T.level v) ∧
        (∀ v, T.level v < g.μ) ∧
        (∀ v, v ≠ T.root → c'.nmem ztbvy < g.N ∧
          (T.par v : ℕ) = c.nmem (g.bO + c'.nmem ztbvy) ∧
          (T.parent v : ℕ) = c.nmem (g.bV + c'.nmem ztbvy)) ∧
        (∀ d : Fin g.N, T.level ztbyq ≤ T.level ztbmc + 1) := by
  zqbki
  zqbkf
  have b4 := g.base_eq 4; have b5 := g.base_eq 5; have b6 := g.base_eq 6
  set Y := primalLay g with hY
  have hYg : Y.Good W := primalLay_good hμN hO hR hV hW
  unfold bfsP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hR1, hf1⟩ : ∃ c1 k1, Exec P W (block [.copyN 130100 130021,
      .copyN 130101 130022, .copyN 130102 130023, .copyN 130103 130030, .copyN 130104 130031,
      .copyN 130105 130031, .copyN 130106 130032, .copyN 130107 130033, .copyN 130108 130034,
      .copyN 130109 130035, .copyN 130110 130011, .constN 130111 0, .constN 130112 0]) c c1 k1 ∧
      k1 = 13 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ Regs Y 0 0 c1 ∧
      PFr StARG ztisl c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, rfl, ztzv,
      ⟨fun r hr => ?fr, rfl, rfl, rfl, by_simp_all⟩⟩
    case fr =>
      zqbkg
    all_goals try (config_simp <;>
                   first
                   | exact hG.one
                   | exact hG.rO
                   | exact hG.rR
                   | exact hG.rV
                   | exact hG.rμ
                   | exact hG.rN
                   | exact hG.rbase 0 by_omega
                   | exact hG.rbase 1 by_omega
                   | exact hG.rbase 2 by_omega
                   | exact hG.rbase 3 by_omega
                   | exact hG.rbase 4 by_omega
                   | exact hG.rbase 5 by_omega)
  have hm1' : MapArrays c1.nmem g.bO g.bR g.bV g.μ g.N M := by_simp_all
  have henv : Y.env c1.nmem = primalEnv c1.nmem g.bO g.bR g.bV ztmkd zteac zteac
      g.μ g.N := rfl
  have hF1 : ∀ u, u < g.μ → c1.nmem ztrk < g.N ∧
      c1.nmem ztzlx = u := by_simp_all
  have hok : ztrzc := by rw [henv]; exact primalEnv_ok hm1' hF1
  have hpre : (Y.env c1.nmem).Pre 0 0 ztocr := by
    refine ⟨hok, hμ, ?_, hμ, fun w hw' _ => ?_⟩
    · show view c1.nmem zteac g.μ 0 ≠ 1
      rw [view_lt hμ, hm1, hzero 0 by_omega]; omega
    · show view c1.nmem _ g.μ w = g.μ
      rw [view_lt (show w < g.μ from hw'), hm1]; exact hlab w hw'
  obtain ⟨c', k, e, hk, ⟨hw', hfr', hI⟩, hht⟩ := bfs_exec (P := P) hYg hR1 hpre hw1
  zukuh
  have hGenc := primalEnv_enc (bDB := g.base 1) (bVB := g.base 1) hm1' hF1
  rw [← henv] at hGenc
  have hdb : ∀ d, d < g.N → (Y.env c1.nmem).db d ≠ 1 := by
    zuip
    show view c1.nmem zteac g.N d ≠ 1
    rw [view_lt hd, hm1, hzero d hd]; omega
  have hvb : ∀ v, v < g.μ → (Y.env c1.nmem).vb v ≠ 1 := by
    zuml
    show view c1.nmem zteac g.μ v ≠ 1
    rw [view_lt hv, hm1, hzero v by_omega]; omega
  obtain ⟨T, hroot, hlev, hpar, hhead, hlt⟩ := primal_tree hM hμ rfl hGenc hdb hvb hI
  -- the cost
  zugnd

  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hf1.trans ⟨fun r hr => hfr'.1 r (fun h => hr (by
      unfold Scr at h; unfold StARG; omega)), hfr'.2.1, hfr'.2.2.1, hfr'.2.2.2.1,
      fun a ha => hfr'.2.2.2.2 a (fun h => ha (by
        unfold Lay.Written at h; simp only [hY, primalLay] at h; omega))⟩, T, hroot,
      fun v => ?_, hlt, fun v hv => ?_, hhead⟩
  · have : (Y.env c1.nmem).N = g.N := rfl
    have : (Y.env c1.nmem).nv = g.μ := rfl
    omega
  · rw [hlev v]
    show _ = view c'.nmem (g.base 3) g.μ v
    zunuu
  · obtain ⟨h1, h2, h3⟩ := hpar v hv
    have hpv : parV Y c'.nmem v = c'.nmem ztbvy := by
      show view c'.nmem ztvqz g.μ v = _; zunuu
    rw [hpv] at h1 h2 h3
    refine ⟨h1, ?_, ?_⟩
    · zvmxx; show view c1.nmem g.bO g.N _ = _; zuoct
    · zvncq; show view c1.nmem g.bV g.N _ = _; zuoct
theorem parP_exec (hw : WordsBounded W c) (hG : GR g c) (hμ : 0 < g.μ)
    (hV : g.bV + g.N ≤ g.A0) (hpar : ∀ x, 1 ≤ x → x < g.μ → c.nmem ztrqv < g.N)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W parP c c' k ∧ k ≤ 9 * g.μ + 8 ∧ WordsBounded W c' ∧
      PFr StARG zthwz c c' ∧ c'.nmem (g.base 6) = 0 ∧
      ∀ x, 1 ≤ x → x < g.μ → c'.nmem ztlpg = c.nmem (g.bV + c.nmem ztrqv) := by
  zqbki
  have b4 := g.base_eq 4; have b6 := g.base_eq 6
  unfold parP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hzero1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130500 130023, .copyN 130501 130034, .copyN 130502 130036,
        .copyN 130503 130011]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130500 = g.bV ∧ c1.nreg 130501 = g.base 4 ∧ c1.nreg 130502 = g.base 6 ∧
      c1.nreg 130503 = g.μ ∧ c1.nreg 130001 = 1 ∧ c1.nreg 130009 = 0 ∧
      PFr StARG zthwz c c1 := by
    exec_block
    refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ztrg⟩
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.zero
                   | exact hG.rV
                   | exact hG.rμ
                   | exact hG.rbase 4 by_omega
                   | exact hG.rbase 6 by_omega)
    zqbkg
  obtain ⟨c', k, e, hk, hw', hf', h0, hx⟩ := parStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 r3
    hμ by_omega by_omega by_omega (fun x h1 h2 => by
      grind)
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw',
    hf1.trans (hf'.mono (fun r h => by unfold ParRG at h; unfold StARG; omega) by_omega),
    by omega,
    by simp_all⟩
theorem upP_exec (hw : WordsBounded W c) (hG : GR g c) (hμ : 0 < g.μ)
    (hL : 0 < g.L) (hpv : ∀ x, x < g.μ → c.nmem ztlpg < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W upP c c' k ∧ k ≤ 12 * g.μ * g.L + 7 * g.L + 16 ∧ WordsBounded W c' ∧
      PFr StARG ztezu c c' ∧
      ∀ j, j < g.L → ∀ x, x < g.μ → c'.nmem ztjwy =
        (fun y => c.nmem ztrqx)^[2 ^ j] x := by
  zqbki
  have b6 := g.base_eq 6
  zqbkk
  unfold upP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130510 130036, .copyN 130511 130084, .copyN 130512 130011,
        .copyN 130513 130017]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130510 = g.base 6 ∧ c1.nreg 130511 = g.A0 + 54 * g.U ∧ c1.nreg 130512 = g.μ ∧
      c1.nreg 130513 = g.L ∧ c1.nreg 130001 = 1 ∧
      PFr StARG ztezu c c1 := by
    exec_block
    refine ztxhz
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.rL
                   | exact hG.rμ
                   | exact hG.rbase 6 by_omega
                   | (rw [hG.rbase 54 by_omega]; rfl))
    zqbkg
  obtain ⟨c', k, e, hk, hw', hf', htab⟩ := upStmt_exec (P := P) hw1 hone1 r0 r1 r2 r3 hL
    ztqoj by_omega by_omega by_omega by_omega hμ
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw',
    hf1.trans (hf'.mono (fun r h => by unfold UpRG at h; unfold StARG; omega) by_omega),
    by simp_all⟩

/-- Iterates of functions agreeing on an invariant range agree there. -/
theorem iterate_congr_lt {f f' : ℕ → ℕ} {n : ℕ} (h : ∀ x, x < n → f x = f' x)
    (hf : ∀ x, x < n → f' x < n) (k : ℕ) : ∀ x, x < n → f^[k] x = f'^[k] x ∧ f'^[k] x < n := by
  induction k with
  | zero => intro x hx; exact by_simp_all
  | succ k ih =>
    zuh
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h x hx]
    zufeo
theorem upTf_lt {μ N : ℕ} {F : Type} {M : CombMap ztemr F ztjiv} (T : SpanTree M) {x : ℕ}
    (hx : x < μ) : upTf T x < μ := by
  zumvj

/-- **The facts of stage A.** -/
structure AF (g : GV) {F : Type} (M : CombMap ztbry F ztbrx) (T : SpanTree M)
    (m : ℕ → ℕ) : Prop where
  map : MapArrays m g.bO g.bR g.bV g.μ g.N M
  zero : ∀ d, d < g.N → m ztefe = 0
  first_lt : ∀ u, u < g.μ → m ztrk < g.N
  first_v : ∀ u, u < g.μ → m ztzly = u
  root : (T.root : ℕ) = 0
  lev : ∀ v : Fin g.μ, m ztjc = T.level v
  lev_lt : ∀ v : Fin g.μ, T.level v < g.μ
  par_lt : ∀ v : Fin g.μ, v ≠ T.root → m ztbvy < g.N
  par_eq : ∀ v : Fin g.μ, v ≠ T.root → (T.par v : ℕ) = m (g.bO + m ztbvy)
  pv : ∀ v : Fin g.μ, m ztrqw = T.parent v
  upt : ∀ j, j < g.L → ∀ x, x < g.μ →
    m ztjwy = ztqxy^[2 ^ j] x
  head_le : ∀ d : Fin g.N, T.level ztbyq ≤ T.level ztbmc + 1

/-- The addresses read by the facts of stage A. -/
def KeepA (g : GV) (a : ℕ) : Prop :=
  a < g.A0 + 2 * g.U ∨ (g.base 3 ≤ a ∧ a < g.base 5) ∨ (g.base 6 ≤ a ∧ a < g.base 7) ∨
    ztfry
theorem AF.congr {F : Type} {M : CombMap ztbry F ztbrx} {T : SpanTree M}
    {m m' : ℕ → ℕ} (h : AF g M T m) (hA : g.bO + g.N ≤ g.A0 ∧ g.bR + g.N ≤ g.A0 ∧
      g.bV + g.N ≤ g.A0) (he : ∀ a, KeepA g a → m' a = m a) : AF g M T m' := by
  zueqs
  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b3 := g.base_eq 3; have b4 := g.base_eq 4
  have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7
  have hLμ : ∀ j, j < g.L → j * g.μ + g.μ ≤ g.L * g.U := by
    zun
    have : ztl * g.μ ≤ g.L * g.U := Nat.mul_le_mul by_omega by_omega
    grind
  refine ⟨fun d => ?_, fun d hd => ?_, fun u hu => ?_, fun u hu => ?_, h.root, fun v => ?_,
    h.lev_lt, fun v hv => ?_, fun v hv => ?_, fun v => ?_, fun j hj x hx => ?_, h.head_le⟩
  · have hd := d.2
    rw [he _ ztbei, he _ ztbei,
      he _ ztbei]
    exact h.map d
  · zunau; exact h.zero d hd
  · zunau; exact h.first_lt u hu
  · have := h.first_lt u hu
    rw [he ztrk ztbei, he _ ztbei]
    exact h.first_v u hu
  · have := v.2; zunau; exact h.lev v
  · have := v.2; zunau; exact h.par_lt v hv
  · have := v.2; have := h.par_lt v hv
    rw [he ztbvy ztbei, he _ ztbei]
    exact h.par_eq v hv
  · have := v.2; zunau; exact h.pv v
  · have := hLμ j hj
    zunau; exact h.upt j hj x hx

/-- The memory written by stage A. -/
def WrA (g : GV) (a : ℕ) : Prop :=
  (g.A0 ≤ a ∧ a < g.A0 + 7 * g.U) ∨ ztfry
set_option maxHeartbeats 4000000 in
theorem stageA_exec {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M) (hM : M.Connected) (hμ : 0 < g.μ)
    (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0) (hL : 0 < g.L) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageA c c' k ∧ k ≤ 62 * g.N + 84 * g.μ + 12 * g.μ * g.L + 7 * g.L + 72 ∧
      WordsBounded W c' ∧ GR g c' ∧ PFr StARG zthsb c c' ∧ ∃ T, AF g M T c'.nmem := by
  zqbki
  zqbkk
  zqbkf
  have b4 := g.base_eq 4; have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7
  have hGR : ∀ {c1 : Config} {Am : ℕ → Prop}, PFr StARG Am c c1 → GR g c1 := fun hf =>
    hG.frame (fun r hr => hf.1 r (by unfold GRReg at hr; unfold StARG; omega))
  have hmono : ∀ {c0 c1 : Config} {Am : ℕ → Prop}, PFr StARG Am c0 c1 → (∀ a, Am a → WrA g a) →
      PFr StARG _ c0 c1 := fun hf hA => hf.mono by_simp_all hA
  -- `ZERO := 0`
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 1 by_omega) hG.rN hG.zero ztpc ztpc
    ztpc by_omega by_omega
  have hf1' : PFr StARG zthsb c c1 := hmono (hf1.mono (fun r h => by
    unfold FillRG at h; unfold StARG; omega) (fun a h => h)) (fun a h => by unfold WrA; omega)
  have hG1 := hGR hf1'
  -- `LAB := μ`
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, hl2⟩ := fillWith_exec (P := P) hw1 hG1.one
    (hG1.rbase 2 by_omega) hG1.rμ hG1.rμ ztpc ztpc
    ztpc by_omega by_omega
  have hf2' : PFr StARG zthsb c1 c2 := hmono (hf2.mono (fun r h => by
    unfold FillRG at h; unfold StARG; omega) (fun a h => h)) (fun a h => by unfold WrA; omega)
  have hG2 := hGR (hf1'.trans hf2')
  have m2 : ∀ a, a < g.A0 → c2.nmem a = c.nmem a := fun a ha =>
    (hf1'.trans hf2').2.2.2.2 a zteqo
  have hmap2 : ztoqn := fun d => by
    have := d.2
    rw [m2 _ by_omega, m2 _ by_omega, m2 _ by_omega]; exact hmap d
  -- the first darts
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hF3⟩ := firstP_exec (P := P) hw2 hG2
    (fun d hd => by rw [hmap2.vert hd]; omega)
    (fun u hu => by
      obtain ⟨d, hd⟩ := M.vert_surj ⟨u, hu⟩
      exact ⟨d, d.2, by rw [hmap2.vert d.2, hd]⟩) hV hW
  have hf3' : PFr StARG zthsb c2 c3 := hmono hf3 ztdnt
  have hG3 := hGR ((hf1'.trans hf2').trans hf3')
  have m3 : ∀ a, a < g.A0 → c3.nmem a = c.nmem a := fun a ha =>
    ((hf1'.trans hf2').trans hf3').2.2.2.2 a zteqo
  have hmap3 : MapArrays c3.nmem g.bO g.bR g.bV g.μ g.N M := fun d => by
    have := d.2
    rw [m3 _ by_omega, m3 _ by_omega, m3 _ by_omega]; exact hmap d
  have hF3' : ∀ u, u < g.μ → c3.nmem ztrk < g.N ∧
      c3.nmem (g.bV + c3.nmem ztrk) = u := by
    grind
  have hz3 : ∀ d, d < g.N → c3.nmem ztefe = 0 := fun d hd => by
    rw [hf3.2.2.2.2 _ by_omega, hf2.2.2.2.2 _ by_omega]; grind
  have hl3 : ∀ v, v < g.μ → c3.nmem ztdol = g.μ := fun v hv => by
    zubbh
  -- the primal search
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, T, hroot, hlev, hlt, hpar, hhead⟩ :=
    bfsP_exec (P := P) hw3 hG3 hmap3 hM hμ hμN hO hR hV hF3' hz3 hl3 hW
  have hf4' : PFr StARG zthsb c3 c4 := hmono hf4 ztdnt
  have hG4 := hGR (((hf1'.trans hf2').trans hf3').trans hf4')
  have hrootv : ∀ x (_ : 1 ≤ x) (h2 : x < g.μ), (ztujq : Fin g.μ) ≠ T.root := by
    grind
  have m4 : ∀ a, a < g.A0 → c4.nmem a = c.nmem a := fun a ha =>
    (((hf1'.trans hf2').trans hf3').trans hf4').2.2.2.2 a zteqo
  -- the parent array
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, hp0, hp5⟩ := parP_exec (P := P) hw4 hG4 hμ hV
    (fun x h1 h2 => (hpar ztujq (hrootv x h1 h2)).1) hW
  have hf5' : PFr StARG zthsb c4 c5 := hmono hf5 ztdnt
  have hG5 := hGR ((((hf1'.trans hf2').trans hf3').trans hf4').trans hf5')
  have hpv5 : ∀ v : Fin g.μ, c5.nmem ztrqw = T.parent v := by
    zujbq
    zufro
    · subst hv
      rw [SpanTree.parent_root, hroot]
      omega
    · have h1 : 1 ≤ (v : ℕ) := by
        omega
      rw [hp5 v h1 v.2, (hpar v hv).2.2]
      have := (hpar v hv).1
      rw [m4 _ by_omega, m3 _ by_omega]
  -- the table
  obtain ⟨c6, k6, x6, hk6, hw6, hf6, ht6⟩ := upP_exec (P := P) hw5 hG5 hμ hL
    (fun x hx => by rw [hpv5 ztfxa]; omega) hW
  have hf6' : PFr StARG _ c5 c6 := hmono hf6 ztdnt
  have hfall := ((((hf1'.trans hf2').trans hf3').trans hf4').trans hf5').trans hf6'
  refine ⟨c6, k1 + ztrd,
    .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 x6)))), by_omega, hw6, hGR hfall, hfall, T, ?_⟩
  have m6 : ∀ a, a < g.A0 → c6.nmem a = c.nmem a := fun a ha =>
    hfall.2.2.2.2 a zteqo
  refine ⟨fun d => ?_, fun d hd => ?_, fun u hu => ?_, fun u hu => ?_, hroot, fun v => ?_, hlt,
    fun v hv => ?_, fun v hv => ?_, fun v => ?_, fun j hj x hx => ?_, hhead⟩
  · have := d.2
    rw [m6 _ by_omega, m6 (g.bR + d) by_omega, m6 ztnzw by_omega]; exact hmap d
  · zqbkj
    exact hz3 d hd
  · zqbkj
    exact (hF3' u hu).1
  · have := (hF3' u hu).1
    rw [hf6.2.2.2.2 ztrk by_omega, hf5.2.2.2.2 ztrk by_omega,
      hf4.2.2.2.2 ztrk by_omega, m6 _ by_omega, ← m3 _ by_omega]
    exact (hF3' u hu).2
  · have := v.2
    zunrl; exact hlev v
  · have := v.2
    zunrl; exact (hpar v hv).1
  · have := v.2; have := (hpar v hv).1
    rw [hf6.2.2.2.2 ztbvy by_omega, hf5.2.2.2.2 ztbvy by_omega,
      m6 _ by_omega, (hpar v hv).2.1, m3 _ by_omega]
  · have := v.2
    rw [hf6.2.2.2.2 _ by_omega]; exact hpv5 v
  · rw [ht6 j hj x hx]
    have hagree : ∀ y, y < g.μ → c5.nmem ztrqx = upTf T y := by
      zusy
      rw [hpv5 zthnw]; unfold upTf; grind
    exact (iterate_congr_lt hagree (fun y hy => upTf_lt T hy) _ x hx).1
