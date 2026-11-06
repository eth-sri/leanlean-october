module

public import Chazelle.Golf

public import Chazelle.Core.FuseAsmAux

/-!
# WP-F fusion assembly, part 28: the fusion driver

`fuseRun sw sB`: the query list of side `0`, the sweep of side `0`, the query list of side `1`,
the sweep of side `1`, the collection of the answers, the deduplication and `BuildNF`
(`fuseRun_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK MergeAsm

@[expose] public section

/-- The arguments of the deduplication. -/
def ddSet : Stmt := block [.copyN 70240 70156, .copyN 70241 70110]

/-- **The fusion driver.** -/
def fuseRun (sw sB : Stmt) : Stmt :=
  .seq sideQ₀ (.seq (swStage sw 0 70150 70128 70153) (.seq sideQ₁
    (.seq (swStage sw 1 70151 70128 70155) (.seq collectS (.seq ddSet (.seq ddRun
      (bldStage sB)))))))

theorem ddSet_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W ddSet c c' k ∧ k = 2 ∧ c'.nreg 70240 = c.nreg 70156 ∧
      c'.nreg 70241 = c.nreg 70110 ∧ (∀ r, r ≠ 70240 → r ≠ 70241 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ddSet
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other]



/-- **The fusion driver.** -/
theorem fuseRun_exec {sw sB : Stmt} {κs F : ℕ → ℕ} {κB : ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop}
    (hM : Meets sw (sweepBands ∪ oracleBands) (SwPre X Ok) SwPost (SwCost κs F))
    (hB : Meets sB {bBuild, bSort, bSign} BPre BPost (BCost κB)) (hloc : X.CapLocal)
    {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} (hF : FCtx P W J H N₁ N₂ (c.nreg ALLOC) c) (hP : FPre P X Ok J N₁ N₂ c)
    (hroom : c.nreg ALLOC + fuseκ κs κB (c.nreg 70006) * (N₁.nChords + N₂.nChords + 1) *
      (F (c.nreg 70005) + Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 1) ≤ W) :
    ∃ c' k N, Exec P W (fuseRun sw sB) c c' k ∧
      k ≤ fuseκ κs κB (c.nreg 70006) * (N₁.nChords + N₂.nChords + 1) *
        (F (c.nreg 70005) + Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 1) ∧
      Frame FB c c' k ∧ c.nreg ALLOC ≤ c'.nreg 70007 ∧
      NFWithin c'.nmem (c'.nreg 70007) (c'.nreg ALLOC) N ∧
      IsNF (chainModel J.whole) (Qof P) N ∧
      N.F (chainModel J.whole) (Qof P) =
        J.fusion (N₁.F (chainModel J.left) (Qof P)) (N₂.F (chainModel J.right) (Qof P)) ∪
          glueChords J ∧
      N.nChords ≤ 2 * (N₁.nChords + N₂.nChords) + 7 := by
  obtain ⟨A, hA⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ x, N₁.nChords = x := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ x, N₂.nChords = x := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ x, c.nreg 70006 = x := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ x, c.nreg 70005 = x := ⟨_, rfl⟩
  rw [hK₁, hK₂, hD, hγ, hA] at hroom
  rw [hK₁, hK₂, hD, hγ]
  have hG := hF.good
  have hHW := hF.hw
  have hlen₁ : N₁.chords.length = K₁ := hK₁
  have hlen₂ : N₂.chords.length = K₂ := hK₂
  -- the budget
  obtain ⟨B₂, hB₂⟩ : ∃ x, x = κs D * (K₁ + K₂ + (2 * K₁ + 5) + 1) *
      (F γ + Nat.clog 2 (K₁ + K₂ + (2 * K₁ + 5) + 1) + 1) := ⟨_, rfl⟩
  obtain ⟨B₄, hB₄⟩ : ∃ x, x = κs D * (K₁ + K₂ + (2 * K₂ + 3) + 1) *
      (F γ + Nat.clog 2 (K₁ + K₂ + (2 * K₂ + 3) + 1) + 1) := ⟨_, rfl⟩
  obtain ⟨B₆, hB₆⟩ : ∃ x, x = SortR.sortCost 40 (2 * K₁ + 2 * K₂ + 8) := ⟨_, rfl⟩
  obtain ⟨B₇, hB₇⟩ : ∃ x, x = κB * ((2 * K₁ + 2 * K₂ + 8) *
      (Nat.clog 2 (2 * K₁ + 2 * K₂ + 8) + 1) + 1) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ x, x = fuseκ κs κB D * (K₁ + K₂ + 1) *
      (F γ + Nat.clog 2 (K₁ + K₂ + 1) + 1) := ⟨_, rfl⟩
  rw [← hT] at hroom
  rw [← hT]
  have hbud := fuse_total (κs := κs) (κB := κB) (D := D) (K₁ := K₁) (K₂ := K₂)
    (L₀ := 2 * K₁ + 5) (L₁ := 2 * K₂ + 3) (Kc := 2 * K₁ + 2 * K₂ + 8)
    (Kd := 2 * K₁ + 2 * K₂ + 8) (Fg := F γ) le_rfl le_rfl (by omega) le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl
  rw [← hB₂, ← hB₄, ← hB₆, ← hB₇, ← hT] at hbud
  simp only [← Nat.add_assoc] at hbud
  -- 1. the query list of side `0`
  obtain ⟨c₁, k₁, v₁, v₀, t₁, t₀, k₀, e₁, hk₁, hk₁', lv₁, lv₀, lt₁, lt₀, lk₀, s₁, a₁, n₁, L₁,
      m₁, r₁, rr₁, rm₁, o₁, q05, q08, R₁, pv₁, pv₀, pt₁, pt₀, pk₀, nk₀⟩ :=
    sideQ₀_exec c hw hF (by rw [hK₁, hA]; unfold sq0Cost; rw [← Nat.add_assoc]; omega)
  rw [hK₁] at hk₁
  unfold sq0Cost at hk₁
  obtain ⟨L₀, hL₀⟩ : ∃ l, l = endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀) := ⟨_, rfl⟩
  rw [← hL₀] at hk₁' a₁ n₁ L₁
  have hL₀l : L₀.length ≤ 2 * K₁ + 5 := by
    rw [hL₀]; simp only [List.length_append, endQL_length, NF.nChords] at *; omega
  have w₁ := e₁.wb_right
  have F₁ : Frame FB c c₁ k₁ := frame_side (Or.inl rfl) r₁ rr₁ m₁ rm₁ o₁ a₁ hk₁'
  have hF₁ : FCtx P W J H N₁ N₂ A c₁ := by
    rw [← hA]; exact hF.keep (fun r h1 h2 => r₁ r (bside_lo (Or.inl rfl) h1 (by omega)))
      (fun a ha => m₁ a ha) (by rw [a₁]; omega)
  have hP₁ : FPre P X Ok J N₁ N₂ c₁ :=
    hP.keep hloc (fun r h1 h2 => r₁ r (bside_lo (Or.inl rfl) (by omega) (by omega))) F₁
  have e06₁ : c₁.nreg 70006 = D := by rw [r₁ _ (by decide), hD]
  have e05₁ : c₁.nreg 70005 = γ := by rw [r₁ _ (by decide), hγ]
  have ok₀ := side₀_ok J (Qof P) hF.is₁ pv₁ pv₀ pt₁ pt₀ pk₀ nk₀
  rw [← hL₀] at ok₀
  -- 2. the sweep of side `0`
  have mono₂ := sweepc_mono (κs D) (K₁ + K₂) (F γ) hL₀l
  rw [← hB₂] at mono₂
  obtain ⟨c₂, k₂, R₀, e₂, hk₂, hR₀l, hRB₀, hRB₀', hR₀, sees₀, F₂, g₂, n₂⟩ :=
    swStage_exec hM c₁ w₁ hF₁ hP₁ (i := 0) (S := 70150) (Lr := 70128) (RB := 70153)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (L := L₀) n₁
      (by rw [s₁]; exact L₁) (by rw [s₁, a₁]) (fun q hq => (ok₀ q hq).1) (by norm_num)
      (fun q hq => (ok₀ q hq).2)
      (by rw [e06₁, e05₁, hK₁, hK₂, a₁, hA]; omega)
  rw [e06₁, e05₁, hK₁, hK₂] at hk₂
  have w₂ := e₂.wb_right
  have g₂' : ∀ r, 70000 ≤ r → r < 70152 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    g₂ r (by unfold bandOf bFuse; omega) (by omega) (by omega)
  have hF₂ : FCtx P W J H N₁ N₂ A c₂ := hF₁.keep (fun r h1 h2 => g₂' r h1 (by omega))
    (fun a ha => F₂.2.2.1 a (by have := hF₁.le; omega)) F₂.2.2.2.2.2.1
  have hP₂ : FPre P X Ok J N₁ N₂ c₂ :=
    hP₁.keep hloc (fun r h1 h2 => g₂' r (by omega) (by omega)) F₂
  have R₂ : CapRegs P J c₂ := R₁.keep fun r h => g₂' r (by omega) (by omega)
  -- 3. the query list of side `1`
  obtain ⟨c₃, k₃, t'₁, t'₀, k₁', e₃, hk₃, hk₃', lt'₁, lt'₀, lk₁, s₃, a₃, n₃, L₃, m₃, r₃, rr₃, rm₃,
      o₃, q305, q308, pt'₁, pt'₀, pk₁, nk₁⟩ :=
    sideQ₁_exec c₂ w₂ hF₂ R₂ (by
      rw [hK₂]; unfold sq1Cost; rw [← Nat.add_assoc]
      have := F₂.2.2.2.2.2.2; rw [a₁, hA] at this
      omega)
  rw [hK₂] at hk₃
  unfold sq1Cost at hk₃
  obtain ⟨L₁', hL₁'⟩ : ∃ l, l = endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁') := ⟨_, rfl⟩
  rw [← hL₁'] at hk₃' a₃ n₃ L₃
  have hL₁l : L₁'.length ≤ 2 * K₂ + 3 := by
    rw [hL₁']; simp only [List.length_append, endQL_length, NF.nChords] at *; omega
  have w₃ := e₃.wb_right
  have F₃ : Frame FB c₂ c₃ k₃ := frame_side (Or.inr rfl) r₃ rr₃ m₃ rm₃ o₃ a₃ hk₃'
  have hF₃ : FCtx P W J H N₁ N₂ A c₃ := hF₂.keep
    (fun r h1 h2 => r₃ r (bside_lo (Or.inr rfl) h1 (by omega)))
    (fun a ha => m₃ a (by have := hF₂.le; omega)) (by rw [a₃]; omega)
  have hP₃ : FPre P X Ok J N₁ N₂ c₃ :=
    hP₂.keep hloc (fun r h1 h2 => r₃ r (bside_lo (Or.inr rfl) (by omega) (by omega))) F₃
  have ok₁ := side₁_ok J (Qof P) hF.is₂ pt'₁ pt'₀ pk₁ nk₁
  rw [← hL₁'] at ok₁
  have e06₃ : c₃.nreg 70006 = D := by
    rw [r₃ _ (by decide), g₂' _ (by norm_num) (by norm_num), e06₁]
  have e05₃ : c₃.nreg 70005 = γ := by
    rw [r₃ _ (by decide), g₂' _ (by norm_num) (by norm_num), e05₁]
  -- 4. the sweep of side `1`
  have mono₄ := sweepc_mono (κs D) (K₁ + K₂) (F γ) hL₁l
  rw [← hB₄] at mono₄
  have al₂ := F₂.2.2.2.2.2.2
  have al₂' := F₂.2.2.2.2.2.1
  obtain ⟨c₄, k₄, R₁', e₄, hk₄, hR₁l, hRB₁, hRB₁', hR₁, sees₁, F₄, g₄, n₄⟩ :=
    swStage_exec hM c₃ w₃ hF₃ hP₃ (i := 1) (S := 70151) (Lr := 70128) (RB := 70155)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (L := L₁') n₃
      (by rw [s₃]; exact L₃) (by rw [s₃, a₃]) (fun q hq => (ok₁ q hq).1)
      (fun _ => ⟨_, by rw [hL₁', endQL_eq], by simp only [List.length_append]; omega⟩)
      (fun q hq => (ok₁ q hq).2)
      (by rw [e06₃, e05₃, hK₁, hK₂, a₃]; rw [a₁, hA] at al₂; omega)
  rw [e06₃, e05₃, hK₁, hK₂] at hk₄
  have w₄ := e₄.wb_right
  have g₄' : ∀ r, 70000 ≤ r → r < 70154 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    g₄ r (by unfold bandOf bFuse; omega) (by omega) (by omega)
  have al₄ := F₄.2.2.2.2.2.2
  have al₄' := F₄.2.2.2.2.2.1
  -- the lists at `c₄`
  have mem14 : ∀ a, a < c₁.nreg ALLOC → c₄.nmem a = c₁.nmem a := fun a ha => by
    rw [F₄.2.2.1 a (by rw [a₃]; omega), m₃ a (by omega), F₂.2.2.1 a ha]
  have mem24 : ∀ a, a < c₂.nreg ALLOC → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [F₄.2.2.1 a (by rw [a₃]; omega), m₃ a ha]
  have x50 : c₄.nreg 70150 = A := by
    rw [g₄' _ (by norm_num) (by norm_num), r₃ _ (by decide), g₂' _ (by norm_num) (by norm_num),
      s₁, hA]
  have x52 : c₄.nreg 70152 = L₀.length := by
    rw [g₄' _ (by norm_num) (by norm_num), r₃ _ (by decide)]; exact n₂
  have x53 : c₄.nreg 70153 = c₂.nreg 70153 := by
    rw [g₄' _ (by norm_num) (by norm_num), r₃ _ (by decide)]
  have x51 : c₄.nreg 70151 = c₂.nreg ALLOC := by rw [g₄' _ (by norm_num) (by norm_num), s₃]
  have x05 : c₄.nreg 70105 = 1 := by rw [g₄' _ (by norm_num) (by norm_num), q305]
  have x08 : c₄.nreg 70108 = 0 := by rw [g₄' _ (by norm_num) (by norm_num), q308]
  -- 5. the collection
  obtain ⟨c₅, k₅, e₅, hk₅, s₅, n₅, a₅, L₅, F₅, r₅⟩ := collectS_exec (P := P) c₄ w₄ x05 x08
    (L₀ := L₀) (L₁ := L₁') (R₀ := R₀) (R₁ := R₁')
    (by rw [x50, ← hA]; exact chordList_agree (E := c₁.nreg ALLOC) L₁ a₁.symm.le mem14)
    x52 (by rw [x53]; exact resultList_agree hR₀ (by omega) mem24) hR₀l
    (by rw [x50]; rw [a₁, hA] at al₂'; omega) (by rw [x53]; omega)
    (by rw [x51]; exact (chordList_agree (E := c₃.nreg ALLOC) L₃ a₃.symm.le
          fun a ha => F₄.2.2.1 a ha))
    n₄ hR₁ hR₁l (by rw [x51]; omega) (by omega)
    (by rw [a₁, hA] at al₂; rw [a₃] at al₄; omega)
  have w₅ := e₅.wb_right
  obtain ⟨C, hC⟩ : ∃ l, l = collectQ L₀ R₀ ++ collectQ L₁' R₁' := ⟨_, rfl⟩
  rw [← hC] at n₅ a₅ L₅
  have hCl : C.length ≤ L₀.length + L₁'.length := by
    rw [hC, List.length_append]
    have := collectQ_length_le L₀ R₀; have := collectQ_length_le L₁' R₁'; omega
  have al₅ := F₅.2.2.2.2.2.2
  -- 6. the arguments of the deduplication
  obtain ⟨c₆, k₆, e₆, hk₆, t40, t41, tr₆, tm₆, trr₆, trm₆, to₆⟩ := ddSet_exec (P := P) c₅ w₅
  have w₆ := e₆.wb_right
  have a₆ : c₆.nreg ALLOC = c₅.nreg ALLOC := tr₆ _ (by decide) (by decide)
  have F₆ : Frame FB c₅ c₆ k₆ := ⟨fun r hr ha => tr₆ r (fun h => hr (by rw [h]; exact band7))
      (fun h => hr (by rw [h]; exact band7)), fun r _ => by rw [trr₆], fun a _ => by rw [tm₆],
    fun a _ => by rw [trm₆], to₆, by rw [a₆], by rw [a₆]; omega⟩
  -- 7. the deduplication
  have hdd := sortc_mono 40 (show C.length ≤ 2 * K₁ + 2 * K₂ + 8 by omega)
  rw [← hB₆] at hdd
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, keep₇, h42a, h42b, Dl, hDL, hDc, hDlen, hDmem, hDnd⟩ :=
    ddRun_exec (P := P) c₆ w₆ (T := c₄.nreg ALLOC) (K := C.length) (by rw [t40, s₅])
      (by rw [t41, n₅]) (by rw [a₆, a₅])
      (by
        unfold ddCost
        simp only [← Nat.add_assoc]
        rw [a₆, a₅]; rw [a₁, hA] at al₂; rw [a₃] at al₄
        omega)
  unfold ddCost at hk₇
  have w₇ := e₇.wb_right
  have htl : tlist c₆.nmem (c₄.nreg ALLOC) C.length = C := by rw [tm₆]; exact tlist_eq L₅
  rw [htl] at hDmem
  have al₇ := F₇.2.2.2.2.2.2
  -- the context at `c₇`
  have hF₄ : FCtx P W J H N₁ N₂ A c₄ := hF₃.keep (fun r h1 h2 => g₄' r h1 (by omega))
    (fun a ha => F₄.2.2.1 a (by have := hF₃.le; omega)) al₄'
  have hF₇ : FCtx P W J H N₁ N₂ A c₇ := hF₄.keep
    (fun r h1 h2 => by
      rw [keep₇ r h1 (by omega), tr₆ r (by omega) (by omega), r₅ r (Or.inl (by omega))
        (by omega) (by unfold ALLOC; omega)])
    (fun a ha => by
      have := hF₄.le
      rw [F₇.2.2.1 a (by rw [a₆, a₅]; omega), tm₆, F₅.2.2.1 a (by omega)])
    (by have := F₇.2.2.2.2.2.1; rw [a₆, a₅] at this; omega)
  obtain ⟨-, -, -, -, sdw, sww⟩ := hF₇.side
  -- the chord list
  have hAns : Answers J (Qof P) L₀ L₁' R₀ R₁' := ⟨hR₀l, hR₁l, sees₀, sees₁, ok₀, ok₁⟩
  obtain ⟨hcap, hk01⟩ := capAns_of J (Qof P) pk₀ nk₀ pk₁ nk₁ lk₀ lk₁
  have hCov := (cover_of J (Qof P) hF.is₁ hF.is₂
    (⟨pv₁, pv₀, pt₁, pt₀, pt'₁, pt'₀, hcap⟩ : PtLists J (Qof P) v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁')).1
  rw [← hL₀, ← hL₁'] at hCov
  obtain ⟨hok, hset, hDL'⟩ := fuseList_ok J (Qof P) hF.simple
    (OracleR.distinctHeights_of_goodEnv hG) hF.gen hF.is₁.1 hF.is₂.1 hAns hCov
    (fun x => by rw [hDmem, hC]) hDnd
  -- 8. the normal form
  have hbl := nlogc_mono κB (show Dl.length ≤ 2 * K₁ + 2 * K₂ + 8 by omega)
  rw [← hB₇] at hbl
  obtain ⟨c₈, k₈, N, e₈, hk₈, h07, hNW, hIs, hNmap, F₈, -⟩ := bldStage_exec hB c₇ w₇ hG hHW
    sww sdw hF.simple hDL hDc (by rw [hDc] at h42b; exact h42b) hok
    (by rw [a₆, a₅] at al₇; rw [a₁, hA] at al₂; rw [a₃] at al₄; omega)
  have ex : Exec P W (fuseRun sw sB) c c₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  have Ft : Frame FB c c₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    ftrF F₁ (ftrF F₂ (ftrF F₃ (ftrF F₄ (ftrF F₅ (ftrF F₆ (ftrF (F₇.mono (by decide) le_rfl)
      F₈))))))
  have hcost := fuse_total (κs := κs) (κB := κB) (D := D) (K₁ := K₁) (K₂ := K₂)
    (L₀ := L₀.length) (L₁ := L₁'.length) (Kc := C.length) (Kd := Dl.length) (Fg := F γ)
    (k₆ := k₆ + k₇) (k₇ := k₈) hL₀l hL₁l hCl hDlen hk₁ hk₂ hk₃ hk₄ hk₅
    (by simp only [← Nat.add_assoc]; omega) hk₈
  rw [← hT] at hcost
  have eL₀ : L₀.length = 2 * K₁ + v₁.length + v₀.length + t₁.length + t₀.length + k₀.length := by
    rw [hL₀]; simp only [List.length_append, endQL_length, hlen₁]; ring
  have eL₁ : L₁'.length = 2 * K₂ + t'₁.length + t'₀.length + k₁'.length := by
    rw [hL₁']; simp only [List.length_append, endQL_length, hlen₂]; ring
  have hNl : N.chords.length = Dl.length := by rw [← hNmap, List.length_map]
  refine ⟨c₈, _, N, ex, by omega, Ft, ?_, hNW, hIs, ?_, ?_⟩
  · have := F₇.2.2.2.2.2.1
    rw [a₆, a₅] at this; rw [a₃] at al₄'; rw [a₁] at al₂'
    omega
  · rw [← hset]
    ext x
    simp only [NF.F, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r.h, r.lp, r.rp), by rw [← hNmap]; exact List.mem_map_of_mem hr, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← hNmap] at hy
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
      exact ⟨r, hr, rfl⟩
  · unfold NF.nChords
    omega


end

end FuseAsm

end Chazelle.Core
