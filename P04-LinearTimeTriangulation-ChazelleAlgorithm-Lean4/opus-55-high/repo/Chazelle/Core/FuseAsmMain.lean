module

public import Chazelle.MacT
public import Chazelle.Core.FuseAsmCollQ
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.BruteCorner
public import Chazelle.Core.RestoreTHoleChain
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.DownPhaseDrvXRamH

namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK MergeAsm
@[expose] public section
def ddSet : Stmt := block [.copyN 70240 70156, .copyN 70241 70110]

/-- **The fusion driver.** -/
def fuseRun (sw sB : Stmt) : Stmt :=
  .seq sideQ₀ (.seq (swStage sw 0 70150 70128 70153) (.seq sideQ₁
    (.seq (swStage sw 1 70151 70128 70155) (.seq collectS (.seq ddSet (.seq ddRun
      ztqdy))))))
theorem ddSet_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W ddSet c c' k ∧ k = 2 ∧ c'.nreg 70240 = c.nreg 70156 ∧
      c'.nreg 70241 = c.nreg 70110 ∧ (∀ r, r ≠ 70240 → r ≠ 70241 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ddSet
  exec_block
  simp_all
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The fusion driver.** -/
theorem fuseRun_exec {sw sB : Stmt} {κs F : ℕ → ℕ} {κB : ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop}
    (hM : Meets sw ztdwg ztnpn SwPost zttde)
    (hB : Meets sB {bBuild, bSort, bSign} BPre BPost ztuwn) (hloc : X.CapLocal)
    {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} (hF : FCtx P W J H N₁ N₂ ztm c) (hP : FPre P X Ok J N₁ N₂ c)
    (hroom : c.nreg ALLOC + fuseκ κs κB ztghh * ztks *
      ztyhn ≤ W) :
    ∃ c' k N, Exec P W zttki c c' k ∧
      k ≤ fuseκ κs κB ztghh * ztks *
        ztyhn ∧
      Frame FB c c' k ∧ c.nreg ALLOC ≤ c'.nreg 70007 ∧
      NFWithin c'.nmem ztvgp ztdo N ∧
      IsNF ztbm zta N ∧
      N.F ztbm zta =
        J.fusion ztwjx ztwis ∪
          glueChords J ∧
      N.nChords ≤ 2 * zttbf + 7 := by
  obtain ⟨A, hA⟩ : ztcgh := by_simp_all
  obtain ⟨K₁, hK₁⟩ : ∃ x, N₁.nChords = x := by_simp_all
  obtain ⟨K₂, hK₂⟩ : ∃ x, N₂.nChords = x := by_simp_all
  obtain ⟨D, hD⟩ : ∃ x, c.nreg 70006 = x := by_simp_all
  obtain ⟨γ, hγ⟩ : ∃ x, c.nreg 70005 = x := by_simp_all
  rw [hK₁, hK₂, hD, hγ, hA] at hroom
  rw [hK₁, hK₂, hD, hγ]
  zudyh

  have hlen₁ : N₁.chords.length = K₁ := hK₁
  have hlen₂ : N₂.chords.length = K₂ := hK₂
  -- the budget
  obtain ⟨B₂, hB₂⟩ : ∃ x, x = κs D * (K₁ + K₂ + (2 * K₁ + 5) + 1) *
      (F γ + Nat.clog 2 (K₁ + K₂ + (2 * K₁ + 5) + 1) + 1) := by_simp_all
  obtain ⟨B₄, hB₄⟩ : ∃ x, x = κs D * (K₁ + K₂ + (2 * K₂ + 3) + 1) *
      (F γ + Nat.clog 2 (K₁ + K₂ + (2 * K₂ + 3) + 1) + 1) := by_simp_all
  obtain ⟨B₆, hB₆⟩ : ∃ x, x = SortR.sortCost 40 (2 * K₁ + 2 * K₂ + 8) := by_simp_all
  obtain ⟨B₇, hB₇⟩ : ∃ x, x = κB * ((2 * K₁ + 2 * K₂ + 8) *
      (Nat.clog 2 (2 * K₁ + 2 * K₂ + 8) + 1) + 1) := by_simp_all
  obtain ⟨T, hT⟩ : ∃ x, x = fuseκ κs κB D * (K₁ + K₂ + 1) *
      (F γ + Nat.clog 2 ztctf + 1) := by_simp_all
  rw [← hT] at hroom
  zuhnu
  have hbud := fuse_total (κs := κs) (κB := κB) (D := D)
    (L₀ := 2 * K₁ + 5) (L₁ := 2 * K₂ + 3)
    (Kd := 2 * K₁ + 2 * K₂ + 8) (Fg := F γ) le_rfl le_rfl by_omega le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl
  rw [← hB₂, ← hB₄, ← hB₆, ← hB₇, ← hT] at hbud
  simp only [← Nat.add_assoc] at hbud
  -- 1. the query list of side `0`
  obtain ⟨c₁, k₁, v₁, v₀, t₁, t₀, k₀, e₁, hk₁, hk₁', lv₁, lv₀, lt₁, lt₀, lk₀, s₁, a₁, n₁, L₁,
      m₁, r₁, rr₁, rm₁, o₁, q05, q08, R₁, pv₁, pv₀, pt₁, pt₀, pk₀, nk₀⟩ :=
    sideQ₀_exec c hw hF (by rw [hK₁, hA]; unfold sq0Cost; omega)
  rw [hK₁] at hk₁
  unfold sq0Cost at hk₁
  obtain ⟨L₀, hL₀⟩ : ∃ l, l = endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀) := by_simp_all
  rw [← hL₀] at hk₁' a₁ n₁ L₁
  have hL₀l : L₀.length ≤ 2 * K₁ + 5 := by
    zuoxv; simp only [List.length_append, endQL_length, NF.nChords] at *; omega
  zud
  have F₁ := frame_side ztp r₁ rr₁ m₁ rm₁ o₁ a₁ hk₁'
  have hF₁ : FCtx P W J H N₁ N₂ A c₁ := by
    rw [← hA]; exact hF.keep (fun r h1 h2 => r₁ r (bside_lo ztp h1 by_omega))
      by_omega by_omega
  have hP₁ :=
    hP.keep hloc (fun r h1 h2 => r₁ r (bside_lo ztp by_omega by_omega)) F₁
  have e06₁ : c₁.nreg 70006 = D := by rw [r₁ _ by_decide, hD]
  have e05₁ : c₁.nreg 70005 = γ := by rw [r₁ _ by_decide, hγ]
  have ok₀ := side₀_ok J _ hF.is₁ pv₁ pv₀ pt₁ pt₀ pk₀ nk₀
  rw [← hL₀] at ok₀
  -- 2. the sweep of side `0`
  have mono₂ := sweepc_mono ztmpp ztsyv ztuye hL₀l
  rw [← hB₂] at mono₂
  obtain ⟨c₂, k₂, R₀, e₂, hk₂, hR₀l, hRB₀, hRB₀', hR₀, sees₀, F₂, g₂, n₂⟩ :=
    swStage_exec hM c₁ w₁ hF₁ hP₁ (i := 0) (S := 70150) (Lr := 70128) (RB := 70153)
      by_norm_num by_norm_num by_norm_num by_norm_num by_decide (L := L₀) n₁
      by_grind by_omega (fun q hq => (ok₀ q hq).1) by_norm_num
      (fun q hq => (ok₀ q hq).2)
      by_grind
  rw [e06₁, e05₁, hK₁, hK₂] at hk₂
  zue
  have g₂' : ∀ r, 70000 ≤ r → r < 70152 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    g₂ r ztiiv by_omega by_omega
  have hF₂ := hF₁.keep by_grind
    (fun a ha => F₂.2.2.1 a by_omega) F₂.2.2.2.2.2.1
  have hP₂ :=
    hP₁.keep hloc by_grind F₂
  have R₂ := R₁.keep fun r h => g₂' r by_omega by_omega
  -- 3. the query list of side `1`
  obtain ⟨c₃, k₃, t'₁, t'₀, k₁', e₃, hk₃, hk₃', lt'₁, lt'₀, lk₁, s₃, a₃, n₃, L₃, m₃, r₃, rr₃, rm₃,
      o₃, q305, q308, pt'₁, pt'₀, pk₁, nk₁⟩ :=
    sideQ₁_exec c₂ w₂ hF₂ R₂ (by
      rw [hK₂]; unfold sq1Cost; zunew
      have := F₂.2.2.2.2.2.2; omega)
  rw [hK₂] at hk₃
  unfold sq1Cost at hk₃
  obtain ⟨L₁', hL₁'⟩ : ∃ l, l = endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁') := by_grind
  rw [← hL₁'] at hk₃' a₃ n₃ L₃
  have hL₁l : L₁'.length ≤ 2 * K₂ + 3 := by
    zuoxw; simp only [List.length_append, endQL_length, NF.nChords] at *; omega
  zubj
  have F₃ := frame_side ztbt r₃ rr₃ m₃ rm₃ o₃ a₃ hk₃'
  have hF₃ := hF₂.keep
    (fun r h1 h2 => r₃ r (bside_lo ztbt h1 by_omega))
    (fun a ha => m₃ a by_omega) by_omega
  have hP₃ :=
    hP₂.keep hloc (fun r h1 h2 => r₃ r (bside_lo ztbt by_omega by_omega)) F₃
  have ok₁ := side₁_ok J _ hF.is₂ pt'₁ pt'₀ pk₁ nk₁
  rw [← hL₁'] at ok₁
  have e06₃ : c₃.nreg 70006 = D := by
    rw [r₃ _ by_decide, g₂' _ by_norm_num by_norm_num, e06₁]
  have e05₃ : c₃.nreg 70005 = γ := by
    rw [r₃ _ by_decide, g₂' _ by_norm_num by_norm_num, e05₁]
  -- 4. the sweep of side `1`
  have mono₄ := sweepc_mono ztmpp ztsyv ztuye hL₁l
  rw [← hB₄] at mono₄
  have al₂ := F₂.2.2.2.2.2.2
  have al₂' := F₂.2.2.2.2.2.1
  obtain ⟨c₄, k₄, R₁', e₄, hk₄, hR₁l, hRB₁, hRB₁', hR₁, sees₁, F₄, g₄, n₄⟩ :=
    swStage_exec hM c₃ w₃ hF₃ hP₃ (i := 1) (S := 70151) (Lr := 70128) (RB := 70155)
      by_norm_num by_norm_num by_norm_num by_norm_num by_decide (L := L₁') n₃
      by_grind by_omega (fun q hq => (ok₁ q hq).1)
      (fun _ => ⟨_, by rw [hL₁', endQL_eq], by simp only [List.length_append]; omega⟩)
      (fun q hq => (ok₁ q hq).2)
      by_grind
  rw [e06₃, e05₃, hK₁, hK₂] at hk₄
  zucc
  have g₄' : ∀ r, 70000 ≤ r → r < 70154 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    g₄ r ztiiv by_omega by_omega
  have al₄ := F₄.2.2.2.2.2.2
  have al₄' := F₄.2.2.2.2.2.1
  -- the lists at `c₄`
  have mem14 : ∀ a, a < c₁.nreg ALLOC → c₄.nmem a = c₁.nmem a := fun a ha => by
    rw [F₄.2.2.1 a by_omega, m₃ a by_omega, F₂.2.2.1 a ha]
  have mem24 : ∀ a, a < c₂.nreg ALLOC → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [F₄.2.2.1 a by_omega, m₃ a ha]
  have x50 : c₄.nreg 70150 = A := by
    rw [g₄' _ by_norm_num by_norm_num, r₃ _ by_decide, g₂' _ by_norm_num by_norm_num,
      s₁, hA]
  have x52 : c₄.nreg 70152 = L₀.length := by
    zunox; exact n₂
  have x53 : c₄.nreg 70153 = c₂.nreg 70153 := by
    zunox
  have x51 : c₄.nreg 70151 = c₂.nreg ALLOC := by rw [g₄' _ by_norm_num by_norm_num, s₃]
  have x05 : c₄.nreg 70105 = 1 := by rw [g₄' _ by_norm_num by_norm_num, q305]
  have x08 : c₄.nreg 70108 = 0 := by rw [g₄' _ by_norm_num by_norm_num, q308]
  -- 5. the collection
  obtain ⟨c₅, k₅, e₅, hk₅, s₅, n₅, a₅, L₅, F₅, r₅⟩ := collectS_exec (P := P) c₄ w₄ x05 x08
    (L₀ := L₀) (L₁ := L₁') (R₀ := R₀) (R₁ := R₁')
    (by rw [x50, ← hA]; exact chordList_agree L₁ a₁.symm.le mem14)
    x52 (by rw [x53]; exact resultList_agree hR₀ by_omega mem24) hR₀l
    by_omega by_omega
    (by rw [x51]; exact (chordList_agree L₃ a₃.symm.le
          F₄.2.2.1))
    n₄ hR₁ hR₁l by_omega by_omega
    by_grind
  zuef
  obtain ⟨C, hC⟩ : ∃ l, l = collectQ L₀ R₀ ++ collectQ L₁' R₁' := zths
  rw [← hC] at n₅ a₅ L₅
  have hCl : C.length ≤ L₀.length + L₁'.length := by
    rw [hC, List.length_append]
    have := collectQ_length_le L₀ R₀; have := collectQ_length_le L₁' R₁'; omega
  have al₅ := F₅.2.2.2.2.2.2
  -- 6. the arguments of the deduplication
  obtain ⟨c₆, k₆, e₆, hk₆, t40, t41, tr₆, tm₆, trr₆, trm₆, to₆⟩ := ddSet_exec (P := P) c₅ w₅
  zujb
  have a₆ : ztfkx := tr₆ _ by_decide by_decide
  have F₆ : Frame FB c₅ c₆ k₆ := ⟨fun r hr ha => tr₆ r ztwmm
      ztwmm, fun r _ => by rw [trr₆], fun a _ => by zuoxx,
    fun a _ => by rw [trm₆], to₆, by rw [a₆], by_omega⟩
  -- 7. the deduplication
  have hdd := sortc_mono 40 (show C.length ≤ 2 * K₁ + 2 * K₂ + 8 by omega)
  rw [← hB₆] at hdd
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, keep₇, h42a, h42b, Dl, hDL, hDc, hDlen, hDmem, hDnd⟩ :=
    ddRun_exec (P := P) c₆ w₆ (T := c₄.nreg ALLOC) (K := C.length) by_omega
      by_omega by_omega
      (by
        unfold ddCost
        simp only [← Nat.add_assoc]
        rw [a₆, a₅]; rw [a₁, hA] at al₂; rw [a₃] at al₄
        omega)
  unfold ddCost at hk₇
  zubgp
  have htl : tlist c₆.nmem (c₄.nreg ALLOC) C.length = C := by zuoxx; exact tlist_eq L₅
  rw [htl] at hDmem
  have al₇ := F₇.2.2.2.2.2.2
  -- the context at `c₇`
  have hF₄ := hF₃.keep (fun r h1 h2 => g₄' r h1 by_omega)
    (fun a ha => F₄.2.2.1 a by_omega) al₄'
  have hF₇ := hF₄.keep
    (fun r h1 h2 => by
      rw [keep₇ r h1 by_omega, tr₆ r by_omega by_omega, r₅ r by_omega
        by_omega ztu])
    (fun a ha => by
      have := hF₄.le
      rw [F₇.2.2.1 a by_omega, tm₆, F₅.2.2.1 a by_omega])
    by_omega
  obtain ⟨-, -, -, -, sdw, sww⟩ := hF₇.side
  -- the chord list
  have hAns : Answers J _ L₀ L₁' R₀ R₁' := ⟨hR₀l, hR₁l, sees₀, sees₁, ok₀, ok₁⟩
  obtain ⟨hcap, hk01⟩ := capAns_of J _ pk₀ nk₀ pk₁ nk₁ lk₀ lk₁
  have hCov := (cover_of J _ hF.is₁ hF.is₂
    (⟨pv₁, pv₀, pt₁, pt₀, pt'₁, pt'₀, hcap⟩ : PtLists J _ v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁')).1
  rw [← hL₀, ← hL₁'] at hCov
  obtain ⟨hok, hset, hDL'⟩ := fuseList_ok J zta hF.simple
    (OracleR.distinctHeights_of_goodEnv hG) hF.gen hF.is₁.1 hF.is₂.1 hAns hCov
    (fun x => by rw [hDmem, hC]) hDnd
  -- 8. the normal form
  have hbl := nlogc_mono κB (show Dl.length ≤ 2 * K₁ + 2 * K₂ + 8 by omega)
  rw [← hB₇] at hbl
  obtain ⟨c₈, k₈, N, e₈, hk₈, h07, hNW, hIs, hNmap, F₈, -⟩ := bldStage_exec hB c₇ w₇ hG hHW
    sww sdw hF.simple hDL hDc by_omega hok
    (by rw [a₆, a₅] at al₇; rw [a₁, hA] at al₂; rw [a₃] at al₄; omega)
  have ex : Exec P W zttki c c₈ _ :=
    .seq e₁ ztey
  have Ft : Frame FB c c₈ _ :=
    ftrF F₁ (ftrF F₂ (ftrF F₃ (ftrF F₄ (ftrF F₅ (ftrF F₆ (ftrF (F₇.mono by_decide le_rfl)
      F₈))))))
  have hcost := fuse_total
    (k₆ := k₆ + k₇) hL₀l hL₁l hCl hDlen hk₁ hk₂ hk₃ hk₄ hk₅
    by_omega hk₈
  rw [← hT] at hcost
  have eL₀ : L₀.length = 2 * K₁ + v₁.length + v₀.length + t₁.length + t₀.length + k₀.length := by
    zuoxv; simp only [List.length_append, endQL_length, hlen₁]; ring
  have eL₁ : L₁'.length = 2 * K₂ + t'₁.length + t'₀.length + k₁'.length := by
    zuoxw; simp only [List.length_append, endQL_length, hlen₂]; ring
  have hNl : N.chords.length = Dl.length := by rw [← hNmap, List.length_map]
  refine ⟨c₈, _, N, ex, by_omega, Ft, ?_, hNW, hIs, ?_, ?_⟩
  · have := F₇.2.2.2.2.2.1
    rw [a₆, a₅] at this; rw [a₃] at al₄'; rw [a₁] at al₂'
    omega
  · rw [← hset]
    zumx
    simp only [NF.F, Set.mem_ofPred_eq]
    constructor
    · zuoc
      exact ⟨ztlm, by rw [← hNmap]; exact List.mem_map_of_mem hr, rfl⟩
    · zuifw
      rw [← hNmap] at hy
      zufza
      exact ztkmp
  · unfold NF.nChords
    omega
theorem nf_F_congr {M : Model} {Q : Polygon} {N N' : NF} (h : N.chords = N'.chords) :
    N.F M Q = N'.F M Q := by
  zujqb
theorem nChords_congr {N N' : NF} (h : N.chords = N'.chords) : N.nChords = N'.nChords := by
  unfold NF.nChords; zvmwc

/-- **WP-F: the fusion.** -/
theorem fuseSpec_of (hS : SweepSpecH) (hBd : BuildNFSpec) : FuseSpec := by
  obtain ⟨mk, κs, hSw⟩ := sweep_meets hS
  obtain ⟨sB, κB, hBM⟩ := build_meets hBd
  obtain ⟨capF, hcapF⟩ := FuseDeg.fusionDegSpec
  refine ⟨fun sh => fuseRun ztkbc sB, fuseκ κs κB, capF, ?_⟩
  intro sh Bs F X Ok hloc hBs hsh P W c hw hpre hroom
  obtain ⟨hG, hHW, hX, hcap, hJWF, H, J, N₁, N₂, hJ, hPs, hgen, hOk1, hOk2, hOkw, hN1, hN2,
    hi1, hi2, hd1, hd2, hs1, hs2⟩ := hpre
  have hF : FCtx P W J H N₁ N₂ ztm c :=
    ⟨hG, hHW, hJ, hJWF, hPs, hgen, hN1, hN2, hi1, hi2, le_rfl⟩
  have hP : FPre P X Ok J N₁ N₂ c := ⟨hOk1, hOk2, hOkw, hd1, hd2, hs1, hs2, hX, hcap⟩
  have hK1 : c.nmem ztfue = N₁.nChords := hN1.nfAt.1
  have hK2 : c.nmem ztfuf = N₂.nChords := hN2.nfAt.1
  zufqq
  zuiit
  obtain ⟨c', k, N, ex, hk, Fr, hle, hNW, hIs, hNF, hNk⟩ :=
    fuseRun_exec (hSw sh Bs F X Ok hloc hBs hsh) hBM hloc c hw hF hP hroom
  refine ⟨c', k, ex, by beta_reduce; rw [hK1, hK2]; exact hk, ?_, Fr⟩
  intro H' J' N₁' N₂' hJ' hA1 hA2
  have eJ : J = J' := junction_eq hJ hJ'
  subst eJ
  have e1 := chords_eq_of_nfAt hN1.nfAt hA1
  have e2 := chords_eq_of_nfAt hN2.nfAt hA2
  rw [← nf_F_congr e1, ← nf_F_congr e2, ← nChords_congr e1, ← nChords_congr e2]
  refine ⟨N, hle, hNW, hIs, hNF, hNk, ?_, ?_⟩
  · zummq
    exact hcapF J zta _ _ _ hPs hgen hi1.1 hi2.1 hd1 hd2
  · zummq
    exact FuseMath.fusionWeightSpec J zta _ _ _ hPs hgen hi1.1 hi2.1 hs1 hs2
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- **The first position of the left stretch is the shared vertex.** -/
theorem start_pt (hP : J.P.Simple) :
    sidePt (chainModel J.whole).W
      ((6 + tpos J.whole ztbv + 0) % (chainModel J.whole).W.n) 0 = J.shared := by
  zubwd
  have hd : 0 < lL1 J + lL2 J := by
    zuogn; unfold llen; have := J.one_le_m₁; grind
  rw [hC.sidePt_eq hd 0, Chazelle.Chain.sidePt_zero]
  zujql
  rw [ite_eq_left (by
    unfold lL1; have := J.one_le_m₁; have := tpos_lt J.left J.m₁
    grind), add_zero]
  have := walk_tour J.left J.m₁ 0 (by have := tpos_lt J.left J.m₁; omega)
  zukqd
  zubk
  exact tourV_left_zero J
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- **The rule for a chord inside a chord of `S₂`** (fused chords and wall pieces): let `f ∈ F₂⁺`,
`f ⊆ c ∈ S₂`, be attached at a position `(pB, tB)` of the open right stretch which is not the
split vertex (for instance at a point of `C₂` other than the top of `C₂`, or inside a walk edge);
then its side labels are the regions of `S₂` on the same side of `c`. -/
theorem sideLabel_sub (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {c f : Set Point} (hc : c ∈ S₂)
    (hf : f ∈ F₂plus J S₂) (hfc : f ⊆ c) {pB : ℕ} {tB : ℝ}
    (hB : SideAttach (chainModel J.whole).W f pB tB)
    (h0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv)
    (hL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hns : tB = 0 → sidePt (chainModel J.whole).W pB tB ≠ J.right.top)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {V : Set Point}
    (hV : V ∈ (chainModel J.right).regions S₂) (hVs : SideOf ztj ρ c V) :
    SideLabel J S₂ f ρ V := by
  zuftz
  obtain ⟨d, hd, hd0, hpd⟩ := stretch_decomp J hP hS₂a hS₂.1 hB.1 hB.2.1 hB.2.2.1 h0 hL
  have hns' := hns
  rw [hpd] at hB hns'
  have hsec : tB = 0 → d ≠ 0 ∧ d ≠ rL1 J := by
    zuibv
    refine ⟨hd0 ht, fun hdr => ?_⟩
    have hlt : ztidz := by_omega
    apply hns' ht
    rw [ht, hdr]
    exact sidePt_split J hP hS₂a hS₂.1 hlt
  exact sideLabel_fused J hP hS₂ hF hf hc hfc hd hB.2.1 hB.2.2.1 hsec hB hρ hV hVs
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf sideCcw sideCross sideDot)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
theorem top_corner_sub (C : Chain) (hP : C.P.Simple) (x : Point) :
    (sideLeftOf C.slitTop C.top ztjhm x →
      sideLeftOf ztxuv C.top ztjhm x) ∧
    (sideLeftOf ztxuv C.top C.slitTop x →
      sideLeftOf ztxuv C.top ztjhm x) := by
  set β := C.sideBeta
  have hN0 := sub_ne_zero.2 ztcld
  have hP0 : ztpix :=
    sub_ne_zero.2 ztdsw
  have hU0 := sub_ne_zero.2 C.sideSlitTop_ne_top
  zucfg
  zucuq
  · rw [← C.sideTour_one_eq_last β hT]
    zumki
    · refine Or.inr (Or.inr (Or.inr ⟨Chazelle.Chain.sideCross_self _,
        Chazelle.Chain.sideDot_self_pos hN0, ?_⟩))
      zux

      exact Chazelle.Chain.sideCcw_not_ray_left hN0 hc.1 hc.2 h
    · refine Or.inr (Or.inr (Or.inr ⟨Chazelle.Chain.sideCross_self _,
        Chazelle.Chain.sideDot_self_pos hN0, ?_⟩))
      zux

      refine Chazelle.Chain.sideCcw_not_ray_right hN0 ?_ ?_ h
      · rw [Chazelle.Chain.sideCross_swap, hc.1, neg_zero]
      · rw [Chazelle.Chain.sideDot_comm]; simp_all
  · have hmain : sideCcw ztblu ztyy
        ztwmj := by
      rcases C.sideGood_sideBeta hP with h | h | h
      · omega
      · omega
      omega
    exact ⟨(Chazelle.Chain.sideCcw_sub_left hN0 hmain),
      (Chazelle.Chain.sideCcw_sub_right hN0 hU0 hP0 hmain)⟩
variable (C : Chain) (x : Point)
/-- The left sector at the first copy of the top (walk vertex `6`). -/
theorem sideLeft_top_first :
    sideLeft (chainModel C).W 6 0 x ↔ sideLeftOf C.slitTop C.top ztjhm x := by
  zubco
  zuigh
  have h1 : (6 + ztz - 1) % ztz = 5 := by
    rw [show 6 + ztz - 1 = 5 + ztz by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]
  have h2 : ztsua % ztz = 1 + 6 := by_simp_all
  rw [h1, h2, C.sideWalk_vtx_five, C.sideWalk_vtx_six, C.sideWalk_vtx_tour _ by_omega]

/-- The left sector at the last copy of the top (walk vertex `2m+6`). -/
theorem sideLeft_top_last :
    sideLeft (chainModel C).W ztcc 0 x ↔
      sideLeftOf ztxuv C.top C.slitTop x := by
  zubco
  zuigh
  have h1 : (2 * C.m + 6 + ztz - 1) % ztz = ztdl + 6 := by
    rw [show 2 * C.m + 6 + ztz - 1 = ztysq + ztz by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  have h2 : ztbjc % ztz = 0 := by
    simp
  rw [h1, h2, C.sideWalk_vtx_tour _ by_simp_all,
    C.sideWalk_vtx_tour _ by_omega, C.sideTour_two_m, C.sideWalk_vtx_zero]

/-- The two copies of the top in the walk of a chain are at the top. -/
theorem sidePt_top_copies :
    sidePt (chainModel C).W 6 0 = C.top ∧ sidePt (chainModel C).W ztcc 0 = C.top := by
  rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, cm_W, C.sideWalk_vtx_six,
    C.sideWalk_vtx_tour _ by_omega, C.sideTour_two_m]
  simp
section Split
variable (J : Merge.Junction)

/-- The split vertex of `C` is the top of `C₁` (`sidePt_splitL` without `TopStrict`). -/
theorem sidePt_splitL0 (hP : J.P.Simple) {S₁ : Set ztf}
    (hS₁ : S₁ ⊆ Merge.augChords J.left) (hS₁f : S₁.Finite) (hlt : lL1 J < lL1 J + lL2 J) :
    sidePt (chainModel J.whole).W
      ztwnx 0 = J.left.top := by
  have hC := corr_left0 J hP hS₁ hS₁f
  have hδ : zthoc := by
    zuccr
    have := hC.hδ by_omega
    omega
  zudti
  have := hC.A2 0 ztbg
  zuigy
  rw [this, show 6 + tpos J.left J.m₁ + lL1 J + lδ J = 6 + tpos J.left J.m₁ + ztjzy by ring]
  exact left_split_top J hδ

/-- Case G of the left correspondence (a nonempty second piece). -/
theorem left_caseG (hlt : lL1 J < lL1 J + lL2 J) :
    lL1 J = 2 * J.left.m - tpos J.left J.m₁ ∧ lδ J = 7 ∧ 0 < tpos J.left J.m₁ ∧
      tpos J.left J.m₁ < 2 * J.left.m := by
  have := tpos_lt J.left J.m₁
  zufd
  unfold lL1 lL2 lδ at *
  grind

/-- **The left sector at the split vertex** is the corner `tour(2m₁-1) → top₁ → tour(1)` of `C₁`. -/
theorem sideLeft_split (hP : J.P.Simple) (hlt : lL1 J < lL1 J + lL2 J)
    (x : Point) :
    sideLeft (chainModel J.whole).W
        ztwnx 0 x ↔
      sideLeftOf (J.left.sideTour J.left.sideBeta ztcgo) J.left.top
        (J.left.sideTour J.left.sideBeta 1) x := by
  zubao
  obtain ⟨hL1, hδ, hτ0, hτ⟩ := left_caseG J hlt
  zumdz
  zuerx
  zufd
  rw [Chazelle.Chain.sideLeft_zero, mod_pred_mod hC.n_pos _ by_omega,
    mod_succ_mod]
  have hprev := hC.A1 ztrsw by_omega
  have hcur := hC.A1 _ le_rfl
  have hnext : (chainModel J.whole).W.vtx
      ((6 + tpos J.whole ztbv + (lL1 J + 1)) % (chainModel J.whole).W.n) =
      (chainModel J.left).W.vtx (ztigv %
        (chainModel J.left).W.n) := by
    have := hC.A2 1 by_omega
    omega
  rw [hprev, hcur, hnext]
  have e1 : (6 + tpos J.left J.m₁ + ztrsw) % (chainModel J.left).W.n =
      ztcgo + 6 := by
    zuhlu
  have e2 : (6 + tpos J.left J.m₁ + lL1 J) % (chainModel J.left).W.n = 2 * J.left.m + 6 := by
    zuhlu
  have e3 : ztigv % (chainModel J.left).W.n = 1 + 6 := by
    rw [hn₁, show 6 + tpos J.left J.m₁ + lL1 J + lδ J + 1 = ztjec + ztcsh by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  rw [e1, e2, e3, cm_W, J.left.sideWalk_vtx_tour _ (show 2 * J.left.m - 1 ≤ 2 * J.left.m by omega),
    J.left.sideWalk_vtx_tour _ by_omega, J.left.sideTour_two_m,
    J.left.sideWalk_vtx_tour _ by_grind]

/-- An attachment is transported along an inclusion of left sectors at the same point. -/
theorem attach_of_sector {W W' : Polygon} {c : Set Point} {p p' : ℕ}
    (hA : SideAttach W c p 0) (hp' : p' < W'.n) (hpt : sidePt W' p' 0 = sidePt W p 0)
    (hsec : ∀ x, sideLeft W p 0 x → sideLeft W' p' 0 x) : SideAttach W' c p' 0 := by
  obtain ⟨-, -, -, hw, r, hr, hl⟩ := hA
  refine ⟨hp', le_rfl, zero_lt_one, by_simp_all, r, hr, fun x hx hxw hxd => ?_⟩
  simp_all

/-- **An attachment at either copy of the top of `C₁` gives an attachment at the split vertex.** -/
theorem attach_split_of_left (hP : J.P.Simple) 
    (hlt : lL1 J < lL1 J + lL2 J) {c : Set Point} {k : ℕ} (hk : k = 6 ∨ k = 2 * J.left.m + 6)
    (hA : SideAttach (chainModel J.left).W c k 0) :
    SideAttach (chainModel J.whole).W c
      ztwnx 0 := by
  zubao
  have hsplit := sidePt_splitL0 J hP ztzi finite_empty hlt
  zuhhn
  refine attach_of_sector hA ztdtk ?_ fun x hx => ?_
  · grind
  · rw [sideLeft_split J hP hlt]
    zuvk
    · exact (top_corner_sub J.left ztrwv x).1
        ((sideLeft_top_first J.left x).1 hx)
    · exact (top_corner_sub J.left ztrwv x).2
        ((sideLeft_top_last J.left x).1 hx)

/-- **Soundness at the split vertex**: a detection hit arriving at a copy of the top of `C₁` gives
the piece attached at the split vertex of `C`. -/
theorem attach_split_of_arrival (hP : J.P.Simple) 
    (hlt : lL1 J < lL1 J + lL2 J) {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k = 6 ∨ k = 2 * J.left.m + 6)
    (hA : Arrival (chainModel J.left).W ztiu σ k 0) :
    SideAttach (chainModel J.whole).W ztxvb
      ztwnx 0 :=
  attach_split_of_left J hP hlt hk ztlga

/-- **Completeness at the split vertex**: a shot of `C` (free, from a point not above the top of
`C₁`) whose first hit is the top of `C₁` is genuine in the model of `C₁`, arriving at the copy
`2m₁+6` of the top when shot to the east and at the copy `6` when shot to the west. -/
theorem genuine_of_split (hP : J.P.Simple) {a : Point}
    (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hfree : FreeAt J.whole a σ)
    (hend : rayPt a σ zton = J.left.top) :
    Genuine J.left a σ zton ∧
      (σ = 1 → Arrival (chainModel J.left).W ztwqt σ
        ztjev 0) ∧
      (σ = -1 → Arrival (chainModel J.left).W ztwqt σ 6 0) := by
  zubao
  zujzp
  have hPl := hP
  zubsr

  zuhhn
  zuerx
  zumdz
  have hNb : (J.left.sideTour J.left.sideBeta 1).2 ≤ J.left.top.2 :=
    J.left.vertex_snd_le_top ztsyj
  have hPb : (J.left.sideTour J.left.sideBeta ztcgo).2 ≤ J.left.top.2 :=
    J.left.vertex_snd_le_top ztsyj
  have hPne := J.left.sideTour_last_ne_top hPl J.left.sideBeta
  have hNne := J.left.sideTour_one_ne_top hPl J.left.sideBeta
  have hW1 : (J.left.sideWalk J.left.sideBeta).vtx _ =
      J.left.sideTour J.left.sideBeta ztcgo := J.left.sideWalk_vtx_tour _ by_omega
  have hW2 : (J.left.sideWalk J.left.sideBeta).vtx ((2 * J.left.m - 1 + 6 + 1) %
      (J.left.sideWalk J.left.sideBeta).n) = J.left.top := by
    rw [J.left.sideWalk_n, show 2 * J.left.m - 1 + 6 + 1 = 2 * J.left.m + 6 by omega,
      Nat.mod_eq_of_lt by_omega, J.left.sideWalk_vtx_tour _ le_rfl, J.left.sideTour_two_m]
  have hW6 : (J.left.sideWalk J.left.sideBeta).vtx ztfmo = J.left.top := by
    rw [zero_add]; exact J.left.sideWalk_vtx_six _
  have hW7 : (J.left.sideWalk J.left.sideBeta).vtx (ztpsi %
      (J.left.sideWalk J.left.sideBeta).n) = J.left.sideTour J.left.sideBeta 1 := by
    rw [J.left.sideWalk_n, show 0 + 6 + 1 = 1 + 6 by omega, Nat.mod_eq_of_lt by_omega,
      J.left.sideWalk_vtx_tour _ by_omega]
  have hya : a.2 = J.left.top.2 := by
    have := congrArg Prod.snd hend; simpa [rayPt] using this
  have hxa : a.1 + σ * T = J.left.top.1 := by
    have := congrArg Prod.fst hend; simpa [rayPt] using this
  -- the neighbours of the top do not lie on the ray before it (the ray is in the domain there)
  have hPw : σ = 1 → ¬ ((J.left.sideTour J.left.sideBeta ztcgo).2 = J.left.top.2 ∧
      (J.left.sideTour J.left.sideBeta ztcgo).1 ≤ J.left.top.1) := by
    zujgg
    set P := J.left.sideTour J.left.sideBeta ztcgo with hPdef
    have hlt : P.1 < J.left.top.1 := by_grind
    set d := J.left.top.1 - P.1 with hd
    zuhy

    have hu0 : 0 ≤ 1 - ε / d := by rw [sub_nonneg, div_le_one hd0]; linarith
    have hu1 : 1 - ε / d < 1 := by have := div_pos hε0 hd0; linarith
    have hm := J.left.sideWalk_tour_pt_mem J.left.sideBeta (i := 2 * J.left.m - 1) by_omega
      ztczk hu0 hu1
    zumuv
    rw [hW1, hW2] at hm
    have heq : rayPt a 1 ztbpt = Geometry.lerp P J.left.top (1 - ε / d) := by
      ext
      · zujov
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hd0.ne']; grind
      · zuhpy
    zugfr

  have hNe : σ = -1 → ¬ ((J.left.sideTour J.left.sideBeta 1).2 = J.left.top.2 ∧
      J.left.top.1 ≤ (J.left.sideTour J.left.sideBeta 1).1) := by
    zujgg
    set N := J.left.sideTour J.left.sideBeta 1 with hNdef
    have hlt : J.left.top.1 < N.1 := by_grind
    set d := N.1 - J.left.top.1 with hd
    zuhy

    have hu0 := (div_pos hε0 hd0).le
    have hu1 : ε / d < 1 := by rw [div_lt_one hd0]; omega
    have hm := J.left.sideWalk_tour_pt_mem J.left.sideBeta (i := 0) by_omega
      by_grind hu0 hu1
    zumuv
    rw [hW6, hW7] at hm
    have heq : rayPt a (-1) ztbpt = Geometry.lerp J.left.top N (ε / d) := by
      ext
      · zujov
        rw [div_mul_cancel₀ _ hd0.ne']; linarith
      · zuhpy
    zugfr

  set N := J.left.sideTour J.left.sideBeta 1
  set P := J.left.sideTour J.left.sideBeta ztcgo
  set t := J.left.top with ht
  have hU1 : (J.left.slitTop - t).1 = 0 := by simp [Chazelle.Chain.slitTop, t]
  have hU2 : 0 < (J.left.slitTop - t).2 := by
    simp only [Chazelle.Chain.slitTop, Prod.snd_sub, t]; linarith [J.left.top_snd_lt_radius]
  have hsub : ∀ s : ℝ, rayPt t s 1 - t = (ztdwb : Point) := by
    intro s; ext <;> zvmxf
  refine ⟨⟨hT0, fun s h0 h1 => dom_left J by_simp_all (by simpa [rayPt] using ha₁), ?_⟩, ?_, ?_⟩
  · rw [hend, ← h6]
    exact hM₁.trace 6 by_omega 0 le_rfl zero_le_one
  · zunq
    refine ⟨by_omega, le_rfl, zero_lt_one, by_simp_all, ?_⟩
    rw [hend, sideLeft_top_last, ← ht]
    zucfg
    rw [hsub]
    refine Chazelle.Chain.sideCcw_west hU1 hU2 rfl by_norm_num
      ztdzb by_grind
      ?_
    zufdo
  · zunq
    refine ⟨by_omega, le_rfl, zero_lt_one, by_grind, ?_⟩
    rw [hend, sideLeft_top_first, ← ht]
    zucfg
    rw [show -(-1 : ℝ) = 1 by norm_num, hsub]
    refine Chazelle.Chain.sideCcw_east hU1 hU2 rfl one_pos
      ztdzb by_grind ?_
    zufdo
end Split
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open WalkEmbed
namespace Sweep
theorem far_attach {M : Model} (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) (x : Point) :
    ∃ (p : ℕ) (t : ℝ), SideAttach M.W e p t ∧ sidePt M.W p t ≠ x := by
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ := hM.ends e he
  grind
section Machine
variable (J : Merge.Junction)
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
theorem boxPt_congr {C C' : Chain} (ht : C.top = C'.top) (hR : C.radius = C'.radius) (e : ℕ) :
    boxPt C e = boxPt C' e := by
  unfold boxPt
  rcases e with _ | _ | _ | _ | _ | _ | _ | e <;> simp [Chazelle.Chain.slitTop, ht, hR]
section Machine
variable (J : Merge.Junction)

/-- The two cases of `¬ VNotTop`. -/
theorem vtop_cases (hv : ¬ VNotTop J) :
    tpos J.whole J.m₁ = 0 ∨ tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m := by
  unfold VNotTop at hv; omega

/-- **The shared vertex is the top of `C`** (`¬ VNotTop`). -/
theorem shared_eq_top (hv : ¬ VNotTop J) : J.shared = J.whole.top := by
  zumh
  zunf
  zucz
  zudnh
  rcases vtop_cases J hv with hA | hB
  · have := walk_tour J.whole J.m₁ 0 by_omega
    rw [add_zero, hA, add_zero, Nat.mod_eq_of_lt by_omega, tourV_right J ztbg,
      tourV_right_zero, cm_W, J.whole.sideWalk_vtx_six] at this
    simp_all
  · have := walk_tour J.whole J.m₁ ztgyh by_omega
    rw [tourV_right J le_rfl, tourV_right_end,
      show 6 + tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m + 6 by omega,
      Nat.mod_eq_of_lt by_omega, cm_W, J.whole.sideWalk_vtx_tour _ le_rfl,
      J.whole.sideTour_two_m] at this
    simp_all

/-- The top of `C₁` is the shared vertex (`¬ VNotTop`). -/
theorem left_top_eq (hv : ¬ VNotTop J) : J.left.top = J.shared := by
  have h := shared_eq_top J hv
  zucz
  zufd
  have hv1 : ztuli := rfl
  have hkm : J.whole.topIdx ≤ J.m₁ :=
    J.whole.topIdx_min by_omega fun i hi => by
      rw [hv1, h]; exact J.whole.vertex_snd_le_top hi
  have hle : J.left.topIdx ≤ J.whole.topIdx :=
    J.left.topIdx_min by_omega fun i hi => by
      rw [← J.whole_vertex, ← J.whole_vertex]
      exact J.whole.vertex_snd_le_top by_omega
  have hge : J.whole.topIdx ≤ J.left.topIdx := by
    have hlt := J.left.topIdx_le
    refine J.whole.topIdx_min by_omega fun i hi => ?_
    rw [J.whole_vertex J.left.topIdx]
    have h3 : (J.left.vertex J.m₁).2 ≤ (J.left.vertex J.left.topIdx).2 :=
      J.left.vertex_snd_le_top by_omega
    have h4 : J.left.vertex J.m₁ = J.whole.top := by_tauto
    zukrz
    exact (J.whole.vertex_snd_le_top hi).trans h3
  show J.left.vertex J.left.topIdx = J.shared
  rw [le_antisymm hle hge, ← J.whole_vertex, h]; rfl

/-- **The box blocks of `C` and `C₁` agree** (`¬ VNotTop`): from the end of the tour of `C` and
of `C₁` (walk vertices `2m + 6` and `2m₁ + 6`), seven edges. -/
theorem box_agree (hv : ¬ VNotTop J) :
    Agree (chainModel J.whole).W (chainModel J.left).W ztjew ztjev 7 := by
  zubre
  have h1 := walk_box J.whole 0 e he
  have h2 := walk_box J.left 0 e he
  have hτ := tpos_lt J.whole 0
  have hτ₁ := tpos_lt J.left 0
  rw [show 6 + tpos J.whole 0 + (2 * J.whole.m - tpos J.whole 0) + e = 2 * J.whole.m + 6 + e by
    omega] at h1
  rw [show 6 + tpos J.left 0 + (2 * J.left.m - tpos J.left 0) + e = 2 * J.left.m + 6 + e by
    omega] at h2
  zubuw
  refine boxPt_congr ?_ ?_ e
  · rw [← shared_eq_top J hv, left_top_eq J hv]
  rfl

/-! ## Offsets of the left stretch in all cases -/

/-- The offset of the base of the left stretch. -/
noncomputable def lOff : ℕ :=
  dOf (chainModel J.whole).W.n ztve ztxfw

/-- **The offset of the left base**: `2 m₂` when the second copy of `v` comes before the end of
the tour of `C`, else `2 m₂ + 7` (the box block of `C` is passed in between). -/
theorem lOff_eq : lOff J = if tpos J.whole J.m₁ + 2 * J.m₂ < 2 * J.whole.m then 2 * J.m₂
    else 2 * J.m₂ + 7 := by
  zumh
  zunf
  zucz
  zudnh
  unfold lOff dOf
  rw [tpos_second J, hn]
  zus
  · rw [Nat.mod_eq_of_lt h, show 6 + ztevy + ztcsi -
      ztve = 2 * J.m₂ + ztcsi by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]
  · have e : ztevy % ztjex =
        tpos J.whole J.m₁ + 2 * J.m₂ - 2 * J.whole.m := by
      zul
    rw [e, show 6 + (tpos J.whole J.m₁ + 2 * J.m₂ - 2 * J.whole.m) + ztcsi -
        ztve = 2 * J.m₂ + 7 by omega, Nat.mod_eq_of_lt by_omega]

/-- The left stretch fits after its base offset. -/
theorem lOff_add_llen : lOff J + llen J ≤ (chainModel J.whole).W.n := by
  zumh
  zunf
  zucz
  zudnh
  rw [lOff_eq, hn]
  unfold llen
  zuezn
  by_cases h : tpos J.whole J.m₁ + 2 * J.m₂ < 2 * J.whole.m
  · grind
  · have e : ztevy % ztjex =
        tpos J.whole J.m₁ + 2 * J.m₂ - 2 * J.whole.m := by
      zul
    grind

/-- `lOff = L` when the shared vertex is not the top of `C`. -/
theorem lOff_of_vnt (hv : VNotTop J) : lOff J = rlen J := by
  zunf
  zucz
  zuebc
  rw [lOff_eq]; unfold rlen; grind
variable {d : ℕ}
/-- **Offsets of the left stretch** (all cases): the position `d` of the left stretch has offset
`lOff + d`. -/
theorem off_left_gen (hd : d < llen J) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
      ztbakt =
      (lOff J : ℝ) + d + t := by
  zumh
  zunf
  zudpt
  zufus
  have hgL : 6 + tpos J.whole ztbv < (chainModel J.whole).W.n := by_omega
  have hsum := lOff_add_llen J
  have e : ztwtl % (chainModel J.whole).W.n =
      (6 + tpos J.whole J.m₁ + ztrsx) % (chainModel J.whole).W.n := by
    have hb := add_dOf hg hgL
    unfold lOff
    zuork
    conv_rhs => rw [← Nat.mod_add_mod, hb]
  rw [e, off_key hg by_omega ht ht1]
  simp

/-- **A genuine hit on the left stretch is a cut at offset `lOff + d + t`** (all cases; see
`cut_of_genuine`). -/
theorem cut_of_genuine_gen (hP : J.P.Simple) {a : Point}
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) (hhit : J.whole.hitParam a σ = τ)
    {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ} (hsec : t = 0 → d ≠ 0 ∧ d ≠ lL1 J)
    (hA : Arrival (chainModel J.left).W ztiu σ
      ztok t) :
    SideAttach (chainModel J.whole).W ztxc
        ztwkx t ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ztbakt =
        (lOff J : ℝ) + d + t := by
  zujx
  · zulbc

    exact attach_whole_of_arrival J hP hσ hτ hd hsec hA
  · exact off_left_gen J (by zuooo; exact hd) hA.2.1 hA.2.2.1

/-! ## Detection on the box block of `C` (`¬ VNotTop`) -/

/-- **Offsets of the box block of `C`**: the position `(2m + 6 + d, t)` has offset
`2m - τ + d + t`. -/
theorem off_box_pos (hd : d < 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
      ztebm =
      ((2 * J.whole.m - tpos J.whole J.m₁ : ℕ) : ℝ) + d + t := by
  zumh
  zunf
  zufus
  rw [show 2 * J.whole.m + 6 + d = 6 + tpos J.whole J.m₁ + (2 * J.whole.m - tpos J.whole J.m₁ + d)
    by omega, off_key hg by_omega ht ht1]
  simp

/-- **Soundness on the box block**: a detection hit arriving at a position of the box block of the
model of `C₁` (not its first vertex) gives the piece attached at the corresponding position of
the box block of `C`. -/
theorem attach_box_of_arrival (hv : ¬ VNotTop J) {a : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) {d : ℕ} (hd : d < 7) {t : ℝ}
    (hsec : t = 0 → 1 ≤ d)
    (hA : Arrival (chainModel J.left).W ztiu σ
      ztbag t) :
    SideAttach (chainModel J.whole).W ztxvb
      ztbxi t := by
  zubjb

  exact (hB.sideAttach_iff hn hn₁ hd hsec _).2 ztlga

/-- **Completeness on the box block**: a shot of `C` (free, from a point not above the top of
`C₁`) whose chord is attached at a position of the box block of `C` (not its first vertex) at its
first hit is genuine in the model of `C₁`, arriving at the corresponding position of its box
block. -/
theorem genuine_of_attach_box (hP : J.P.Simple) (hv : ¬ VNotTop J)
    {a : Point} (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfree : FreeAt J.whole a σ) {d : ℕ} (hd : d < 7) {t : ℝ} (hsec : t = 0 → 1 ≤ d)
    (hA : SideAttach (chainModel J.whole).W ztxc
      ztbxi t)
    (hend : sidePt (chainModel J.whole).W
      ztbxi t =
        rayPt a σ zton) :
    Genuine J.left a σ zton ∧
      Arrival (chainModel J.left).W ztwqt σ
        ztbag t := by
  zubjb

  zubao
  zujzp
  zubsr

  have hA₁ := (hB.sideAttach_iff hn hn₁ hd hsec _).1 hA
  have hpt : sidePt (chainModel J.left).W
      ztbag t = rayPt a σ T := by
    rw [← hB.sidePt_eq hd t]; omega
  refine ⟨⟨hT0, fun s h0 h1 => dom_left J by_simp_all by_simp_all, ?_⟩, ?_⟩
  · zuezz
    zuitk
  · zusl

    have hmem : ztxzu := by
      zudlx

      have e : ztxti := by
        zufqp
      zui
      exact Geometry.lerp_mem_segment _ _ by_positivity
        ztmdf
    have hne : ztxzv := by
      zuq
      have := congrArg Prod.fst h
      zudv
      zubbe
    zuehc
    have hdist : ztxtg := by
      zuhkx
    zuhyy
    have h1 : sideLeft (chainModel J.left).W ztbag t
        (rayPt (sidePt (chainModel J.left).W
          ztbag t) (-σ) s) := by
      grind
    have := (sideLeft_rayPt_iff _ _ t _ hs0 one_pos).1 h1
    grind

/-- **A genuine hit on the box block is a cut** of `F` at the corresponding position of the box
block of `C`, at the offset `2m - τ + d + t`. -/
theorem cut_of_genuine_box (hv : ¬ VNotTop J) {a : Point}
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) (hhit : J.whole.hitParam a σ = τ)
    {d : ℕ} (hd : d < 7) {t : ℝ} (hsec : t = 0 → 1 ≤ d)
    (hA : Arrival (chainModel J.left).W ztiu σ
      ztbag t) :
    SideAttach (chainModel J.whole).W ztxc
        ztbxi t ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ztebm =
        ((2 * J.whole.m - tpos J.whole J.m₁ : ℕ) : ℝ) + d + t := by
  refine ⟨?_, off_box_pos J hd hA.2.1 hA.2.2.1⟩
  zulbc

  exact attach_box_of_arrival J hv hσ hτ hd hsec hA
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- The direction of a direction code. -/
theorem dirOf_cases (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  zubqi

/-! ## The first hit of `C`, one theorem per kind of query -/

/-! ## The compositions -/

/-- The data of an answer record at the first hit parameter `T`: positions of the walk of `C` of the
query point and of the hit point (height code `h + 1`), at which the chord is attached. -/
def RecordData (Q : Polygon) (z : Point) (σ T : ℝ) (h pz pw lp rp : ℕ) : Prop :=
  (Q.vtx h).2 = z.2 ∧ (chainModel J.whole).pos Q ztgpf = z ∧
    (chainModel J.whole).pos Q ztgpe = rayPt z σ T ∧
    SideAttach (chainModel J.whole).W ztxvc pz
      ((chainModel J.whole).param Q ztgpf) ∧
    SideAttach (chainModel J.whole).W ztxvc pw
      ((chainModel J.whole).param Q ztgpe) ∧
    ztkic ∧ ztiua
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (freeIn regionsIn sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- The chain of side `1` is `C₂`. -/
theorem sideChain_one : sideChain J 1 = J.right := ite_eq_right one_ne_zero
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- **An admissible chord of `C` through a point of a chord `c ∈ S₂` in the domain of `C₂` lies in
`c`**: its points beyond an end of `c` would put that end (not in the domain of `C₂`) strictly
inside the chord, in the domain of `C`. -/
theorem sub_of_mem_dom (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e c : Set Point}
    (he : e ∈ (chainModel J.whole).Adm) (hc : c ∈ S₂) {K : Point} (hKe : K ∈ e) (hKc : K ∈ c)
    (hKD : K ∈ J.right.dom) : e ⊆ c := by
  zunw
  obtain ⟨y, l, r, hH, hy, hceq, -, -⟩ := Merge.augChords_spec ztbac
  obtain ⟨a, b, hab, heab, hab2, hopen, -, -⟩ := hM.ends e he
  subst hceq
  obtain ⟨hKy, hKl, hKr⟩ := hKc
  have hKpt : K = ((K.1, y) : Point) := by_grind
  have hl : l < K.1 := by
    rcases hKl.lt_or_eq with h | h
    · zubh
    · exfalso; apply hH.left_not; grind
  have hr : K.1 < r := by
    rcases hKr.lt_or_eq with h | h
    · zubh
    · exfalso; apply hH.right_not; grind
  have hya : a.2 = y := by
    have := hKe; rw [heab] at this
    obtain ⟨v, -, -, hv⟩ := Geometry.mem_segment_iff_lerp.1 this
    have h2 : K.2 = a.2 := by zvmyq; simp only [Geometry.lerp_snd]; grind
    grind
  -- a point strictly between two points of the chord is in the domain of `C`
  have inner : ∀ u₁ u₂ : ℝ, u₁ ∈ Icc (0 : ℝ) 1 → u₂ ∈ Icc (0 : ℝ) 1 → ∀ x : ℝ,
      (lerp a b u₁).1 < x → x < (lerp a b u₂).1 → (ztjw : Point) ∈ J.whole.dom := by
    intro u₁ u₂ hu₁ hu₂ x hx1 hx2
    have hd : (lerp a b u₂).1 - (lerp a b u₁).1 ≠ 0 := by_linarith
    have hne : ztsdr := by
      grind
    set s := u₁ + ztucp * (ztfvg / ztdei)
      with hs
    have hq : 0 < ztfvg / ztdei :=
      div_pos by_linarith by_linarith
    have hq1 : ztfvg / ztdei < 1 := by
      zubie
    have hu : u₁ ≠ u₂ := by_grind
    have hs01 : ztgut := by
      rcases lt_or_gt_of_ne hu with h | h
      · constructor <;> nlinarith [hu₁.1, hu₂.2]
      · constructor <;> nlinarith [hu₁.2, hu₂.1]
    have hpt : lerp a b s = (ztjw : Point) := by
      have e1 : (lerp a b u₂).1 - (lerp a b u₁).1 = ztucp * ztbco := by
        simp only [Geometry.lerp_fst]; ring
      zubjw
      · zudlh
        rw [hs, e1]
        have hu' : u₂ - u₁ ≠ 0 := by_grind
        field_simp
        zudlh
        ring
      · zudbx
    zvnbr; tauto
  zugh
  zumfb
  rw [heab] at hz'
  obtain ⟨u₂, hu₂0, hu₂1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz'
  have hK' := hKe
  rw [heab] at hK'
  obtain ⟨u₁, hu₁0, hu₁1, hKu⟩ := Geometry.mem_segment_iff_lerp.1 hK'
  have hzy : (lerp a b u₂).2 = y := by
    zudbx
  refine ⟨hzy, ?_, ?_⟩
  · zux

    have := inner u₂ u₁ by_grind by_grind l hc by_grind
    exact hH.left_not ztrou
  · zux

    have := inner u₁ u₂ by_grind by_grind r by_grind hc
    exact hH.right_not ztrou

/-- **The two chords of a tie lie in one chord of `S₂`**: two chords of `F₂⁺` attached at one
position whose point is in the domain of `C₂`. -/
theorem tie_parent (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e e' : Set Point} (he : e ∈ F₂plus J S₂)
    (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hA' : SideAttach (chainModel J.whole).W e' p t)
    (hKD : sidePt (chainModel J.whole).W p t ∈ J.right.dom) :
    ∃ c ∈ S₂, e ⊆ c ∧ e' ⊆ c := by
  zunw
  zudnk
  set K := sidePt (chainModel J.whole).W p t with hK
  have hKe := hA.2.2.2.1
  have hKe' := hA'.2.2.2.1
  rcases F₂plus_cases J hS₂ he with ⟨c, hc, hec⟩ | ⟨hv, hvy⟩ | ⟨ht, hty⟩
  · exact ⟨c, hc, hec, sub_of_mem_dom J hP hS₂ ztmkq hc hKe' (hec hKe) hKD⟩
  all_goals
    rcases F₂plus_cases J hS₂ he' with ⟨c, hc, hec⟩ | ⟨hv', hvy'⟩ | ⟨ht', hty'⟩
    · exact ⟨c, hc, sub_of_mem_dom J hP hS₂ ztcik hc hKe (hec hKe') hKD, hec⟩
    all_goals exfalso
  -- two chords through points of `C₂` (the shared vertex or the top of `C₂`) on both sides of `K`
  all_goals
    have hdir := hM.tie_pair hFs he he' ztnr hA hA'
  · -- both through the shared vertex
    zucdg

  · -- the shared vertex and the top of `C₂` at one height: they coincide
    have hvt := shared_eq_top_of_snd J
      by_grind
    zucdg

  · have hvt := shared_eq_top_of_snd J
      by_grind
    zucdg

  · -- both through the top of `C₂`
    have htD : J.right.top ≠ K := fun h =>
      J.right.not_mem_set_of_mem_dom by_grind J.right.top_mem_set
    grind

/-- **A chord of `F₂⁺` inside a chord `c ∈ S₂`, attached at a point of the domain of `C₂`, is the
chord seen from an endpoint of `c`**: from the left end in the direction `1` or from the right end
in the direction `-1`. -/
theorem piece_of_parent (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂)
    (hec : e ⊆ c) {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W e p t)
    (hKD : sidePt (chainModel J.whole).W p t ∈ J.right.dom) :
    (FreeAt J.whole ztffp 1 ∧ e = Merge.shoot J.whole ztffp 1) ∨
      (FreeAt J.whole ztffq (-1) ∧ e = Merge.shoot J.whole ztffq (-1)) := by
  zunw
  zudnk
  zucol
  have hlD := fun h => hH.left_not ztrot
  have hrD := fun h => hH.right_not ztrot
  -- the far end of `e` is an end of `c`
  obtain ⟨a, b, hab, heab, -, hopen, -, -⟩ := hM.ends e ztcik
  have hK := hA.2.2.2.1
  set K := sidePt (chainModel J.whole).W p t
  -- an end of `c` lies in `e`
  have hend : (ztetv : Point) ∈ e ∨ (ztevf : Point) ∈ e := by
    rcases F₂plus_cases J hS₂ he with ⟨c', hc', hec'⟩ | ⟨hv, -⟩ | ⟨ht, -⟩
    · -- a fused piece: its origin is an end of its chord, which is `c`
      rcases he with ((⟨c₁, hc₁, hfree, rfl⟩ | ⟨c₁, hc₁, hfree, rfl⟩) | hsh) | htop
      · zuhyi
        have ho : Merge.lend c₁ ∈ Merge.shoot J.whole _ 1 := origin_mem J
        have hsub : Merge.shoot J.whole _ 1 ⊆ c₁ :=
          Merge.Junction.shoot_lend_subset J by_grind
        obtain ⟨y₁, l₁, r₁, hH₁, -, hc₁eq, hl₁, -⟩ := Merge.augChords_spec ztvuc
        have hsame : c₁ = c := by
          zuss

          · simp_all
          · exfalso
            zuy
            · exact hH.left_not by_simp_all
            · exact hH.right_not by_simp_all
        simp_all
      · zuhyi
        have ho : Merge.rend c₁ ∈ Merge.shoot J.whole _ (-1) := origin_mem J
        have hsub : Merge.shoot J.whole _ _ ⊆ c₁ :=
          Merge.Junction.shoot_rend_subset J by_grind
        obtain ⟨y₁, l₁, r₁, hH₁, -, hc₁eq, -, hr₁⟩ := Merge.augChords_spec ztvuc
        have hsame : c₁ = c := by
          zuss

          · simp_all
          · exfalso
            zuy
            · exact hH.left_not by_simp_all
            · exact hH.right_not by_simp_all
        simp_all
      · zufle
        have hv : J.shared ∈ J.whole.chordSet J.m₁ σ := by
          have : ztuli := rfl
          zvnnr; exact Geometry.left_mem_segment _ _
        zuhfs
        zuri

        have hvD := fun h =>
          J.right.not_mem_set_of_mem_dom h J.shared_mem_right
        zukgn
        zudsj
        · zudsk
          · zugke
          grind
        grind
      · obtain ⟨σ, -, -, rfl⟩ := htop
        have hv' : ztxmm := by
          zubut
        have hv : ztzor := by
          zugxx
        zuhfs
        zuri

        have hvD := fun h =>
          J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
        zukgm
        zudsj
        · zudsk
          · zugke
          grind
        grind
    · zuhfs
      zuri

      have hvD := fun h =>
        J.right.not_mem_set_of_mem_dom h J.shared_mem_right
      zukgn
      zudsj
      · zudsk
        · zugke
        grind
      grind
    · have hvc := hec ht
      zuri

      have hvD := fun h =>
        J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
      zukgm
      zudsj
      · zudsk
        · zugke
        grind
      grind
  -- the chord seen from that end
  rcases hend with hle | hre
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole ztcik hle hlD
    zur
    · simp_all
    · exfalso
      -- the chord seen to the west from the left end leaves `c`
      obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole
        ztqfq ztbt hfree
      have hmem : rayPt (ztetv : Point) (-1) (J.whole.hitParam ztetv (-1)) ∈ e := by
        zuhlp
      have := hec hmem
      zukts
      obtain ⟨-, h1, -⟩ := this
      zuipt

  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole ztcik hre hrD
    zur
    · exfalso
      obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole
        ztqfq ztp hfree
      have hmem : rayPt (ztevf : Point) 1 (J.whole.hitParam ztevf 1) ∈ e := by
        zuhlp
      have := hec hmem
      zukts
      obtain ⟨-, -, h1⟩ := this
      zuipt

    simp_all
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Near
variable {M : Model}

/-- **A region faced just after a position is faced at nearby later non-cut positions.** -/
theorem faces_near_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p : ℕ} {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) {U : Set Point}
    (hW : AfterFaces M p t U) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ t + s < 1 ∧ ¬ M.IsCut F ztwoq ∧ M.Faces p ztuf U := by
  zugrb
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    ztzeq
  zucmv
  set s := min ztbng ztxxr / 2 with hs
  have hm : 0 < min ztbng ztxxr :=
    lt_min ztkam (lt_min hε by_linarith)
  have h1 := min_le_left ztbng ztxxr
  have h2 := min_le_right ztbng ztxxr
  zubcm

  have h5 := min_le_left ε ztca
  have h6 := min_le_right ε ztca
  refine ⟨s, by_linarith, by_linarith, by_linarith, ?_, hW' s by_linarith by_linarith
    by_linarith⟩
  have := hsub ztdxm
  grind
variable {n g p : ℕ}
/-- The offset of the position just before a walk vertex. -/
theorem off_before_vertex (hg : g < n) (hp : p < n) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hpos : 0 < off n g ztmm) :
    off n g ztxqb = off n g ztmm - s := by
  have hpg : p ≠ g := by
    intro h; subst h; simp [off_self] at hpos
  zucyn
  · zufsw
    zui
    have hn1 : ztfzm := by_simp_all
    rw [hn1]
    zumtr
    have hg0 : (0 : ℝ) < g := by
      positivity
    have hgn : (g : ℝ) + 1 ≤ n := by exact_mod_cast hg
    grind
  · have e : ztxfl := by
      zuxw
    zui
    have hp1' : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by_simp_all
    rw [hp1']
    zumtr
    rcases lt_or_gt_of_ne hpg with h | h
    · have h' : (p : ℝ) + 1 ≤ g := by exact_mod_cast h
      grind
    · have h' : (g : ℝ) + 1 ≤ p := by exact_mod_cast h
      grind

/-- The offset of a position before `(p, t)` on the same edge. -/
theorem off_before_edge (hg : g < n) (hp : p < n) {t s : ℝ} (hs0 : 0 < s)
    (hst : s < t) (ht1 : t < 1) :
    off n g ((p : ℝ) + ztfuw) = off n g ztdj - s := by
  have := off_add_small hg hp (t := t - s) (s := s) by_linarith hs0.le by_linarith
  simp_all

/-- **A region faced just before a position is faced at nearby earlier non-cut positions**
(at positive offset). -/
theorem faces_near_before (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℕ} (hg : g < M.W.n) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hpos : 0 < off M.W.n g ztdj) {U : Set Point}
    (hW : BeforeFaces M p t U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℕ) (u : ℝ), q < M.W.n ∧ u ∈ Ioo (0 : ℝ) 1 ∧ ¬ M.IsCut F ztxy ∧
      M.Faces q u U ∧ off M.W.n g ztdj - ε < off M.W.n g ztxy ∧
      off M.W.n g ztxy < off M.W.n g ztdj := by
  obtain ⟨δ, hδ, hWp, hW0⟩ := hW
  zudsi
  · obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (eventually_not_cut_before hM hF hfin ztdj)
    zucmv
    set s := min ztbng ztkaz / 2 with hs
    have hm : 0 < min ztbng ztkaz := lt_min ztkam (lt_min hε htp)
    have h1 := min_le_left ztbng ztkaz
    have h2 := min_le_right ztbng ztkaz
    zubcm

    have h5 := min_le_left ε t
    have h6 := min_le_right ε t
    have hst : ztslv := by_linarith
    have hoff := off_before_edge hg hp (show 0 < s by linarith) hst ht1
    refine ⟨p, t - s, hp, ztbcx, ?_, hWp htp s by_linarith by_linarith hst,
      by grind, by_grind⟩
    have := hsub ztdxm
    grind
  · -- at a walk vertex: the end of the previous edge
    set q := ztoh % M.W.n with hq
    have hqn : q < M.W.n := Nat.mod_lt _ by_omega
    have hkey : ∀ s : ℝ, (q : ℝ) + zteb = (p : ℝ) - s ∨ (q : ℝ) + zteb = (M.W.n : ℝ) - s := by
      zumhi
      zucyn
      · right
        have e : ztcrd := by
          simp
        zugek
      · left
        have e : ztxfk := by
          rw [show p + M.W.n - 1 = ztoq + M.W.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega]
        zugek
    obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      ((eventually_not_cut_before hM hF hfin (p : ℝ)).and
        (eventually_not_cut_before hM hF hfin (M.W.n : ℝ)))
    zucmv
    set s := min ztbng ztkay / 2 with hs
    have hm : 0 < min ztbng ztkay := lt_min ztkam (lt_min hε one_pos)
    have h1 := min_le_left ztbng ztkay
    have h2 := min_le_right ztbng ztkay
    zubcm

    have h5 := min_le_left ε (1 : ℝ)
    have h6 := min_le_right ε (1 : ℝ)
    zudpf
    have hs1 : ztdrm := by_linarith
    have hoff := off_before_vertex hg hp hs0 hs1 by_omega
    simp only [add_zero] at hoff hpos ⊢
    refine ⟨q, 1 - s, hqn, ztbcx, ?_, hW0 rfl s hs0 by_linarith,
      by grind, by_grind⟩
    have hns := hsub ⟨hs0, show s < δ₁ by linarith⟩
    simp only [mem_ofPred_eq] at hns
    rcases hkey s with h | h <;> zvmwc
    · grind
    grind
end Near
section Machine
variable (J : Merge.Junction)
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
variable (J : Merge.Junction)

/-! ## Offsets -/

/-- The base of the offsets: the copy of the shared vertex on the `C₂` side. -/
noncomputable def gW : ℕ := 6 + tpos J.whole J.m₁

/-- The offset of a key of the walk of `C`. -/
noncomputable def oW (x : ℝ) : ℝ := off (chainModel J.whole).W.n (gW J : ℝ) x

/-- The length of the right stretch: the `C₁` part is the offsets `[Lst, n)`. -/
noncomputable def Lst : ℕ := rL1 J + rL2 J

/-- No cut of `F₂⁺` has its offset strictly between `a` and `b`. -/
def NoCutIn (S₂ : Set ztf) (a b : ℝ) : Prop :=
  ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x → x < (chainModel J.whole).W.n →
    ¬ (a < oW J x ∧ oW J x < b)

/-- **The label set** `Λ` contains every label of the region faced just after `(p, t)`, up to the
gap labels. -/
def LabIn (S₂ : Set ztf) (p : ℕ) (t : ℝ) (Λ : Set ztf) : Prop :=
  ∀ G ∈ (chainModel J.whole).regions ztbi, AfterFaces ztbm p t G →
    ∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V → V ∈ Λ ∨ GapLab J S₂ V

/-! ## Stage 3 → 4: the event log -/

/-- **The event log** (keys `(p, t)` of the walk of `C`, label sets). -/
def LogOK (S₂ : Set ztf) (es : List ztwws) : Prop :=
  es ≠ [] ∧
  (∀ x ∈ es, x.1 < (chainModel J.whole).W.n ∧ 0 ≤ x.2.1 ∧ x.2.1 < 1 ∧
    (Lst J : ℝ) ≤ oW J ztbui) ∧
  ztxsp ∧
  es.Pairwise ztxxd ∧
  (∀ i, i + 1 < es.length →
    NoCutIn J S₂ ztbarp
      ztbarq) ∧
  (∀ x ∈ es.getLast?, NoCutIn J S₂ (oW J ztbui) (chainModel J.whole).W.n) ∧
  ∀ x ∈ es, LabIn J S₂ x.1 x.2.1 x.2.2

/-! ## Stage 2 → 3: the stops -/

/-- **The stop chords**: the shared chords and the wall pieces (`StopChord`), and the top chords
(chords of `C` through the top of `C₂`, shot from it). -/
def StopChord2 (S₂ : Set ztf) (e : Set Point) : Prop :=
  StopChord J S₂ e ∨
    ∃ σ : ℝ, ztdd ∧ FreeAt J.whole J.right.top σ ∧
      e = Merge.shoot J.whole J.right.top σ

/-- **The stop list**: exactly the attachments on the `C₁` part of the stop chords of `F₂⁺`,
sorted by offset (keys `(p, t)` and chords). -/
def StopsOK (S₂ : Set ztf) (ss : List ztpet) : Prop :=
  (∀ s ∈ ss, s.2.2 ∈ F₂plus J S₂ ∧ StopChord2 J S₂ s.2.2 ∧
    SideAttach (chainModel J.whole).W s.2.2 s.1 s.2.1 ∧ (Lst J : ℝ) ≤ oW J (s.1 + s.2.1)) ∧
  (∀ e ∈ F₂plus J S₂, StopChord2 J S₂ e → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W e p t → (Lst J : ℝ) ≤ oW J ztk → (p, t, e) ∈ ss) ∧
  ss.Pairwise (fun x y => oW J ztbui ≤ oW J ztoki) ∧ ss.Nodup

/-! ## Stage 3 → side-1 answers: the endpoint table -/

/-- The origin of the endpoint query `j` of a chord list in the model `M₂`: the left end of chord
`j / 2` for even `j`, its right end for odd `j`. -/
noncomputable def endOrigin (Q : Polygon) (N : NF) (j : ℕ) : Point :=
  if j % 2 = 0 then Merge.lend ztwqa
  else Merge.rend ztwqa

/-- The direction of the endpoint query `j` (east for even `j`). -/
noncomputable def endDir (j : ℕ) : ℝ := if j % 2 = 0 then 1 else -1

/-- **The endpoint table** for the chords of `N₂` whose origin is a point of `C₂` other than the
shared vertex and the top of `C₂` (the other origins give stop chords): `some (p, t)` is the far
attachment, on the `C₁` part, of the chord of `C` seen from the origin; `none` says that this chord
does not end on `C₁` (it is the chord seen in `C₂`). -/
def TabOK (Q : Polygon) (N : NF) (T : ℕ → Option zthlt) : Prop :=
  ∀ j, j < 2 * N.nChords → endOrigin J Q N j ∈ J.right.set → endOrigin J Q N j ≠ J.shared →
    endOrigin J Q N j ≠ J.right.top →
    FreeAt J.whole zttr ztri ∧
    match T j with
    | some (p, t) =>
        SideAttach (chainModel J.whole).W
            ztxmy p t ∧
          sidePt (chainModel J.whole).W p t =
            rayPt zttr ztri
              ztztr ∧
          (Lst J : ℝ) ≤ oW J ztk
    | none => J.whole.hitParam zttr ztri =
        J.right.hitParam zttr ztri

/-! ## Region indices of a normal form -/

/-- The region correspondence of a valid normal form (a fixed choice; proofs only). -/
noncomputable def regOf (M : Model) (Q : Polygon) (N : NF) : ℕ → Set Point := by
  classical
  exact if h : IsNF M Q N then Classical.choose h.2.2.2 else fun _ => ∅
theorem regOf_spec {M : Model} {Q : Polygon} {N : NF} (h : IsNF M Q N) :
    RegionCorr M Q N ztiak ∧ ChordSidesOK M Q N ztiak ∧
      ArcsOK M Q N ztiak ∧ RegionsOK M Q N ztiak ∧ SeqOK M Q N ∧
      ztiby ∧
      ∀ j, j < N.arcs.length → ProperPos M Q Q.n (N.arc j).s ∧ ProperPos M Q Q.n (N.arc j).e := by
  classical
  unfold regOf
  zulpp
  exact Classical.choose_spec h.2.2.2

/-! ## Memory layouts -/

/-- The chord of a stop record: kind `0` shared, `1` wall piece of chord `k`, `2` top. -/
noncomputable def stopSet (Q : Polygon) (N : NF) (kind k b : ℕ) : Set Point :=
  if kind = 0 then Merge.shoot J.whole J.shared ztkz
  else if kind = 1 then
    Merge.shoot J.whole (endOrigin J Q N ztxul) ztkz
  else Merge.shoot J.whole J.right.top ztkz

/-- `S` stop records of five words at `A`. -/
def StopRecsAt (m : ℕ → ℕ) (A : ℕ) (rs : List ztcf) : Prop :=
  ∀ i, i < rs.length →
    m ztjgj = (rs.getD i ztip).1 ∧
    m ztgzo = (rs.getD i ztip).2.1 ∧
    m ztnim = (rs.getD i ztip).2.2.1 ∧
    m ztnin = (rs.getD i ztip).2.2.2.1 ∧
    m ztnio = (rs.getD i ztip).2.2.2.2

/-- The stop list of the records. -/
noncomputable def stopsOf (Q : Polygon) (N : NF) (rs : List ztcf) :
    List ztpet :=
  rs.map fun r => (r.1, (chainModel J.whole).param Q ztbhg,
    stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2)

/-- `E` log records of seven words at `A`: key `(e, h)`, label count `n ≤ 4`, four labels. -/
def LogRecsAt (m : ℕ → ℕ) (A : ℕ) (rs : List ztck) : Prop :=
  ∀ i, i < rs.length →
    m (A + 7 * i) = (rs.getD i ztem).1 ∧
    m (A + 7 * i + 1) = (rs.getD i ztem).2.1 ∧
    m (A + 7 * i + 2) = (rs.getD i ztem).2.2.1 ∧
    m (A + 7 * i + 3) = (rs.getD i ztem).2.2.2.1 ∧
    m (A + 7 * i + 4) = (rs.getD i ztem).2.2.2.2.1 ∧
    m (A + 7 * i + 5) = (rs.getD i ztem).2.2.2.2.2.1 ∧
    m (A + 7 * i + 6) = (rs.getD i ztem).2.2.2.2.2.2

/-- The label set of a log record: the regions (`regOf`) of its first `n ≤ 4` labels. -/
noncomputable def labSet (Q : Polygon) (N : NF) (n l₀ l₁ l₂ l₃ : ℕ) : Set ztf :=
  (regOf ztj Q N) ''
    {l | (0 < n ∧ l = l₀) ∨ (1 < n ∧ l = l₁) ∨ (2 < n ∧ l = l₂) ∨ (3 < n ∧ l = l₃)}

/-- The event log of the records. -/
noncomputable def logOf (Q : Polygon) (N : NF) (rs : List ztck) :
    List ztwws :=
  rs.map fun r => (r.1, (chainModel J.whole).param Q ztbhg,
    labSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2)

/-- The endpoint table at `A`: three words `(f, e, h)` per query. -/
noncomputable def tabOf (Q : Polygon) (m : ℕ → ℕ) (A : ℕ) (j : ℕ) : Option zthlt :=
  if m (A + 3 * j) = 1 then
    some (m ztnih, (chainModel J.whole).param Q ⟨m ztnih, m (A + 3 * j + 2)⟩)
  else none
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed
namespace Sweep
section EvInv
variable (J : Merge.Junction)

/-- **A bracket chord**: every attachment lies on the `C₁` part. -/
def EvBrk (e : Set Point) : Prop :=
  ∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W e p t → (Lst J : ℝ) ≤ oW J ztk

/-- **The offset `o` is enclosed**: strictly between the two attachments of a chord of `F₂⁺` on
the `C₁` part, or after the `C₁` attachment of a chord attached at offset `0` (a pocket). -/
def EvEncl (S₂ : Set ztf) (o : ℝ) : Prop :=
  ∃ e ∈ F₂plus J S₂, ∃ (pa pb : ℕ) (ta tb : ℝ), SideAttach (chainModel J.whole).W e pa ta ∧
    SideAttach (chainModel J.whole).W e pb tb ∧
    sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb ∧
    (Lst J : ℝ) ≤ oW J ztbf ∧ oW J ztbf < o ∧ (o < oW J ztbd ∨ oW J ztbd = 0)

/-- **A label set is valid for a region**: some valid label (`Valid`) of the region is in the set
or is a gap label. -/
def EvVal (S₂ : Set ztf) (Λ : Set ztf) (G : Set Point) : Prop :=
  ∃ L, (L ∈ Λ ∨ GapLab J S₂ L) ∧ L ∈ (chainModel J.right).regions S₂ ∧ Valid J S₂ G L

/-- **The facts at a non-cut position**: it is enclosed, or the regions faced there have a valid
label set. -/
def EvPos (S₂ : Set ztf) (Λ : Set ztf) (p : ℕ) (t : ℝ) : Prop :=
  EvEncl J S₂ ztxae ∨
    ∀ G ∈ (chainModel J.whole).regions ztbi, (chainModel J.whole).Faces p t G →
      EvVal J S₂ Λ G

/-- **The invariant of the event loop** at a key with offset `oK` and label set `Λ`: every later
non-cut position reached through keys carrying only bracket chords has `EvPos`. -/
def EvInv (S₂ : Set ztf) (oK : ℝ) (Λ : Set ztf) : Prop :=
  ∀ (p : ℕ) (t : ℝ), p < (chainModel J.whole).W.n → t ∈ Ioo (0 : ℝ) 1 →
    ¬ (chainModel J.whole).IsCut ztbi ztk → oK < oW J ztk →
    (∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oK < oW J ztej → oW J ztej < oW J ztk → EvBrk J e) →
    EvPos J S₂ Λ p t
variable {J}
variable {S₂ : Set (Set Point)}
/-- **Keys carrying only bracket chords keep the invariant.** -/
theorem evInv_mono {oK oK' : ℝ} {Λ : Set ztf}
    (h : EvInv J S₂ oK Λ) (hle : oK ≤ oK')
    (hbr : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oK < oW J ztej → oW J ztej ≤ oK' → EvBrk J e) :
    EvInv J S₂ oK' Λ := by
  intro p t hp ht hnc ho hb
  refine h p t hp ht hnc by_linarith fun e he q s hA h1 h2 => ?_
  grind

/-- **After a pocket key** every position is enclosed. -/
theorem evInv_pocket {e : Set Point} (he : e ∈ F₂plus J S₂)
    {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach (chainModel J.whole).W e pa ta)
    (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (hAo : (Lst J : ℝ) ≤ oW J ztbf) (hBo : oW J ztbd = 0) (Λ : Set ztf) :
    EvInv J S₂ (oW J ztbf) Λ :=
  fun _ _ _ _ _ ho _ => Or.inl ⟨e, he, pa, pb, ta, tb, hA, hB, hAB, hAo, ho, Or.inr hBo⟩

/-- `oW` is the offset from the base `gW`. -/
theorem oW_eq (x : ℝ) :
    oW J x = off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x := rfl
theorem Lst_eq : (Lst J : ℝ) = ((rL1 J + rL2 J : ℕ) : ℝ) := rfl

/-- **An enclosed position faces an unlabelled region.** -/
theorem not_rlabel_of_encl (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut ztbi ztk)
    (hE : EvEncl J S₂ ztxae) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) (hf : (chainModel J.whole).Faces p t G)
    (V : Set Point) : ¬ RLabel J S₂ G V := by
  obtain ⟨e, he, pa, pb, ta, tb, hA, hB, hAB, hAo, ho, hBo⟩ := hE
  rcases hBo with hBo | hBo
  · exact no_label_of_bracket J hP hS₂ hS₂f hG he hA hB hAB hAo (hAo.trans (ho.trans hBo).le) hp ht hnc hf
      (Or.inl ⟨ho, hBo⟩) V
  · exact no_label_of_pocket J hP hS₂ hS₂f hG he hA hB hAB hAo hBo hp ht hnc hf ho V

/-- **A cut-free stretch just after a position** facing the region faced just after it. -/
theorem after_pos_exists (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) {G : Set Point}
    (hW : AfterFaces ztbm p t G) :
    ∃ s, 0 < s ∧ t + s < 1 ∧ (chainModel J.whole).Faces p ztuf G ∧
      ¬ (chainModel J.whole).IsCut ztbi ztxaf ∧
      oW J ztxaf = oW J ztk + s ∧
      ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x → x < (chainModel J.whole).W.n →
        ¬ ztbalf := by
  zuv
  zust
  obtain ⟨δ, hδ, hfac⟩ := hW
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hM hC.hF hC.hfin ztdj)
  zucmv
  set s := min ztbng ztca / 2 with hs
  have hm : 0 < min ztbng ztca := lt_min ztkam by_linarith
  have h1 := min_le_left ztbng ztca
  have h2 := min_le_right ztbng ztca
  zubcm

  zudpf
  have hoff : oW J ztxaf = oW J ztk + s :=
    off_add_small hC.hg hp ht0 hs0.le by_linarith
  refine ⟨s, hs0, by_linarith, hfac s hs0 by_linarith by_linarith, ?_, hoff, ?_⟩
  · have := hsub ztdxm
    grind
  · rintro x hx hx0 hxn ⟨hlo, hhi⟩
    rw [hoff] at hhi
    have hu : 0 ≤ oW J x - oW J ztk := by_linarith
    have hx' := eq_of_off_small hC.hg hp ht0 hu by_linarith hx0 hxn
      (show oW J x = oW J ztk + (oW J x - oW J ztk) by ring)
    have := hsub ⟨show 0 < oW J x - oW J ztk by linarith,
      show oW J x - oW J ztk < δ₁ by linarith⟩
    grind

/-- **The label facts of the event log from the invariant.** -/
theorem labIn_of_evInv (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {Λ : Set ztf} {p : ℕ}
    {t : ℝ} (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h : EvInv J S₂ ztxae Λ) : LabIn J S₂ p t Λ := by
  intro G hG hW V hV hR
  obtain ⟨s, hs0, hs1, hf, hnc, hoff, hgap⟩ := after_pos_exists hP hS₂ hS₂f hp ht0 ht1 hW
  have hpos := h p ztuf hp ztomr hnc by_simp_all
    (fun e he q s' hA h1 h2 => by
      obtain ⟨k0, k1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
      exact absurd ztwo (hgap _ ⟨e, he, q, s', hA, rfl⟩ k0 k1))
  zukma
  · exact absurd hR (not_rlabel_of_encl hP hS₂ hS₂f hp ztomr hnc hE hG hf V)
  · obtain ⟨L, hL, -, hv⟩ := hval G hG hf
    rcases hv.1 V hV hR with rfl | hg
    · omega
    simp_all
end EvInv
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc SideSectorIn)
open WalkEmbed
namespace Sweep
section Comp
variable {M : Model}

/-- **A region on a side of a chord lies in the component of the chord's attachment** (with
respect to the split by another chord `c`): if `Z ∈ F`, `Z ≠ c`, is attached at `P` and the small
left sector at `P` lies in the component `K` of `D \ c`, every region on a side of `Z` meets `K`. -/
theorem side_meets_comp (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {c Z : Set Point}
    (hZ : Z ∈ F) {pz : ℕ} {tz : ℝ} (hP : SideAttach M.W Z pz tz) {k : Point}
    (hsec : SideSectorIn M.W ztyqh pz tz)
    (hcl : IsClosed c) {ρ : ℝ} {R : Set Point} (hRs : SideOf M ρ Z R) :
    (R ∩ connectedComponentIn ztjq k).Nonempty := by
  obtain ⟨a, b, hab, hZab, -, hopen, -, -⟩ := hM.ends Z (hF hZ)
  have hPZ := hP
  rw [hZab] at hPZ
  obtain ⟨r, hr, hs⟩ := hsec
  obtain ⟨-, -, -, -, r', hr', hleft⟩ := hP
  -- an endpoint `e` of `Z` at `P` and the other endpoint `f`
  obtain ⟨e, f, hef, hZef, hPe, hopen'⟩ : ∃ e f : Point, e ≠ f ∧ Z = Chazelle.segment e f ∧
      sidePt M.W pz tz = e ∧ ∀ s ∈ Ioo (0 : ℝ) 1, Geometry.lerp e f s ∈ M.D := by
    rcases hM.attach_endpoint hopen hPZ with h | h
    · grind
    · refine ⟨b, a, hab.symm, by rw [hZab]; exact Chazelle.Jordan.segment_comm a b, h, fun s hs => ?_⟩
      zumlg
      simp_all
  have hcont : Tendsto (fun s : ℝ => Geometry.lerp e f s) (𝓝[>] (0 : ℝ)) (𝓝 e) := by
    have := (Geometry.continuous_lerp e f).tendsto 0
    zugcb
    zuhv
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), Geometry.lerp e f s ∈ ball e zteuc :=
    hcont (ball_mem_nhds e by_grind)
  obtain ⟨s, hsb, hs1⟩ := (hball.and ztxve).exists
  set z := Geometry.lerp e f s with hz
  have hzZ : z ∈ Z := by
    rw [hZef]; exact Geometry.mem_segment_iff_lerp.2 by_grind
  zukhj
  have hze : z ≠ e := by
    zuq
    have hzD' := hzD
    zvmwc at hzD'
    exact hM.trace pz (by have := hPZ.1; omega) tz hPZ.2.1 hPZ.2.2.1.le by_grind
  have hdist : dist z e < min r r' := hsb
  have hzL : Chazelle.Chain.sideLeft M.W pz tz z :=
    by grind
  have hzK : z ∈ connectedComponentIn _ k :=
    hs z (by rw [mem_ball, hPe]; grind) hzL
  -- the component is open, so the points just beside `z` are in it
  have hKo : IsOpen (connectedComponentIn _ k) :=
    (hM.isOpen.sdiff hcl).connectedComponentIn
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztdis : Point) ∈ connectedComponentIn ztjq k := by
    have hc : Continuous (fun δ : ℝ => (ztdis : Point)) := by fun_prop
    have h0 : ((z.1, z.2 + ρ * 0) : Point) = z := by_simp
    have := hc.tendsto 0
    zubuv
    exact (this.mono_left nhdsWithin_le_nhds) (hKo.mem_nhds hzK)
  obtain ⟨δ, h1, h2⟩ := ((hRs z hzZ hzD).and hev).exists
  exact ⟨_, h1, h2⟩

/-- **A region on a side of a chord attached in one arc of `c` is not faced in the other arc.** -/
theorem side_comp (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {c Z : Set Point}
    (hc : c ∈ F) (hZ : Z ∈ F) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {pz : ℕ} {tz : ℝ}
    (hP : SideAttach M.W Z pz tz) (hPin : sideInArc ztbd ztbf zthe) {ρ : ℝ}
    {R : Set Point} (hR : R ∈ M.regions F) (hRs : SideOf M ρ Z R) {py : ℕ} {ty : ℝ}
    (hpy : py < M.W.n) (hty : ty ∈ Ioo (0 : ℝ) 1) (hyin : sideInArc ztbf ztbd ztdhy)
    (hfy : M.Faces py ty R) : False := by
  obtain ⟨K₁, K₂, hne, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, h₁, h₂⟩ := hM.split ztlz hA hB hAB
  have hR1 := hM.region_subset_of_sector hc hR hpy hty hfy (h₁ py hpy ty hty.1.le hty.2 hyin)
  have hcl : IsClosed c := by
    obtain ⟨a, b, -, hcab, -⟩ := hM.ends c ztlz
    zvmyh; exact Chazelle.Geometry.isClosed_segment a b
  obtain ⟨w, hwR, hw2⟩ := side_meets_comp hM hF hZ hP (h₂ pz hP.1 tz hP.2.1 hP.2.2.1 hPin) hcl hRs
  have hw1 := hR1 hwR
  exact hne ((connectedComponentIn_eq hw1).trans (connectedComponentIn_eq hw2).symm)
end Comp

/-! ## The junction: offsets -/
section Junction
variable {J : Merge.Junction}

/-- **`side_comp` in offsets** (from the base `gW`): `c` attached at offsets `oA < oB`, `Z ≠ c`
attached at an offset outside `[oA, oB]`; a region on a side of `Z` is not faced at a position with
offset in `(oA, oB)`. -/
theorem side_comp_off (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c Z : Set Point}
    (hc : c ∈ F₂plus J S₂) (hZ : Z ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W c pa ta) (hB : SideAttach (chainModel J.whole).W c pb tb)
    (hAB : oW J ztbf < oW J ztbd) {pz : ℕ} {tz : ℝ}
    (hPz : SideAttach (chainModel J.whole).W Z pz tz)
    (hPout : oW J zthe < oW J ztbf ∨ oW J ztbd < oW J zthe) {ρ : ℝ}
    {R : Set Point} (hR : R ∈ (chainModel J.whole).regions ztbi)
    (hRs : SideOf ztbm ρ Z R) {py : ℕ} {ty : ℝ}
    (hpy : py < (chainModel J.whole).W.n) (hty : ty ∈ Ioo (0 : ℝ) 1)
    (hy1 : oW J ztbf < oW J ztdhy) (hy2 : oW J ztdhy < oW J ztbd)
    (hfy : (chainModel J.whole).Faces py ty R) : False := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  zucu

  obtain ⟨z0, z1⟩ := Corr.key_mem hPz.1 hPz.2.1 hPz.2.2.1
  obtain ⟨y0, y1⟩ := Corr.key_mem hpy hty.1.le hty.2
  have hAB' : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb := by
    zuq
    zueur

  refine side_comp hC.hM hC.hF hc hZ hA hB hAB' hPz
    ((sideInArc_rev_iff_off hg0 hgn a0 a1 b0 b1 z0 z1 hAB).2 hPout) hR hRs hpy hty
    ((sideInArc_iff_off hg0 hgn a0 a1 b0 b1 y0 y1 hAB).2 ⟨hy1, hy2⟩) hfy

/-- Two attachments of a chord with distinct offsets have distinct points. -/
theorem pt_ne_of_off_ne (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c : Set Point}
    (hc : c ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W c pa ta) (hB : SideAttach (chainModel J.whole).W c pb tb)
    (hne : oW J ztbf ≠ oW J ztbd) :
    sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb := by
  zuv
  zuq
  zueur

/-- **Regions between two non-enclosed positions** (`GL`): two non-cut positions on the walk, not
enclosed, with only bracket chords attached at offsets strictly between them, face the same
region. -/
theorem evGL (hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {p p' : ℕ} {t t' : ℝ} (hp : p < (chainModel J.whole).W.n)
    (hp' : p' < (chainModel J.whole).W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut ztbi ztk)
    (hnc' : ¬ (chainModel J.whole).IsCut ztbi ztjg)
    (hlt : oW J ztk < oW J ztjg) (hE : ¬ EvEncl J S₂ ztxae)
    (hE' : ¬ EvEncl J S₂ (oW J ztjg))
    (hbr : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oW J ztk < oW J ztej → oW J ztej < oW J ztjg → EvBrk J e)
    {G G' : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hG' : G' ∈ (chainModel J.whole).regions ztbi)
    (hf : (chainModel J.whole).Faces p t G) (hf' : (chainModel J.whole).Faces p' t' G') :
    G = G' := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  refine (hC.hM.eq_iff_not_separates hC.hF hC.hfin hG hG' hp hp' ht ht' hnc hnc' hf hf').2
    fun c hc ⟨pa, pb, ta, tb, hA, hB, hAB, hsep⟩ => ?_
  zucu

  zubhm
  zufzh
  have hk := WalkAx.key_ne_of_pt_ne hA hB hAB
  have hxy : ztkzg := by
    grind
  have hxa := fun h => hnc ztexy
  have hxb := fun h => hnc ztkjo
  have hya := fun h => hnc' ztexy
  have hyb := fun h => hnc' ztkjo
  have hs := (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hk hxy hxa hxb hya hyb).1 hsep
  have hne : ∀ {u w : ℝ}, 0 ≤ u → u < (chainModel J.whole).W.n → 0 ≤ w →
      w < (chainModel J.whole).W.n → u ≠ w → oW J u ≠ oW J w :=
    fun hu hun hw hwn huw h => huw (off_inj hg0 hgn hu hun hw hwn h)
  have hoxa := hne x0 x1 a0 a1 hxa
  have hoxb := hne x0 x1 b0 b1 hxb
  have hoya := hne y0 y1 a0 a1 hya
  have hoyb := hne y0 y1 b0 b1 hyb
  -- one attachment strictly inside, the other outside
  have key : ∀ {qa qb : ℕ} {sa sb : ℝ}, SideAttach (chainModel J.whole).W c qa sa →
      SideAttach (chainModel J.whole).W c qb sb →
      sidePt (chainModel J.whole).W qa sa ≠ sidePt (chainModel J.whole).W qb sb →
      oW J ztk < oW J zteuu → oW J zteuu < oW J ztjg →
      oW J ztbjt ≠ oW J ztk → oW J ztbjt ≠ oW J ztjg →
      ¬ (oW J ztk < oW J ztbjt ∧ oW J ztbjt < oW J ztjg) → False := by
    intro qa qb sa sb hQA hQB hQAB h1 h2 h3 h4 hout
    have hbrk := hbr c hc qa sa hQA h1 h2
    rcases lt_or_gt_of_ne h4 with h5 | h5
    · rcases lt_or_gt_of_ne h3 with h6 | h6
      · -- the other end before `x`: `x` is enclosed
        exact hE ⟨c, hc, qb, qa, sb, sa, hQB, hQA, hQAB.symm, hbrk qb sb hQB, h6, Or.inl h1⟩
      grind
    · -- the other end after `y`: `y` is enclosed
      exact hE' ⟨c, hc, qa, qb, sa, sb, hQA, hQB, hQAB, hbrk qa sa hQA, h2, Or.inl h5⟩
  unfold Btw at hs
  by_cases ha : oW J ztk < oW J ztbf ∧ oW J ztbf < oW J ztjg
  · have hnb : ¬ ztxle := by
      zuhgn
      have := hs.1 ztbbu
      exact this ztvby
    exact key hA hB hAB ha.1 ha.2 hoxb.symm hoyb.symm hnb
  · have hb : oW J ztk < oW J ztbd ∧ oW J ztbd < oW J ztjg := by
      zuldq
      have h1 : ¬ ((oW J ztk < oW J ztbf ∧ oW J ztbf < oW J ztjg) ∨
          (oW J ztjg < oW J ztbf ∧ oW J ztbf < oW J ztk)) := by
        zunp
        · grind
        grind
      have h2 : ¬ (ztxle ∨
          (oW J ztjg < oW J ztbd ∧ oW J ztbd < oW J ztk)) := by
        zunp
        · grind
        grind
      exact h1 (hs.2 h2)
    exact key hB hA hAB.symm hb.1 hb.2 hoxa.symm hoya.symm ha
end Junction
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc SideSectorIn)
open WalkEmbed
namespace Sweep
def DirAt (W : Polygon) (e : Set Point) (p : ℕ) (t d : ℝ) : Prop :=
  (d = 1 ∧ ∀ z ∈ e, (sidePt W p t).1 ≤ z.1) ∨ (d = -1 ∧ ∀ z ∈ e, z.1 ≤ (sidePt W p t).1)
theorem DirAt.cases {W : Polygon} {e : Set Point} {p : ℕ} {t d : ℝ} (h : DirAt W e p t d) :
    d = 1 ∨ d = -1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · simp_all
  simp_all
section Key
variable {M : Model}

/-- Every attached chord leaves its position in some direction. -/
theorem dirAt_exists (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) : ∃ d, DirAt M.W c p t d := by
  rcases hM.attach_dir hc hA with h | h
  · tauto
  · exact ⟨-1, Or.inr by_grind⟩

/-- **The two sides of a chord are distinct regions.** -/
theorem side_regions_ne (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t) {U V : Set Point}
    (hU : U ∈ M.regions F) (hV : V ∈ M.regions F) (hSU : SideOf M 1 c U)
    (hSV : SideOf M (-1) c V) : U ≠ V := by
  obtain ⟨U', V', hU', hV', hne, hside, -⟩ := chordSides_of_system ztbip hc
  obtain ⟨z, hz, hzD⟩ := exists_mem_dom hM ztlz hA
  have hS1 : SideOf M 1 c U' := fun z hz hzD => by_simp_all
  have hS2 : SideOf M (-1) c V' := fun z hz hzD => (hside z hz hzD).mono fun δ h => by
    simpa [sub_eq_add_neg] using h.2
  rw [sideOf_eq hU hU' hSU hS1 hz hzD, sideOf_eq hV hV' hSV hS2 hz hzD]
  omega

/-- **The local structure at a key.** -/
theorem keyStruct {Q : Polygon} {F : Set ztf} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) :
    ∃ (X Y : Set Point) (dX dY : ℝ), X ∈ F ∧ Y ∈ F ∧ SideAttach M.W X p t ∧
      SideAttach M.W Y p t ∧ DirAt M.W X p t dX ∧ DirAt M.W Y p t dY ∧
      (∀ c ∈ F, SideAttach M.W c p t → c = X ∨ c = Y) ∧
      (∀ R ∈ M.regions F, AfterFaces M p t R → SideOf M (-dY) Y R) ∧
      (∀ R ∈ M.regions F, BeforeFaces M p t R → SideOf M dX X R) ∧
      (X ≠ Y → ∀ R ∈ M.regions F, (SideOf M dY Y R ↔ SideOf M (-dX) X R)) ∧
      (X = Y → dX = dY) := by
  zubm
  zuglo
  by_cases htie : ∃ e' ∈ F, e' ≠ e ∧ SideAttach M.W e' p t
  · zufiy
    -- the east chord and the west chord
    obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW, hnew⟩ : ∃ ce cw : Set Point, ce ∈ F ∧ cw ∈ F ∧
        SideAttach M.W ce p t ∧ SideAttach M.W cw p t ∧ zticb ∧
        zticc ∧ cw ≠ ce := by
      rcases hM.tie_pair hF he he' hne.symm hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · grind
      grind
    obtain ⟨-, hhor, hall⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
    have hT := fun {G} (hG : G ∈ M.regions F) => after_side_tie hGM hFam hce hcw hnew hAe hAw hE hW hG
    have mid := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ ce U) =>
      (faced_or_middle hGM hFam hce hAe hρ hU hS ztbaev).2 cw hcw hnew hAw
    have mid' := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ cw U) =>
      (faced_or_middle hGM hFam hcw hAw hρ hU hS (Or.inr ztopj)).2 ce hce hnew.symm hAe
    rcases lt_or_gt_of_ne hhor with hdn | hup
    · -- descending: `Y = ce`, `X = cw`
      refine ⟨cw, ce, -1, 1, hcw, hce, hAw, hAe, Or.inr ztopj, Or.inl ztkmt,
        fun c hc hc' => (hall c hc hc').symm, fun R hR hR' => (hT hR).1 hdn hR',
        fun R hR hR' => (hT hR).2.1 hdn hR', fun _ R hR => ?_, fun h => by_simp_all⟩
      zuduy
      exact ⟨fun h => ((mid ztp hR h).2.2.1 hdn).1 rfl,
        fun h => ((mid' ztp hR h).2.2.1 hdn).1 rfl⟩
    · -- ascending: `Y = cw`, `X = ce`
      refine ⟨ce, cw, 1, -1, hce, hcw, hAe, hAw, Or.inl ztkmt, Or.inr ztopj,
        by omega, fun R hR hR' => by rw [neg_neg]; exact (hT hR).2.2.1 hup hR',
        fun R hR hR' => (hT hR).2.2.2 hup hR', fun _ R hR => ?_, fun h => by_simp_all⟩
      exact ⟨fun h => ((mid' ztbt hR h).2.2.2 hup).1 rfl,
        fun h => ((mid ztbt hR h).2.2.2 hup).1 rfl⟩
  · zucyh
    have huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e := by
      grind
    obtain ⟨d, hd⟩ := dirAt_exists hM ztesz hA
    exact ⟨e, e, d, d, he, he, hA, hA, hd, hd, by_simp_all,
      fun R hR hR' => after_side hGM hFam he hA huniq hd hR hR',
      fun R hR hR' => before_side hGM hFam he hA huniq hd hR hR', by_simp_all,
      by simp_all⟩

/-- **A region is not faced in both arcs of a chord.** -/
theorem faced_both_arcs (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {c : Set Point}
    (hc : c ∈ F) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {R : Set Point}
    (hR : R ∈ M.regions F) {p q : ℕ} {t s : ℝ} (hp : p < M.W.n) (hq : q < M.W.n)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (h1 : sideInArc ztbf ztbd ztk) (h2 : sideInArc ztbd ztbf ztej)
    (hf1 : M.Faces p t R) (hf2 : M.Faces q s R) : False := by
  obtain ⟨K₁, K₂, hne, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, k₁, k₂⟩ := hM.split ztlz hA hB hAB
  have hR1 := hM.region_subset_of_sector hc hR hp ht hf1 (k₁ p hp t ht.1.le ht.2 h1)
  have hR2 := hM.region_subset_of_sector hc hR hq hs hf2 (k₂ q hq s hs.1.le hs.2 h2)
  obtain ⟨w, hw⟩ := Chazelle.Chain.regionsIn_nonempty hR
  exact hne ((connectedComponentIn_eq (hR1 hw)).trans (connectedComponentIn_eq (hR2 hw)).symm)
end Key
section Junction
variable {J : Merge.Junction}

/-- **`faced_both_arcs` in offsets.** -/
theorem faced_both_off (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c : Set Point}
    (hc : c ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W c pa ta) (hB : SideAttach (chainModel J.whole).W c pb tb)
    (hAB : oW J ztbf < oW J ztbd) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions ztbi) {p q : ℕ} {t s : ℝ}
    (hp : p < (chainModel J.whole).W.n) (hq : q < (chainModel J.whole).W.n)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (h1 : oW J ztbf < oW J ztk) (h1' : oW J ztk < oW J ztbd)
    (h2 : oW J ztej < oW J ztbf ∨ oW J ztbd < oW J ztej)
    (hf1 : (chainModel J.whole).Faces p t R) (hf2 : (chainModel J.whole).Faces q s R) : False := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  zucu

  zubhm
  obtain ⟨y0, y1⟩ := Corr.key_mem hq hs.1.le hs.2
  exact faced_both_arcs hC.hM hC.hF hc hA hB (pt_ne_of_off_ne hP hS₂ hS₂f hc hA hB hAB.ne) hR hp hq
    ht hs ((sideInArc_iff_off hg0 hgn a0 a1 b0 b1 x0 x1 hAB).2 ⟨h1, h1'⟩)
    ((sideInArc_rev_iff_off hg0 hgn a0 a1 b0 b1 y0 y1 hAB).2 h2) hf1 hf2

/-- **A region faced just before a key of positive offset**, with non-cut positions facing it
arbitrarily close before the key and no cut in between. -/
theorem before_region_exists' (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hpos : 0 < oW J ztk)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ (chainModel J.whole).regions ztbi, BeforeFaces ztbm p t R ∧
      ∃ (q : ℕ) (u : ℝ), q < (chainModel J.whole).W.n ∧ u ∈ Ioo (0 : ℝ) 1 ∧
        ¬ (chainModel J.whole).IsCut ztbi ztzq ∧ (chainModel J.whole).Faces q u R ∧
        oW J ztk - ε < oW J ztzq ∧ oW J ztzq < oW J ztk ∧
        ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x →
          x < (chainModel J.whole).W.n → ¬ ztxlg := by
  zuv
  zust
  zudbo
  have hg := hC.hg
  zued
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < n := by exact_mod_cast hg
  zucmj
  zufyt
  -- the key just before `(p, t)`: `X - s`
  set X : ℝ := if 0 < t ∨ 1 ≤ p then (p : ℝ) + t else (n : ℝ) with hX
  -- the position at distance `s` before the key
  have hw : ∀ s, 0 < s → s < 1 → (0 < t → s < t) →
      ∃ (q : ℕ) (u : ℝ), q < n ∧ u ∈ Ioo (0 : ℝ) 1 ∧ (q : ℝ) + u = X - s ∧
        oW J ztzq = oW J ztk - s := by
    intro s hs0 hs1 hst
    zudsi
    · refine ⟨p, t - s, hp, by_grind, ?_, ?_⟩
      · grind
      · exact off_before_edge hg hp hs0 (hst htp) ht1
    · refine ⟨ztzp % n, 1 - s, Nat.mod_lt _ hn0, by_simp_all, ?_,
        off_before_vertex hg hp hs0 hs1 hpos⟩
      zucyn
      · simp_all
      · rw [hX, ite_eq_left by_omega, show ztzp % n = p - 1 by
          rw [show p + n - 1 = ztoq + n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega], Nat.cast_sub by_omega]
        simp
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_before hM hC.hF hC.hfin X)
  have hδ₀' := hδ₀
  set δ := min (min δ₀ ε) (min 1 ztmlm) with hδ
  have hT : 0 < ztmlm := by_grind
  have hδ0 : ztcfy := lt_min by_grind by_grind
  have hδ1 : δ ≤ δ₀ := le_trans ztff by_grind
  have hδ2 : δ ≤ ε := le_trans ztff by_grind
  have hδ3 : δ ≤ 1 := by_grind
  have hδ4 : 0 < t → δ ≤ t := fun h => by
    grind
  have hnc : ∀ s, 0 < s → s < δ → ∀ (q : ℕ) (u : ℝ), (q : ℝ) + u = X - s →
      ¬ (chainModel J.whole).IsCut ztbi ztzq := by
    intro s hs0 hs1 q u hqu
    have := hsub ⟨hs0, by_grind⟩
    grind
  -- the position at `δ / 2`
  obtain ⟨q, u, hq, hu, hqu, hoff⟩ := hw ztbfe by_linarith by_linarith
    ztbay
  have hnc0 := hnc _ by_linarith by_linarith q u hqu
  obtain ⟨R, hR, hfR⟩ := hM.exists_faces_of_not_cut hC.hF hC.hfin hq hu hnc0
  have hgap : ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x →
      x < n → ¬ ztxlg := by
    rintro x hx hx0 hxn ⟨h1, h2⟩
    set s' := oW J ztk - oW J x with hs'
    obtain ⟨q', u', hq', hu', hqu', hoff'⟩ := hw s' by_linarith by_linarith
      ztbay
    have hk := Corr.key_mem hq' hu'.1.le hu'.2
    have hxeq :=
      off_inj hg0 hgn hx0 hxn hk.1 hk.2 (by rw [← oW_eq, ← oW_eq, hoff', hs']; ring)
    exact hnc s' by_linarith by_linarith q' u' hqu' by_grind
  refine ⟨R, hR, before_faces_of_gap hM hC.hF hC.hfin hg0 hgn hR hq hu hnc0 hfR hp ht0 ht1
    (by rw [← oW_eq, ← oW_eq, hoff]; linarith) hgap, q, u, hq, hu, hnc0, hfR,
    by grind, by_grind, hgap⟩
end Junction
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open WalkEmbed
namespace Sweep
section Tie
variable {J : Merge.Junction}

/-- Every point of an admissible chord of `C` attached at a position has the height of the
position's point. -/
theorem attach_snd_eq (hP : J.P.Simple) {f : Set Point} (hf : f ∈ Merge.augChords J.whole)
    {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W f p t) {z : Point} (hz : z ∈ f) :
    z.2 = (sidePt (chainModel J.whole).W p t).2 := by
  zugb
  obtain ⟨a, b, -, hfab, hy, -⟩ := hM.ends f hf
  have key : ∀ w ∈ f, w.2 = a.2 := by
    zucdk
    rw [hfab] at hw
    obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hw
    simp_all
  rw [key z hz, key _ hA.2.2.2.1]

/-- **The point of a tie off the open right stretch** is in the domain of `C₂` or is the shared
vertex. -/
theorem tie_dom (hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {e e' : Set Point} (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂)
    (hne : e ≠ e') {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W e p t)
    (hA' : SideAttach (chainModel J.whole).W e' p t)
    (hout : ¬ (0 < oW J ztk ∧ oW J ztk < Lst J)) :
    sidePt (chainModel J.whole).W p t ∈ J.right.dom ∨
      sidePt (chainModel J.whole).W p t = J.shared := by
  zuv
  zust
  set x := sidePt (chainModel J.whole).W p t with hx
  have hpt : ∀ {f : Set Point}, f ∈ F₂plus J S₂ → SideAttach (chainModel J.whole).W f p t →
      ∃ z ∈ f, z ∈ J.whole.dom ∧ z.2 = x.2 := by
    intro f hf hAf
    obtain ⟨z, hz, hzD⟩ := exists_mem_dom hM (hC.hF hf) hAf
    exact ⟨z, hz, hzD, attach_snd_eq hP ztleo hAf hz⟩
  -- `x` lies strictly inside the box
  have hbox : x ∈ Chain.box J.whole.radius := by
    rcases hM.tie_pair hC.hF he he' hne hA hA' with ⟨hE, hW⟩ | ⟨hW, hE⟩
    · obtain ⟨zE, hzE, hzED, hzE2⟩ := hpt he hA
      obtain ⟨zW, hzW, hzWD, -⟩ := hpt he' hA'
      zucge

      · zuicc
      · zuicb
    · obtain ⟨zE, hzE, hzED, hzE2⟩ := hpt he' hA'
      obtain ⟨zW, hzW, hzWD, -⟩ := hpt he hA
      zucge

      · zuicc
      · zuicb
  have hR : ztpkl := FuseMath.radius_of_P J (C' := J.right) rfl
  have hy : x.2 ≤ J.right.top.2 := F₂plus_snd_le J hS₂ he hA.2.2.2.1
  by_cases hxd : x ∈ J.right.dom
  · simp_all
  · right
    rcases (Merge.not_mem_dom_iff J.right hy).1 hxd with h | h
    · simp_all
    · by_contra hv
      exact hout (off_right_pt J hP hS₂ hS₂f hA.1 hA.2.1 hA.2.2.1 h hv)

/-- **A chord of `S₂` containing two distinct points of a chord is determined.** -/
theorem parent_unique {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c c' : Set Point} (hc : c ∈ S₂) (hc' : c' ∈ S₂) {u w : Point} (huw : u ≠ w) (hu : u ∈ c)
    (hw : w ∈ c) (hu' : u ∈ c') (hw' : w ∈ c') : c = c' := by
  obtain ⟨y, a, b, hH, -, rfl, -, -⟩ := Merge.augChords_spec ztbac
  obtain ⟨y', a', b', hH', -, rfl, -, -⟩ := Merge.augChords_spec zthxv
  have hx : u.1 ≠ w.1 := fun h => huw (Prod.ext h (hu.1.trans hw.1.symm))
  have hconv : ∀ {y a b : ℝ}, u ∈ Visibility.hseg y a b → w ∈ Visibility.hseg y a b →
      (ztfly : Point) ∈ Visibility.hseg y a b ∧
        (ztfly : Point) ≠ ztdv ∧ (ztfly : Point) ≠ ztdy := by
    intro y a b hu hw
    obtain ⟨-, h1, h2⟩ := hu
    obtain ⟨-, h3, h4⟩ := hw
    refine ⟨ztgpk, fun h => ?_, fun h => ?_⟩
    · grind
    grind
  have hyy : ztsne := hu.1.symm.trans hu'.1
  zulau
  obtain ⟨hm, hma, hmb⟩ := hconv hu hw
  obtain ⟨hm', -, -⟩ := hconv hu' hw'
  rcases Chain.hchordIn_inter hH hH' hm hm' with ⟨-, rfl, rfl⟩ | ⟨h1, -⟩
  · rfl
  simp_all

/-- **At most two pieces of a chord of `S₂`**: three chords of `F₂⁺` inside `c ∈ S₂`, attached at
points of the domain of `C₂`, are not pairwise distinct. -/
theorem pieces_le_two (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₂) {e₁ e₂ e₃ : Set Point}
    (he₁ : e₁ ∈ F₂plus J S₂) (he₂ : e₂ ∈ F₂plus J S₂) (he₃ : e₃ ∈ F₂plus J S₂) (h₁ : e₁ ⊆ c)
    (h₂ : e₂ ⊆ c) (h₃ : e₃ ⊆ c) {p₁ p₂ p₃ : ℕ} {t₁ t₂ t₃ : ℝ}
    (hA₁ : SideAttach (chainModel J.whole).W e₁ p₁ t₁)
    (hA₂ : SideAttach (chainModel J.whole).W e₂ p₂ t₂)
    (hA₃ : SideAttach (chainModel J.whole).W e₃ p₃ t₃)
    (hD₁ : sidePt (chainModel J.whole).W p₁ t₁ ∈ J.right.dom)
    (hD₂ : sidePt (chainModel J.whole).W p₂ t₂ ∈ J.right.dom)
    (hD₃ : sidePt (chainModel J.whole).W p₃ t₃ ∈ J.right.dom) :
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃ := by
  rcases piece_of_parent J hP hS₂ he₁ hc h₁ hA₁ hD₁ with ⟨-, k₁⟩ | ⟨-, k₁⟩ <;>
    rcases piece_of_parent J hP hS₂ he₂ hc h₂ hA₂ hD₂ with ⟨-, k₂⟩ | ⟨-, k₂⟩ <;>
    rcases piece_of_parent J hP hS₂ he₃ hc h₃ hA₃ hD₃ with ⟨-, k₃⟩ | ⟨-, k₃⟩
  all_goals first
    | exact Or.inl (k₁.trans k₂.symm)
    | exact Or.inr (Or.inl (k₁.trans k₃.symm))
    | exact Or.inr (Or.inr (k₂.trans k₃.symm))
end Tie
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open WalkEmbed
namespace Sweep
section Anchor
variable (J : Merge.Junction)

/-- **Side labels**: every region on a side of `Z` has a valid label set `Λ`. -/
def EvSideLab (S₂ : Set ztf) (Λ : Set ztf) (Z : Set Point) : Prop :=
  ∀ G ∈ (chainModel J.whole).regions ztbi, ∀ ρ : ℝ, ztbtc →
    SideOf ztbm ρ Z G → EvVal J S₂ Λ G

/-- **No tie at a copy of the shared vertex beyond the start.** -/
def NoTieV (S₂ : Set ztf) : Prop :=
  ∀ e ∈ F₂plus J S₂, ∀ e' ∈ F₂plus J S₂, e ≠ e' → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W e p t → SideAttach (chainModel J.whole).W e' p t →
    sidePt (chainModel J.whole).W p t = J.shared → (Lst J : ℝ) < oW J ztk → False
variable {J}

/-- Two positions with equal offsets are equal. -/
theorem pos_eq_of_oW (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p p' : ℕ} {t t' : ℝ}
    (hp : p < (chainModel J.whole).W.n) (hp' : p' < (chainModel J.whole).W.n) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (ht0' : 0 ≤ t') (ht1' : t' < 1) (h : oW J ztk = oW J ztjg) :
    p = p' ∧ t = t' := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  obtain ⟨a0, a1⟩ := Corr.key_mem hp ht0 ht1
  obtain ⟨b0, b1⟩ := Corr.key_mem hp' ht0' ht1'
  exact Chazelle.Chain.sideKey_inj ht0 ht1 ht0' ht1' (off_inj hg0 hgn a0 a1 b0 b1 h)

/-- **A cut-free stretch just after a position, of length below `ε`.** -/
theorem after_pos_eps (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) {G : Set Point}
    (hW : AfterFaces ztbm p t G) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ t + s < 1 ∧ (chainModel J.whole).Faces p ztuf G ∧
      ¬ (chainModel J.whole).IsCut ztbi ztxaf ∧
      oW J ztxaf = oW J ztk + s ∧
      ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x → x < (chainModel J.whole).W.n →
        ¬ ztbalf := by
  zugrb
  obtain ⟨s, hs0, hs1, hf, hnc, hoff, hgap⟩ := after_pos_exists hP hS₂ hS₂f hp ht0 ht1
    (G := G) ⟨min δ ε, lt_min hδ hε, fun s h0 h1 h2 => hW' s h0 (lt_of_lt_of_le h1
      ztff) h2⟩
  -- shrink to below `ε`: the positions of the stretch face the same region
  by_cases hsε : s < ε
  · grind
  · push Not at hsε
    zuv
    set s' := min ztkax s / 2 with hs'
    have hm : 0 < min ztkax s := lt_min (lt_min hδ hε) hs0
    have h1 := min_le_left ztkax s
    have h2 := min_le_right ztkax s
    have h3 := min_le_left δ ε
    have h4 := min_le_right δ ε
    have hs'0 : ztrzk := by_linarith
    have hoff' : oW J (p + ztubs) = oW J ztk + s' :=
      off_add_small hC.hg hp ht0 hs'0.le by_linarith
    refine ⟨s', hs'0, by_linarith, by_linarith, hW' s' hs'0 by_linarith by_linarith, ?_,
      hoff', ?_⟩
    · intro hcut
      obtain ⟨k0, k1⟩ := Corr.key_mem hp (show 0 ≤ t + s' by linarith) (show t + s' < 1 by linarith)
      grind
    grind

/-- **The direction of a chord at a position is unique.** -/
theorem dirAt_unique (hP : J.P.Simple) {e : Set Point} (he : e ∈ Merge.augChords J.whole)
    {p : ℕ} {t d d' : ℝ} (_hA : SideAttach (chainModel J.whole).W e p t)
    (h : DirAt (chainModel J.whole).W e p t d) (h' : DirAt (chainModel J.whole).W e p t d') :
    d = d' := by
  zugb
  obtain ⟨a, b, hab, heab, hy, -⟩ := hM.ends e he
  have ha : a ∈ e := by rw [heab]; exact Geometry.left_mem_segment _ _
  have hb : b ∈ e := by rw [heab]; exact Geometry.right_mem_segment _ _
  have hne : ztsdk := fun hx => hab (Prod.ext hx hy)
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rfl
  · grind
  · grind
  · rfl

/-- **A chord leaves its two attachments in opposite directions.** -/
theorem dirAt_other (hP : J.P.Simple) {e : Set Point} (he : e ∈ Merge.augChords J.whole)
    {pa pb : ℕ} {ta tb d : ℝ} (hA : SideAttach (chainModel J.whole).W e pa ta)
    (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (h : DirAt (chainModel J.whole).W e pa ta d) : DirAt (chainModel J.whole).W e pb tb (-d) := by
  zugb
  have hy : (sidePt (chainModel J.whole).W pa ta).2 = (sidePt (chainModel J.whole).W pb tb).2 :=
    (attach_snd_eq hP he hB hA.2.2.2.1)
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inr ⟨by_norm_num, dir_opposite hM he hA hB hAB h⟩
  · rcases hM.attach_dir he hB with h' | h'
    · exact Or.inl ⟨by_norm_num, h'⟩
    · exfalso
      have e1 := h' _ hA.2.2.2.1
      have e2 := h _ hB.2.2.2.1
      grind

/-- **The anchored chord is not strictly inside a bracket interval**: a chord `e ≠ Z` attached at
offsets `A < B` with `A < oK < B`, `Z` attached at `K` and at an offset below `A`, is impossible. -/
theorem anchor_not_inside (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {Z e : Set Point}
    (hZ : Z ∈ F₂plus J S₂) (he : e ∈ F₂plus J S₂) (hZe : Z ≠ e) {pK pz pa pb : ℕ}
    {tK tz ta tb : ℝ} (hZK : SideAttach (chainModel J.whole).W Z pK tK)
    (hZz : SideAttach (chainModel J.whole).W Z pz tz)
    (hA : SideAttach (chainModel J.whole).W e pa ta) (hB : SideAttach (chainModel J.whole).W e pb tb)
    (h1 : oW J ztbf < oW J ztkm) (h2 : oW J ztkm < oW J ztbd)
    (hz : oW J zthe < oW J ztbf) : False := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  have hAB := pt_ne_of_off_ne hP hS₂ hS₂f he hA hB (by linarith : oW J ztbf ≠ oW J ztbd)
  have := no_cross_off hC.hM hC.hF hC.hfin he hZ (Ne.symm hZe) hA hB hAB hZK hZz hg0 hgn
    (by zuobl; linarith) by_tauto
    by_tauto
  rw [← oW_eq, ← oW_eq, ← oW_eq] at this
  grind

/-- **A position just after a key with a closed block before it is not enclosed**: if the chords
attached at offsets in `[oK, oB]` other than `Z` have all their attachments there, `Z` is attached
at `K` and below `Lst`, and the position `y` (just after `B`, no cut between) precedes a
non-enclosed `x`, then `y` is not enclosed. -/
theorem noEncl_of_closed (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {Z : Set Point}
    (hZ : Z ∈ F₂plus J S₂) {pK pz : ℕ} {tK tz : ℝ}
    (hZK : SideAttach (chainModel J.whole).W Z pK tK)
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J zthe < Lst J)
    (hLst : (Lst J : ℝ) ≤ oW J ztkm) {oB : ℝ} (hKB : oW J ztkm ≤ oB)
    (hcl : ∀ e ∈ F₂plus J S₂, e ≠ Z → ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oW J ztkm ≤ oW J ztej → oW J ztej ≤ oB → ∀ (q' : ℕ) (s' : ℝ),
        SideAttach (chainModel J.whole).W e q' s' →
          oW J ztkm ≤ oW J ztkcv ∧ oW J ztkcv ≤ oB)
    {oy ox : ℝ} (hBy : oB < oy) (hyx : oy < ox) (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e q s → ¬ (oB < oW J ztej ∧ oW J ztej < oy))
    (hEx : ¬ EvEncl J S₂ ox) : ¬ EvEncl J S₂ oy := by
  rintro ⟨e, he, qa, qb, sa, sb, hA, hB, hAB, hLa, hay, hby⟩
  -- the first attachment is at most `oB`
  have hA' : oW J zteuu ≤ oB := by
    grind
  rcases hby with hby | hby
  · -- a bracket: the other end beyond `x` would enclose `x`
    have hbx : oW J ztbjt ≤ ox := by
      zubq

      exact hEx ⟨e, he, qa, qb, sa, sb, hA, hB, hAB, hLa, by_linarith, Or.inl h⟩
    by_cases heZ : e = Z
    · subst heZ
      -- `Z` has an attachment below `Lst`: it is `qa` or `qb`
      zuv
      rcases key_of_two hC.hM ztfhs hA hB hAB hZz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · linarith
      grind
    rcases lt_or_ge (oW J zteuu) ztyrk with h | h
    · exact anchor_not_inside hP hS₂ hS₂f hZ he (Ne.symm heZ) hZK hZz hA hB h by_linarith
        by_linarith
    grind
  · -- a pocket: `x` is enclosed too
    exact hEx ⟨e, he, qa, qb, sa, sb, hA, hB, hAB, hLa, by_linarith, Or.inr hby⟩

/-- **A chord nested in another**: a chord `e ≠ c` attached strictly between the two attachments
of `c` has all its attachments between them. -/
theorem closed_nested (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c e : Set Point}
    (hc : c ∈ F₂plus J S₂) (he : e ∈ F₂plus J S₂) (hce : c ≠ e) {pa pb q q' : ℕ}
    {ta tb s s' : ℝ} (hA : SideAttach (chainModel J.whole).W c pa ta)
    (hB : SideAttach (chainModel J.whole).W c pb tb) (hab : oW J ztbf < oW J ztbd)
    (hQ : SideAttach (chainModel J.whole).W e q s) (h1 : oW J ztbf < oW J ztej)
    (h2 : oW J ztej < oW J ztbd) (hQ' : SideAttach (chainModel J.whole).W e q' s') :
    oW J ztbf ≤ oW J ztkcv ∧ oW J ztkcv ≤ oW J ztbd := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  have hAB := pt_ne_of_off_ne hP hS₂ hS₂f hc hA hB hab.ne
  have := no_cross_off hC.hM hC.hF hC.hfin hc he hce hA hB hAB hQ hQ' hg0 hgn
    by_tauto by_tauto
    by_tauto
  tauto

/-- The keys of the attachments of a chord. -/
theorem attach_key_mem {e : Set Point} {q : ℕ} {s : ℝ}
    (hA : SideAttach (chainModel J.whole).W e q s) :
    0 ≤ (q : ℝ) + s ∧ (q : ℝ) + s < (chainModel J.whole).W.n :=
  Corr.key_mem hA.1 hA.2.1 hA.2.2.1
end Anchor
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed
namespace Sweep
theorem noTie_top (C : Chain) (hP : C.P.Simple) {F : Set ztf}
    (hF : F ⊆ (chainModel C).Adm) {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {k : ℕ}
    (hk : k = 6 ∨ k = 2 * C.m + 6) (hA : SideAttach (chainModel C).W c k 0)
    (hA' : SideAttach (chainModel C).W c' k 0) : c = c' := by
  zuct
  zucvy
  have hn : ztdh := cm_n C
  zubt
  have hRt := C.top_snd_lt_radius
  obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW⟩ : ∃ ce cw, ce ∈ F ∧ cw ∈ F ∧
      SideAttach (chainModel C).W ce k 0 ∧ SideAttach (chainModel C).W cw k 0 ∧
      (∀ z ∈ ce, (sidePt (chainModel C).W k 0).1 ≤ z.1) ∧
      (∀ z ∈ cw, z.1 ≤ (sidePt (chainModel C).W k 0).1) := by
    zuxr
    · grind
    grind
  zucbd
  have v6 : ztidg := by
    rw [cm_W, show (6 : ℕ) = 0 + 6 from rfl, C.sideWalk_vtx_tour _ by_omega, C.sideTour_zero]
  have v5 : ztidf := by_rfl
  have v7 : (chainModel C).W.vtx 7 = C.sideTour C.sideBeta 1 := by
    rw [cm_W, show (7 : ℕ) = 1 + 6 from rfl, C.sideWalk_vtx_tour _ by_omega]
  have v26 : ztyto := by
    rw [cm_W, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
  have v0 : ztide := by_rfl
  have v25 : (chainModel C).W.vtx ztptl = C.sideTour C.sideBeta ztdl := by
    rw [cm_W, show 2 * C.m + 5 = ztdl + 6 by omega, C.sideWalk_vtx_tour _ by_omega]
  zuvk
  · have e1 : (chainModel C).wb 6 = (chainModel C).W.vtx 7 := by
      rw [WalkAx.wb_eq, hn, Nat.mod_eq_of_lt by_omega]
    have e2 : (6 + (chainModel C).W.n - 1) % (chainModel C).W.n = 5 := by
      rw [hn, show 6 + ztz - 1 = 5 + ztz by omega, Nat.add_mod_right]
      simp
    zudfp
    have := ccw_up_right by_linarith ztiba hsW
    linarith
  · have e1 : (chainModel C).wb ztcc = (chainModel C).W.vtx 0 := by
      rw [WalkAx.wb_eq, hn, show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]
    have e2 : (ztcc + (chainModel C).W.n - 1) % (chainModel C).W.n = 2 * C.m + 5 := by
      rw [hn, show 2 * C.m + 6 + ztz - 1 = ztptl + ztz by omega,
        Nat.add_mod_right]
      simp
    zudfo
    have := ccw_up_left by_linarith ztiba hsE
    linarith

/-- The arithmetic of the positions of the shared vertex beyond the start. -/
theorem noTieV_arith {m m₁ m₂ b i : ℕ} (hm : m = m₁ + m₂) (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂)
    (hb : b ≤ 2 * m) (hi : i ≤ 2 * m) (hj : Chazelle.Chain.sideE m (ztbcn % ztdk) = m₁)
    (hL : (if 2 * m - ztcnx % ztdk < 2 * m₂ then 2 * m₂ + 7 else 2 * m₂) <
      (i + 6 + ztfk - (6 + ztcnx % ztdk)) % ztfk) :
    i = 0 ∨ i = 2 * m := by
  have hm0 : 0 < 2 * m := by_omega
  have d1 := Nat.div_add_mod ztbcn ztdk
  have d2 := Nat.div_add_mod ztcnx ztdk
  have l1 := Nat.mod_lt ztbcn hm0
  have l2 := Nat.mod_lt ztcnx hm0
  set q1 := ztbcn / ztdk
  set r1 := ztbcn % ztdk
  set q2 := ztcnx / ztdk
  set r2 := ztcnx % ztdk
  have hq1 : q1 ≤ 2 := by
    zuca
    have : 2 * m * 3 ≤ 2 * m * q1 := Nat.mul_le_mul_left _ hc
    omega
  have hq2 : q2 ≤ 1 := by
    zuca
    have : 2 * m * 2 ≤ 2 * m * q2 := Nat.mul_le_mul_left _ hc
    omega
  have d3 := Nat.div_add_mod ztxaa ztfk
  have l3 := Nat.mod_lt ztxaa (show 0 < 2 * m + 7 by omega)
  set q3 := ztxaa / ztfk
  set r3 := ztxaa % ztfk
  have hq3 : q3 ≤ 1 := by
    zuca
    have : ztfk * 2 ≤ ztfk * q3 := Nat.mul_le_mul_left _ hc
    omega
  unfold Chazelle.Chain.sideE at hj
  interval_cases q1 <;> interval_cases q2 <;> interval_cases q3 <;> split_ifs at hj hL <;> omega
variable {J : Merge.Junction}

/-- **No tie at a copy of the shared vertex beyond the start.** -/
theorem noTieV (hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    NoTieV J S₂ := by
  intro e he e' he' hne p t hA hA' hpt hL
  zuhwr
  have hm1 : ztsbu := by
    simp
  obtain ⟨rfl, i, hi, rfl, hidx⟩ := pos_eq_vertex J.whole hP J.whole.sideBeta hA.1 hA.2.1 hA.2.2.1 hm1
    (hpt.trans J.whole_vertex_m₁.symm)
  zuhf
  zunf
  have hp : i + 6 < (chainModel J.whole).W.n := hA.1
  zucwh
  have hoff : oW J ztieu = (dOf (chainModel J.whole).W.n ztead ztcy : ℝ) :=
    by rw [oW, off_key' hg hp le_rfl one_pos, add_zero]
  rw [hoff, Lst, rL1_add_rL2] at hL
  have hL' : rlen J < dOf (chainModel J.whole).W.n ztead ztcy := by_simp_all
  have hcase : i = 0 ∨ i = 2 * J.whole.m := by
    zuivf
    zudnh
    unfold rlen dOf gW tpos at hL'
    zvmxq at hL'
    rw [Chazelle.Chain.sideIdx_eq] at hidx
    exact noTieV_arith (m := J.whole.m) (m₁ := J.m₁) (m₂ := J.m₂) (b := bS J.whole) rfl h1 h2
      (bS_le J.whole) hi hidx hL'
  exact hne (noTie_top J.whole hP hF he he' by_omega hA hA')
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sidePrev sideNext sideLeftOf sideCcw sideCross
  sideDot)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Gen
variable (J : Merge.Junction)
variable (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ) {z : Point} {σ : ℝ}
/-- **Answer of a free direction, either side**: flag `1`, the first hit parameter `T` of `C`, and
the record data. -/
theorem seesInWhole_hit
    (hzq : (chainModel ztgi).pos Q ztpo = z) (hσq : dirOf q.2.2 = σ)
    (hzt : z.2 ≤ J.whole.top.2) {T : ℝ} (hhit : FreeAt J.whole z σ ∧ J.whole.hitParam z σ = T)
    {h pz pw lp rp : ℕ} (hR : RecordData J Q z σ T h pz pw lp rp) :
    SeesInWhole J Q i q (1, h, lp, rp) := by
  obtain ⟨hh, hz, hw, hAz, hAw, hl, hr⟩ := hR
  have hσ : ztim := hσq ▸ dirOf_cases q.2.2
  obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole hzt hσ hhit.1
  rw [hhit.2] at hT0
  obtain ⟨hs, hat⟩ := record_ok ztbm Q hσ hT0 hh hz hw hAz hAw ztuhr
  refine seesInWhole_of_answer J Q i q _ ?_ ?_ <;> zuogv
  · simp_all
  · zuhge
    refine ⟨?_, hat⟩
    zubqb
    unfold Merge.shoot
    simp_all

/-- **Answer of a direction that is not free, either side**: any flag other than `1`. -/
theorem seesInWhole_notFree'
    (hzq : (chainModel ztgi).pos Q ztpo = z) (hσq : dirOf q.2.2 = σ)
    (hnf : ¬ FreeAt J.whole z σ) (r : ℕ × ℕ × ℕ × ℕ) (hr : r.1 ≠ 1) : SeesInWhole J Q i q r := by
  refine seesInWhole_of_answer J Q i q r ?_ ?_ <;> zuogv
  · simp_all
  omega

/-! ## The candidate principle -/

/-- **The first hit of `C` above the top of `C₁`** is the first hit of `C₂`. -/
theorem whole_of_genuine_above₁ (hz₂ : z.2 ≤ J.right.top.2)
    (hz₁ : J.left.top.2 < z.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ₂ : ℝ}
    (h₂ : Genuine J.right z σ τ₂) : FreeAt J.whole z σ ∧ J.whole.hitParam z σ = τ₂ := by
  obtain ⟨hf₂, he₂⟩ := (genuine_iff J.right hz₂ hσ).1 h₂
  zujx
  · rw [freeAt_whole_iff J ztqqy]
    filter_upwards [hf₂] with t ht2
    refine ⟨J.right.dom_subset_box ht2, fun hmem => ?_, J.right.not_mem_set_of_mem_dom ht2⟩
    have := J.left.snd_le_top_of_mem_set hmem
    simp only [rayPt_snd] at this
    linarith
  · have e : J.whole.hitParam z σ = J.right.hitParam z σ := by
      rw [whole_hitParam_eq_min J ztqqy hσ,
        rayHit_eq_empty_of_above J.left hz₁, right_hitParam_eq J hz₂]
      refine min_eq_right ?_
      rw [← right_hitParam_eq J hz₂]
      exact Merge.rayHit_anti ztzi z hσ
    simp_all
end Gen

/-! ## Records from arrival positions -/
section Record

/-- **No horizontal ray in the left sector inside a horizontal edge.** -/
theorem not_sideLeft_horizontal {W : Polygon} {p : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hh : (W.vtx p).2 = (W.vtx ztwjb).2) (σ : ℝ) :
    ¬ sideLeft W p t ztxoo := by
  zumgt
  unfold sideLeft sideLeftOf at hs
  have hprev : sidePrev W p t = W.vtx p := by unfold sidePrev; grind
  rw [hprev] at hs
  set a := W.vtx p with ha
  set b := sideNext W p with hb
  have hb' : b = W.vtx ztwjb := rfl
  set v := sidePt W p t with hv
  have hv1 : v.1 = a.1 + t * ztbco := by_rfl
  have hv2 : v.2 = a.2 := by
    zvmyq; show a.2 + t * ((W.vtx ztwjb).2 - a.2) = a.2; simp_all
  have hb2 : b.2 = a.2 := by_simp_all
  have eB1 : (b - v).1 = ztca * ztbco := by simp only [Prod.fst_sub]; grind
  have eB2 : (b - v).2 = 0 := by_simp_all
  have eA1 : (a - v).1 = -t * ztbco := by_simp_all
  have eA2 : (a - v).2 = 0 := by_simp_all
  have eX2 : (rayPt v σ 1 - v).2 = 0 := by_simp
  have hBA : ztzqq := by unfold sideCross; simp_all
  have hBX : sideCross ztfd (rayPt v σ 1 - v) = 0 := by unfold sideCross; simp_all
  have hdot : sideDot ztfd ztgg ≤ 0 := by
    unfold sideDot; rw [eB1, eB2, eA1, eA2]
    have h1 : 0 ≤ ztca * t := mul_nonneg by_linarith ht0.le
    nlinarith [sq_nonneg ztbco]
  unfold sideCcw at hs
  grind
variable {M : Model}
variable (Q : Polygon)
/-- **The height code of a point**: at a position `(p, t)` whose point has the height of vertex
`h` of `Q`, the position with the height code `h + 1` on edge `p` is the same position (inside a
horizontal edge only the start vertex has a horizontal ray in its left sector). -/
theorem param_of_arrival {p : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {h : ℕ}
    (hy : (Q.vtx h).2 = (sidePt M.W p t).2) {σ : ℝ}
    (hsec : sideLeft M.W p t ztwyg) :
    M.param Q ztdw = t := by
  zuefh
  · have ht : ztbhh := by
      zuct
      exact not_sideLeft_horizontal (lt_of_le_of_ne ht0 ztnr) ht1 hh σ hsec
    zubys
    zufde
    simp_all
  · zufde
    zubi
    rw [ite_eq_right hh, hy]
    have : ztehi := sub_ne_zero.2 ztqaz
    have e : (sidePt M.W p t).2 = (M.wa p).2 + t * ztcrr := rfl
    simp_all
theorem pos_of_arrival {p : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {h : ℕ}
    (hy : (Q.vtx h).2 = (sidePt M.W p t).2) {σ : ℝ}
    (hsec : sideLeft M.W p t ztwyg) :
    M.pos Q ztdw = sidePt M.W p t := by
  zueew
  rw [param_of_arrival Q ht0 ht1 hy hsec]
  rfl
end Record
section RecordJ
variable (J : Merge.Junction)

/-- **The record of a chord of `C` from the arrival positions of its ends**: `(pz, tz)` a position
of the query point `z` whose left sector contains the ray, `(pw, tw)` an arrival position of the
hit point `w = rayPt z σ T`, `h` a vertex of `Q` at the height of `z`. -/
theorem recordData_of_arrival (Q : Polygon) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ}
    (hT : 0 < T) {h : ℕ} (hh : (Q.vtx h).2 = z.2) {pz pw : ℕ} {tz tw : ℝ}
    (hAz : Arrival (chainModel J.whole).W z (-σ) pz tz)
    (hAw : Arrival (chainModel J.whole).W ztxn σ pw tw) :
    RecordData J Q z σ T h pz pw (if σ = 1 then pz else pw) (if σ = 1 then pw else pz) := by
  set M := chainModel J.whole
  zukv
  obtain ⟨hpz, htz0, htz1, hptz, hsecz⟩ := hAz
  obtain ⟨hpw, htw0, htw1, hptw, hsecw⟩ := hAw
  rw [neg_neg] at hsecz
  have hsz : sideLeft M.W pz tz (rayPt (sidePt M.W pz tz) σ 1) := by_simp_all
  have hsw : sideLeft M.W pw tw (rayPt (sidePt M.W pw tw) (-σ) 1) := by_simp_all
  have hyz : (Q.vtx h).2 = (sidePt M.W pz tz).2 := by_simp_all
  have hyw : (Q.vtx h).2 = (sidePt M.W pw tw).2 := by_simp_all
  have ez := param_of_arrival Q htz0 htz1 hyz hsz
  have ew := param_of_arrival Q htw0 htw1 hyw hsw
  -- the attachments
  have hw' : rayPt ztxn (-σ) T = z := by
    zueob
  have hAz' : Arrival M.W (rayPt ztxn (-σ) T) (-σ) pz tz := by
    zuofq
    refine ⟨hpz, htz0, htz1, hptz, ?_⟩
    simp_all
  have att_z := attach_left_of_arrival hnσ hT hAz'
  rw [hw', Geometry.segment_comm] at att_z
  have att_w := attach_left_of_arrival hσ hT ⟨hpw, htw0, htw1, hptw, hsecw⟩
  refine ⟨hh, ?_, ?_, ?_, ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rw [pos_of_arrival Q htz0 htz1 hyz hsz, hptz]
  · rw [pos_of_arrival Q htw0 htw1 hyw hsw, hptw]
  · grind
  · grind
  · simp_all
  grind
end RecordJ
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc sideCross TouchesIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open OracleQ (sj sk ek succP predP)
namespace Sweep
section Records
variable {M : Model} {Q : Polygon} {N : NF}

/-- A chord of the family of a normal form is the chord of a record. -/
theorem nf_chord_of_mem {e : Set Point} (he : e ∈ N.F M Q) :
    ∃ k, k < N.nChords ∧ (N.chord k).toSet M Q = e := by
  obtain ⟨r, hr, rfl⟩ := he
  zubhj
  zulow
  zudly
  simp_all

/-- Two horizontal segments with a nondegenerate second one are equal only with equal ends. -/
theorem hseg_eq_ends {y L R y' a b : ℝ} (h : hseg y L R = hseg y' a b) (hab : a < b) :
    L = a ∧ R = b ∧ y = y' := by
  have ha : (ztteu : Point) ∈ hseg y L R := by zvmwc; exact ztgpm
  have hb : (zttfq : Point) ∈ hseg y L R := by zvmwc; exact ztgpl
  obtain ⟨hy, haL, haR⟩ := ha
  obtain ⟨-, hbL, hbR⟩ := hb
  simp only at hy haL haR hbL hbR
  have hL : ((L, y) : Point) ∈ hseg y' a b := by zvmzi; exact ⟨rfl, le_rfl, by_linarith⟩
  have hR : ((R, y) : Point) ∈ hseg y' a b := by zvmzi; exact ⟨rfl, by_linarith, le_rfl⟩
  obtain ⟨-, hL1, -⟩ := hL
  obtain ⟨-, -, hR2⟩ := hR
  grind

/-- **The ends of an attached record** of a nondegenerate horizontal chord. -/
theorem rec_pos_ends {c : CRec} (hA : c.Attached M Q) {y a b : ℝ}
    (hc : c.toSet M Q = hseg y a b) (hab : a < b) :
    M.pos Q c.lpos = ztdv ∧ M.pos Q c.rpos = ztdy ∧ (Q.vtx c.h).2 = y := by
  have hl := hA.1.2.2.2.1
  have hr := hA.2.2.2.2.1
  have hset : c.toSet M Q = hseg (Q.vtx c.h).2 (M.pos Q c.lpos).1 (M.pos Q c.rpos).1 := rfl
  obtain ⟨hL, hR, hy⟩ := hseg_eq_ends (hset.symm.trans hc) hab
  have hl2 : (M.pos Q c.lpos).2 = (Q.vtx c.h).2 := by rw [hset] at hl; exact hl.1
  have hr2 : (M.pos Q c.rpos).2 = (Q.vtx c.h).2 := by rw [hset] at hr; exact hr.1
  grind
end Records

/-! ## Regions touching a chord -/

/-- A region on a side of an attached admissible chord touches it. -/
theorem touchesIn_of_sideOf {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t) {ρ : ℝ} {U : Set Point}
    (hS : SideOf M ρ c U) : TouchesIn M.D c U := by
  obtain ⟨z, hz, hzD⟩ := exists_mem_dom hM hc hA
  refine ztrfa
  have hev := hS z hz hzD
  have hlim : Tendsto (fun δ : ℝ => ((z.1, z.2 + ρ * δ) : Point)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc0 : Continuous (fun δ : ℝ => (ztdis : Point)) := by fun_prop
    have := hc0.tendsto 0
    zubzw
    zuhv
  zulzh

/-! ## The spine around a key -/
section Spine
variable {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) (hGM : GoodModel M)
  (hne : (N.F M Q).Nonempty)
include hN hGM hne
variable {κ : ℝ} {j : ℕ}
/-- The arc starting at a located cut is at spine position `j` or `j + 1`. -/
theorem spine_start (hj : j < N.arcs.length)
    (hloc : sk M Q N j = κ ∨ ek M Q N j = κ) {p : ℕ} (hp : p < N.arcs.length)
    (hs : sk M Q N p = κ) : p = j ∨ p = succP N.arcs.length j := by
  zuklr
  · exact Or.inl (OracleQ.start_unique hN hGM hne hp hj (hs.trans h.symm))
  · exact Or.inr (OracleQ.end_start_adj hN hGM hne hj hp (h.trans hs.symm))

/-- The arc ending at a located cut is at spine position `j - 1` or `j`. -/
theorem spine_end (hj : j < N.arcs.length)
    (hloc : sk M Q N j = κ ∨ ek M Q N j = κ) {p : ℕ} (hp : p < N.arcs.length)
    (he : ek M Q N p = κ) : p = predP N.arcs.length j ∨ p = j := by
  zuklr
  · left
    have := OracleQ.end_start_adj hN hGM hne hp hj ztvuw
    rw [this, OracleQ.predP_succP hp]
  · exact Or.inr (OracleQ.end_unique hN hGM hne hp hj ztvuw)
end Spine

/-! ## Arcs of the regions around a key -/
section Around
variable {M : Model} {Q : Polygon} {N : NF}

/-- The region indices of the arcs at the spine positions `j - 1`, `j`, `j + 1`. -/
def nbrRegs (N : NF) (j : ℕ) : List ℕ :=
  [(N.arc ztcay).reg, (N.arc ztbhb).reg,
    (N.arc ztcaz).reg]

/-- **A region with an arc starting or ending at a located cut** is one of the three. -/
theorem region_of_arc_at (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {κ : ℝ} {j : ℕ} (hj : j < N.arcs.length) (hloc : sk M Q N j = κ ∨ ek M Q N j = κ)
    {r : ℕ} (hr : r < N.nRegions) {a b : ℝ}
    (harc : M.IsArc ztdu ztqvn a b) (hab : a = κ ∨ b = κ) : r ∈ nbrRegs N j := by
  zuzj
  obtain ⟨i, hi, hir, his, hie⟩ := hArcs.2.2.1 r hr a b harc
  obtain ⟨p, hp, hpi⟩ := NFLoc.seq_surj hN hi
  have hsj : sj N p = i := hpi
  have hA := N.arcs.length
  zufzu
  · have hs : sk M Q N p = a := by unfold sk; simp_all
    rcases spine_start hN hGM hne hj hloc hp hs with rfl | rfl
    · zubdf

    · zubdf

  · have he : ek M Q N p = b := by unfold ek; simp_all
    rcases spine_end hN hGM hne hj hloc hp he with rfl | rfl
    · zubdf

    · zubdf

/-- A region of the family is `regOf` of an index. -/
theorem regOf_surj (hN : IsNF M Q N) {U : Set Point} (hU : U ∈ M.regions ztdu) :
    ∃ r, r < N.nRegions ∧ regOf M Q N r = U :=
  (regOf_spec hN).1.2.2 U hU
end Around

/-! ## Facing just after and just before a cut -/
section Facing
variable {M : Model}

/-- An arc faces its region just before its end inside a walk edge. -/
theorem beforeFaces_of_arc_end' {F : Set ztf} {U : Set Point} {l : ℝ} {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (harc : M.IsArc F U l ztk)
    (hlr : l ≠ (p : ℝ) + t) : BeforeFaces M p t U := by
  zufzk
  refine ⟨δ, hδ, fun _ s hs0 hs1 hst => ?_, fun h => absurd h ht0.ne'⟩
  have := hsub ztdxi
  refine harc.2.2.2.2.2.2 p _ hp by_linarith by_linarith ?_
  grind

/-- **The regions faced just after and just before a cut** have arcs starting and ending at the
cut. -/
theorem faced_arcs (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hp1 : t = 0 → 1 ≤ p)
    (hcut : M.IsCut F ztdj) {U : Set Point} (hU : U ∈ M.regions F) :
    (AfterFaces M p t U → ∃ r, M.IsArc F U ztdj r) ∧
      (BeforeFaces M p t U → ∃ l, M.IsArc F U l ztdj) := by
  zudqz
  obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hAc.2.1 hAc.2.2.1 ht0 ht1 hkey.symm
  obtain ⟨U', V', l, r, hU', hV', -, harcU, harcV, -⟩ := hM.attach_face hF hfin hc hAc
  zubar
  refine ⟨fun hW => ⟨r, ?_⟩, fun hW => ⟨l, ?_⟩⟩
  · have hW' := afterFaces_of_arc harcU hp ht0
      ztnqg
    rw [after_unique ht1 hU hU' hW hW']
    omega
  · have hlr := (WalkAx.arc_cuts hne harcV).2.2
    have hW' : BeforeFaces M p' t' V' := by
      zukmk
      · exact beforeFaces_of_arc_end' hp htp ht1 harcV hlr
      · subst ht00
        exact beforeFaces_of_arc_end hp (hp1 rfl) harcV hlr
    rw [before_unique ht0 hU hV' hW hW']
    omega
end Facing

/-! ## The local hit -/
section LocalHit

/-- A chord record **matches** the position `x` in the direction of code `d`: its end at `x` (the
left end for `d = 1`, the right end otherwise) has the edge and the height code of `x`. -/
def ChordAt (c : CRec) (x : WPos) (d : ℕ) : Prop :=
  (d = 1 ∧ c.lp = x.edge ∧ c.h + 1 = x.hgt) ∨ (d ≠ 1 ∧ c.rp = x.edge ∧ c.h + 1 = x.hgt)

/-- The far end of a chord record for the direction of code `d`. -/
def farPos (c : CRec) (d : ℕ) : WPos := if d = 1 then c.rpos else c.lpos
variable (C : Chain)

/-- The position `(0, 0)` of a chain model is the top of the slit, outside the box band. -/
theorem key_pos_of_band {Q : Polygon} {x : WPos}
    (hzR : |((chainModel C).pos Q x).2| < C.radius) (h0 : (chainModel C).param Q x = 0) :
    1 ≤ x.edge := by
  zukr
  have hp0 : x.edge = 0 := by_omega
  have e : (chainModel C).pos Q x = C.slitTop := by
    show sidePt (chainModel C).W x.edge _ = C.slitTop
    rw [hp0, h0, Chazelle.Chain.sidePt_zero]; rfl
  zvmwe at hzR
  simp only [Chain.slitTop] at hzR
  grind

/-- **The local hit** (completeness).  For a walk position `x` of the chain model whose height code
names the height of its point `z`, with the ray in direction `dirOf d` in its left sector, and an
answer `j` of double identification for its key: the direction is free for the chain, and its
exit point lies on the listed arcs of the regions `nbrRegs N j` outside the closed holes (which are
near `z`), or is the far end of an exit chord of one of these regions matching `x`. -/
theorem local_hit_mem (hP : C.P.Simple) {Q : Polygon} (hD : DistinctHeights Q) {N : NF}
    (hN : IsNF ztc Q N) {x : WPos} {h : ℕ} (hxh : x.hgt = h + 1) (hhn : h < Q.n)
    (hx : x.edge < (chainModel C).W.n) (hx0 : 0 ≤ (chainModel C).param Q x)
    (hx1 : (chainModel C).param Q x < 1) (hyz : (Q.vtx h).2 = ((chainModel C).pos Q x).2)
    {d : ℕ} (hsec : sideLeft (chainModel C).W x.edge ztuy
      (rayPt ztte ztwf 1))
    (hzR : |((chainModel C).pos Q x).2| < C.radius) (hzt : ((chainModel C).pos Q x).2 ≤ C.top.2)
    {j : ℕ} (hj : j < N.arcs.length)
    (hloc1 : ¬ (chainModel C).IsCut ztwjh ztlb →
      N.F ztc Q = ∅ ∨
        sideInArc ztwvb ztwus ztlb)
    (hloc2 : (chainModel C).IsCut ztwjh ztlb →
      sk ztc Q N j = (chainModel C).key Q x ∨
        ek ztc Q N j = (chainModel C).key Q x)
    {m : ℕ → ℕ} {AB K : ℕ}
    (hlist : ∀ r ∈ nbrRegs N j, ∀ a ∈ (N.region r).arcs, ∃ i < K,
      (chainModel C).key Q (ShotList.arcAt m AB i).1 = (chainModel C).key Q (N.arc a).s ∧
      (chainModel C).key Q (ShotList.arcAt m AB i).2 = (chainModel C).key Q (N.arc a).e)
    {hs : List ztqx} (hnear : Restore.Near ztc Q hs ztte) :
    FreeAt C ztte ztwf ∧
      (rayPt ztte ztwf ztzta ∈
          ShotList.loSet ztc Q m AB K hs ∨
        ∃ r ∈ nbrRegs N j, ∃ k ∈ (N.region r).chords, ChordAt ztcgt x d ∧
          (chainModel C).pos Q (farPos ztcgt d) =
            rayPt ztte ztwf
              ztzta) := by
  zudbh
  zuinu
  set p := x.edge with hpdef
  set t := M.param Q x with htdef
  set z := M.pos Q x with hzdef
  zujne
  have hσ : ztim := dirOf_cases d
  have hGM : ztsbo := Or.inl by_grind
  zubm
  zumbq
  zubl

  have hpt : sidePt M.W p t = z := rfl
  have hsec' := hsec
  have hfree := freeAt_of_leave C hP hσ hx hx0 hx1 hpt hsec
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt C hzt hσ hfree
  zuckj
  zuknu
  have hkey : M.key Q x = (p : ℝ) + t := rfl
  have hp1 := (key_pos_of_band C hzR)
  obtain ⟨hRC, hCS, hArcs, hRegs, -, hhlt, -⟩ := regOf_spec hN
  -- a region of `nbrRegs` containing the start of the ray gives the exit point on the arcs
  have via_region : ∀ r, r < N.nRegions → r ∈ nbrRegs N j →
      (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ regOf M Q N r) →
      rayPt z σ T ∈ ShotList.loSet M Q m AB K hs := by
    intro r hr hrn hray
    zufud
    set L := (List.range K).map (fun i => (M.key Q (ShotList.arcAt m AB i).1,
      M.key Q (ShotList.arcAt m AB i).2)) with hLdef
    have hL : ∀ a b, M.IsArc F ztqvn a b → ztvk ∈ L := by
      zucdj

      have hmem := (hArcs.2.2.2 r hr i₀).2 by_omega
      grind
    zuga

    refine ⟨p', t', hp', ht0', ht1', by_grind, fun g hg hin => ?_, hpt'⟩
    obtain ⟨p'', hp'', ⟨t₁, h₁0, h₁1, h₁⟩, t₂, h₂0, h₂1, h₂⟩ := hnear g hg p' t' hp' ht0' ht1' hin
    exact Restore.no_common_edge hM hσ hT hdom hp'' h₁0 h₁1 h₂0 h₂1 h₁
      (h₂.trans hpt'.symm)
  -- the region of the arc at spine `j` when the key is not a cut
  have noncut : ¬ M.IsCut F ztdj → rayPt z σ T ∈ ShotList.loSet M Q m AB K hs := by
    intro hnc
    have hjA := NFLoc.seq_lt hN hj
    zugps
    have hin : sideInArc ztevn zteru ztdj := by
      rcases hloc1 hnc with hF0 | hin
      · zucir
        · grind
        · have hk0 : ztehd := by
            rcases hx0.lt_or_eq with ht | ht
            · grind
            · have := hp1 ht.symm
              positivity
          show sideInArc ztypa ztyoz ztdj
          zucpu
          zujv
      grind
    have hray := ray_mem_region_of_arc hGM hFam (hRC.1 _ hr0) hx hx0 hx1 harc0 hin hσ hsec'
    zudum
    exact via_region _ hr0 (by zupdi) hray
  rcases leave_cases C hP hFam hσ hx hx0 hx1 hpt hsec hzR with ⟨e, he, hAe, hev⟩ | hnc |
      ⟨ht0, -, hnot, hcr⟩
  · -- along a chord of the family attached at `x`
    right
    have he' := hF he
    have hcut : ztidq := ⟨e, he, p, t, hAe, rfl⟩
    have hne : F.Nonempty := ztugi
    obtain ⟨k, hk, hke⟩ := nf_chord_of_mem he
    obtain ⟨y, a, b, hH, -, hey, -, -⟩ := Merge.augChords_spec he'
    zudoh
    have hAk := hN.2.2.1 k hk
    obtain ⟨hla, hrb, hky⟩ := rec_pos_ends hAk (hke.trans hey) hab
    have hze : z ∈ hseg y a b := by rw [← hey, ← hpt]; exact hAe.2.2.2.1
    have hzD : ztsnn := by zvnbr; exact hM.trace p hx t hx0 hx1.le
    obtain ⟨hzy, hza, hzb⟩ := hze
    have hopen := hH.open_mem
    have hzpt : ztyxx := by_grind
    -- the side of `z` on the chord, and the first hit
    obtain ⟨hzend, hfar, hdir, hτ⟩ : (σ = 1 ∧ z.1 = a ∨ σ = -1 ∧ z.1 = b) ∧
        (ztdy : Point) ∉ C.dom ∧ (ztdv : Point) ∉ C.dom ∧ True := by
      refine ⟨?_, hH.right_not, hH.left_not, trivial⟩
      zubrt
      have hs₁0' := hs₁0
      rw [hey] at hs₁
      obtain ⟨-, hs₁a, hs₁b⟩ := hs₁
      zvogc at hs₁a hs₁b
      zukmy
      · left; refine ztuiv
        rw [hσ1] at hs₁b
        grind
      · right; refine ztuiv
        rw [hσ1] at hs₁a
        grind
    have hd1 : σ = 1 ↔ d = 1 := by
      constructor
      · intro h1; by_contra hd; rw [hσdef] at h1; unfold dirOf at h1; grind
      · intro h1; rw [hσdef, h1]; rfl
    -- the genuine hit at the far end
    have hT' : T = b - a := by
      zubsa
      · have hg : ztzoq := genuine_along_chord C he' ztntt
          hzD hσ by_linarith (by
            rw [hey]; refine ztgog <;> zunxb <;> linarith)
          (by
            have : rayPt z σ zthu = (ztdy : Point) := by
              zuyj
            grind)
        zufek
      · have hg : ztzoq := genuine_along_chord C he' ztntt
          hzD hσ by_linarith (by
            rw [hey]; refine ztgog <;> zunxb <;> linarith)
          (by
            have : rayPt z σ zthu = (ztdv : Point) := by
              zuyj
            grind)
        zufek
    -- the region on a faced side
    obtain ⟨ρ, U, hρ, hU, hS, hfac⟩ : ∃ ρ U, (ρ = 1 ∨ ρ = -1) ∧ U ∈ M.regions F ∧ SideOf M ρ e U ∧
        FacedSide M p t ρ σ U := by
      have hdir' : (σ = 1 ∧ ∀ z' ∈ e, (sidePt M.W p t).1 ≤ z'.1) ∨
          (σ = -1 ∧ ∀ z' ∈ e, z'.1 ≤ (sidePt M.W p t).1) := by
        rw [hpt, hey]
        zubsa
        · exact Or.inl ⟨hσ1, fun z' hz' => by zuntc; exact hz'.2.1⟩
        · exact Or.inr ⟨hσ1, fun z' hz' => by zuntc; exact hz'.2.2⟩
      by_cases huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e
      · obtain ⟨U, hU, hS⟩ := side_region_exists hM hF hfin he (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
        exact ⟨1, U, Or.inl rfl, hU, hS,
          (faced_or_middle hGM hFam he hAe ztp hU hS hdir').1 huniq⟩
      · zumiv
        obtain ⟨e', he'F, hAe', hne'⟩ := huniq
        obtain ⟨U₁, hU₁, hS₁⟩ := side_region_exists hM hF hfin he (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
        obtain ⟨U₂, hU₂, hS₂⟩ := side_region_exists hM hF hfin he (Or.inr rfl : (-1 : ℝ) = 1 ∨ _)
        have f1 := (faced_or_middle hGM hFam he hAe ztp hU₁ hS₁ hdir').2 e' he'F hne' hAe'
        have f2 := (faced_or_middle hGM hFam he hAe ztbt hU₂ hS₂ hdir').2 e' he'F hne' hAe'
        grind
    -- its arc at the key, its index, and the chord in its exit list
    obtain ⟨hfa, hfb⟩ := faced_arcs hM hF hfin hx hx0 hx1 hp1 hcut hU
    obtain ⟨rU, hrU, hrUe⟩ := regOf_surj hN hU
    have hmem : rU ∈ nbrRegs N j := by
      have hρσ : ρ * σ = -1 ∨ ρ * σ = 1 := by
        grind
      rcases hρσ with h | h
      · obtain ⟨r', harc⟩ := hfa ztvvc
        zujmh
        exact region_of_arc_at hN hGM hne hj ztmlj hrU harc ztp
      · obtain ⟨l', harc⟩ := hfb ztqqc
        zujmh
        exact region_of_arc_at hN hGM hne hj ztmlj hrU harc ztbt
    have htouch := touchesIn_of_sideOf hM ztesz hAe hS
    have hkr : k ∈ (N.region rU).chords := by
      refine ((hRegs rU hrU).1 k).2 ztuhq
      grind
    -- the height index and the attachment edge
    have hkh : (N.chord k).h = h := by
      zuirz
      exact hD _ _ by_grind hhn hne' by_grind
    have hAk1 := hAk.1
    rw [hke] at hAk1
    have hAk2 := hAk.2
    rw [hke] at hAk2
    refine ⟨rU, hmem, k, hkr, ?_⟩
    zubsa
    · have hd := hd1.1 hσ1
      have hlp := (hM.attach_unique ztesz hAk1 hAe (by
        show M.pos Q (N.chord k).lpos = sidePt M.W p t
        grind)).1
      refine ⟨Or.inl by_omega, ?_⟩
      simp only [farPos, ite_eq_left hd]
      rw [hrb, hT']
      zuyj
    · have hd : d ≠ 1 := by_grind
      have hrp := (hM.attach_unique ztesz hAk2 hAe (by
        show M.pos Q (N.chord k).rpos = sidePt M.W p t
        grind)).1
      refine ⟨Or.inr by_omega, ?_⟩
      simp only [farPos, ite_eq_right hd]
      rw [hla, hT']
      zuyj
  · grind
  · -- a cut walk vertex: the region faced just after or just before
    left
    zujtc
    · have hcut' := hcut
      obtain ⟨c, hc, p', t', hAc, hk'⟩ := hcut'
      obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hAc.2.1 hAc.2.2.1 hx0 hx1 hk'.symm
      zubar
      zubou
      have hp1' := hp1 ht0
      rw [ht0] at hAc harcU harcV
      have hpt0 : sidePt M.W p 0 = z := by_grind
      have hsec0 : sideLeft M.W p 0 ztzns := by_grind
      have hnot' : ∀ c ∈ F, SideAttach M.W c p 0 →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs σ s ∉ c := by
        intro c hc hA; rw [hpt0]; grind
      have hloc := hloc2 hcut
      rw [hkey, ht0] at hloc
      zukle
      · have hray := ray_mem_region_after hGM hFam hU hx harcU hc hAc hσ hsec0 hnot' hcr
        zukvr
        obtain ⟨rU, hrU, rfl⟩ := regOf_surj hN hU
        exact via_region rU hrU (region_of_arc_at hN hGM hne hj hloc hrU harcU ztp) hray
      · have hray := ray_mem_region_before hGM hFam hV hx hp1' harcV hc hAc hσ hsec0 hnot' hcr
        zukvr
        obtain ⟨rV, hrV, rfl⟩ := regOf_surj hN hV
        exact via_region rV hrV (region_of_arc_at hN hGM hne hj hloc hrV harcV ztbt) hray
    grind
