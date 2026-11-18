module

public import Chazelle.Core.ClusterStepMain

/-!
# WP-I, part 40: one iteration of the split driver on the RAM

`splitBody`: pop the top segment `(lo, hi)` of the stack (`popB`), compute the median face and
the level window (`medB`), climb to the centroid (`climbStmt`) and run the tail of the split
(`splitTail`).  `splitBody_exec`: from a memory with the static facts and the driver invariant,
one iteration costs at most `119 (hi - lo) + splitC L k` and restores the invariant for the new
stack.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The keys of a range only matter inside it. -/
theorem cntIn_congr {κ κ' : ℕ → ℕ} {lo hi a b : ℕ} (h : ∀ i, lo ≤ i → i < hi → κ' i = κ i) :
    cntIn κ' lo hi a b = cntIn κ lo hi a b := by
  unfold cntIn
  congr 1
  refine Finset.filter_congr (fun i hi' => ?_)
  simp only [Finset.mem_Ico] at hi'
  rw [h i hi'.1 hi'.2]

theorem SS.Regs.of_frame2 {S : SS} {c c' : Config} (h : S.Regs c)
    (hr : ∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → c'.nreg r = c.nreg r) : S.Regs c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by unfold SplitRG; omega) (by omega) (by omega)]; assumption)

/-- Pop the top entry: `tp := tp - 2`, `lo := STK[tp]`, `hi := STK[tp + 1]`. -/
def popB : Stmt := block [.subN 130701 130701 130001, .subN 130701 130701 130001,
  .addN 130702 130700 130701, .loadN 130300 130702, .addN 130702 130702 130001,
  .loadN 130301 130702]

/-- One iteration of the split driver. -/
def splitBody : Stmt := .seq popB (.seq medB (.seq climbStmt splitTail))

/-- The constant part of the cost of one iteration. -/
def splitC (L k : ℕ) : ℕ := (34 * L + 34) * (L + 2) + 36 * L + 36 * k + 340

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
  refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, fun r a b c d => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [htp, h1]; omega
  · config_simp; simp only [htp, h1, hs]; rw [show tp + 2 - 1 - 1 = tp by omega]
  · config_simp; simp only [htp, h1, hs]; rw [show tp + 2 - 1 - 1 = tp by omega]
  · simp only [Machine.upd_apply]; split_ifs <;> omega

end proofs

section body

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {P : Polygon} {W : ℕ}

/-- The keys of the items of a segment are preorders. -/
theorem SFacts.key_eq {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m) {i : ℕ}
    (hv : m (S.bACT + i) < μ) :
    keyOf m S.bACT S.bFIRST S.bFPRE i = preE (m (S.bFIRST + m (S.bACT + i))) ∧
      m (S.bFIRST + m (S.bACT + i)) < N := by
  have hf := hSF.first ⟨_, hv⟩
  simp only at hf
  have hN : m (S.bFIRST + m (S.bACT + i)) < N := by rw [hf]; exact Fin.isLt _
  exact ⟨by unfold keyOf; rw [hSF.pre _ hN], hN⟩

/-- The good test in memory is the good test of the preorder tree. -/
theorem SFacts.gdF_iff {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m) {lo hi : ℕ}
    (hlt : ∀ i, lo ≤ i → i < hi → m (S.bACT + i) < μ) {z : ℕ} (hz : z < N) :
    GdF m S.bACT S.bFIRST S.bFPRE S.bFSZ lo hi z ↔
      BTree.GdN preE (fun g => (R.sub g).card) (fun i => preE (m (S.bFIRST + m (S.bACT + i))))
        lo hi z := by
  unfold GdF BTree.GdN
  rw [hSF.pre z hz, hSF.sz z hz,
    cntIn_congr (fun i h1 h2 => (hSF.key_eq (hlt i h1 h2)).1)]

open Classical in
/-- **One iteration of the split driver.** -/
theorem splitBody_exec {S : SS} {A0 U : ℕ} {cf : Config} (hw : WordsBounded W cf)
    (hR : S.Regs cf) (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W cf.nmem)
    {lo hi : ℕ} {rest : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}
    (hD : DInv M T k c S cf.nmem ((lo, hi) :: rest) fin D nsp)
    (htp : cf.nreg 130701 = 2 * rest.length + 2) (hnsp : cf.nreg 130704 = nsp)
    (hk : 0 < k) (hs : 0 < S.s) :
    ∃ cf' K, Exec P W splitBody cf cf' K ∧ K + 2 ≤ 119 * (hi - lo) + splitC S.L k ∧
      WordsBounded W cf' ∧ S.Regs cf' ∧
      (∃ news fin' D', DInv M T k c S cf'.nmem (news ++ rest) fin' D' (nsp + 1) ∧
        cf'.nreg 130701 = 2 * (news ++ rest).length ∧
        (news.map (fun p => len p * Nat.size (len p))).sum + (hi - lo) ≤
          (hi - lo) * Nat.size (hi - lo)) ∧
      cf'.nreg 130704 = nsp + 1 ∧ StaticEq A0 U cf.nmem cf'.nmem ∧
      (∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → cf'.nreg r = cf.nreg r) ∧
      cf'.rreg = cf.rreg ∧ cf'.rmem = cf.rmem ∧ cf'.output = cf.output := by
  have hL := hSF.lay
  have := hL.hFIRST; have := hL.hLEV; have := hL.hPV; have := hL.hFP; have := hL.hATT
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ; have := hL.hFPRE
  have := hL.hLBOT; have := hL.hLTOP; have := hL.hHALF; have := hL.hPOW; have := hL.hUPT
  have := hL.hUP; have := hL.hμU; have := hL.hNU; have := hL.hLU; have := hL.hVERT
  have := hL.hOPP; have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hSTK
  have := hL.hDF; have := hL.hW
  have hμ := hSF.hμ; have hN := hSF.hN
  have hpb := hSF.pow_big; have hpU := hSF.pow_U
  have hLU : S.L * S.N ≤ S.L * U := Nat.mul_le_mul_left _ (by omega)
  generalize hm_def : cf.nmem = m at hSF hD
  have hlv : Lv ((lo, hi) :: rest) fin (lo, hi) := Or.inl List.mem_cons_self
  have hhi : hi ≤ μ := hD.rng _ hlv
  have hlh : lo ≤ hi := hD.sinv.wf _ hlv
  have hbig : S.s < hi - lo := hD.sinv.big _ List.mem_cons_self
  have hlen0 := hD.sinv.length_le
  simp only [List.length_cons] at hlen0
  have hmem : ∀ i, lo ≤ i → i < hi →
      m (S.bACT + i) ∈ items (fun i => m (S.bACT + i)) (lo, hi) :=
    fun i i1 i2 => mem_items.mpr ⟨i, i1, i2, rfl⟩
  have hactμ : ∀ i, lo ≤ i → i < hi → m (S.bACT + i) < μ :=
    fun i i1 i2 => hD.sinv.lt _ hlv _ (hmem i i1 i2)
  -- the stack top
  have hstk := hD.stack
  rw [List.length_cons, stkList] at hstk
  obtain ⟨htop, -⟩ := List.cons.inj hstk
  obtain ⟨hlo_eq, hhi_eq⟩ := Prod.mk.inj htop
  -- pop
  obtain ⟨c1, k1, x1, hk1, hw1, hm1, htp1, hlo1, hhi1, hr1, hrr1, hrm1, ho1⟩ :=
    popB_exec (P := P) hw hR (tp := 2 * rest.length) htp (by omega)
  rw [hm_def, ← hlo_eq] at hlo1
  rw [hm_def, ← hhi_eq] at hhi1
  rw [hm_def] at hm1
  have hfr1 : ∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → c1.nreg r = cf.nreg r :=
    fun r h1 h2 h3 => hr1 r h2 (by unfold SplitRG at h1; omega) (by unfold SplitRG at h1; omega)
      (by unfold SplitRG at h1; omega)
  have hR1 : S.Regs c1 := hR.of_frame2 hfr1
  -- the median and the window
  have hhalf : m (S.bHALF + (hi - lo)) = (hi - lo) / 2 := hSF.half _ (by omega)
  have hmed : lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 < hi := by omega
  have hmedv := hactμ _ hmed.1 hmed.2
  have hlov := hactμ lo le_rfl (by omega)
  have hlev0 := hSF.lev ⟨_, hlov⟩
  have hlevlt := hSF.lev_lt ⟨_, hlov⟩
  simp only at hlev0 hlevlt
  obtain ⟨c2, k2, x2, hk2, hw2, hm2, hW2, hy2, hb2, ht2, hlo2, hhi2, hr2, hrr2, hrm2, ho2⟩ :=
    medB_exec (P := P) hw1 hR1 hlo1 hhi1 (by omega)
      (by rw [hm1, hhalf]; omega)
      (by rw [hm1, hhalf, show (hi - lo) / 2 + lo = lo + (hi - lo) / 2 by omega]; omega)
      (by omega) (by rw [hm1]; omega) (by rw [hm1, hlev0]; omega) (by rw [hm1, hlev0]; omega)
  rw [hm1] at hy2 hb2 ht2
  rw [hhalf, show (hi - lo) / 2 + lo = lo + (hi - lo) / 2 by omega] at hy2
  have hR2 : S.Regs c2 := hR1.of_frame hr2
  set y := m (S.bFIRST + m (S.bACT + (lo + (hi - lo) / 2))) with hy_def
  set lbot := m (S.bLBOT + m (S.bLEV + m (S.bACT + lo))) with hlbot
  set ltop := m (S.bLTOP + m (S.bLEV + m (S.bACT + lo))) with hltop
  have hm2' : c2.nmem = m := by rw [hm2, hm1]
  -- the climb
  have hCtx : ClimbCtx c2 lo hi S.bACT S.bFIRST S.bFPRE S.bPOW S.L S.bFSZ S.bUP S.L S.N :=
    ⟨hR2.one, hR2.zero, hlo2, hhi2, hR2.cACT, hR2.cFIRST, hR2.cFPRE, hR2.cPOW, hR2.cLP, hW2,
      hR2.cFSZ, hR2.cUP, hR2.cUPE, hR2.cN, hR2.cL⟩
  have hkey : ∀ i, lo ≤ i → i < hi →
      keyOf m S.bACT S.bFIRST S.bFPRE i = preE (m (S.bFIRST + m (S.bACT + i))) ∧
        m (S.bFIRST + m (S.bACT + i)) < N := fun i i1 i2 => hSF.key_eq (hactμ i i1 i2)
  have hcp := hSF.cpMem
  have hupN : ∀ g, g < N → R.up g < N := by
    intro g hg
    rw [hSF.R_up ⟨g, hg⟩]; exact Fin.isLt _
  have hupit : ∀ n g, g < N → R.up^[n] g < N := by
    intro n; induction n with
    | zero => intro g hg; exact hg
    | succ n ih => intro g hg; rw [Function.iterate_succ_apply]; exact ih _ (hupN g hg)
  have hCM : ClimbMem c2.nmem W lo hi S.bACT S.bFIRST S.bFPRE S.bPOW S.L S.bFSZ S.bUP S.L S.N
      R.up := by
    rw [hm2']
    refine ⟨hD.sorted _ List.mem_cons_self, hlh, hSF.pow, by omega, by omega, by omega,
      by omega, fun i i1 i2 => ?_, fun z hz => ?_, by omega, fun g hg => ?_,
      fun j hj g hg => ?_, by omega⟩
    · have := hkey i i1 i2; have := hactμ i i1 i2; omega
    · have := hcp.prsz z hz; omega
    · rw [hN] at hg ⊢; exact hupN g hg
    · rw [hN] at hg ⊢; exact hSF.up_tab j hj g hg
  have hyN : y < N := (hkey _ hmed.1 hmed.2).2
  have hRn := hSF.R_n
  have hroot : GdF c2.nmem S.bACT S.bFIRST S.bFPRE S.bFSZ lo hi (R.up^[2 ^ S.L] y) := by
    have hyR : y < R.n := by rw [hRn]; exact hyN
    have hpos := (hSF.R_ok.pos_spec hyR).1
    rw [BTree.iterate_up_root hSF.R_ok hyR (by omega), hm2', hSF.R_root,
      hSF.gdF_iff (fun i i1 i2 => hactμ i i1 i2) (by omega), ← hSF.R_root]
    exact BTree.good_root hSF.R_ok hSF.R_pre
      (φ := fun i => m (S.bFIRST + m (S.bACT + i)))
      (fun i i1 i2 => ⟨by rw [hRn]; exact (hkey i i1 i2).2, rfl⟩) (by omega)
  obtain ⟨c3, k3, x3, hk3, hm3, hr3, hrr3, hrm3, ho3, hf3, hres3⟩ :=
    climbStmt_exec (P := P) hw2 hCtx hCM hy2 (by rw [hN]; exact hyN) hSF.L_pos hroot
  rw [hm2'] at hres3
  have hm3' : c3.nmem = m := by rw [hm3, hm2']
  have hfr3 : ∀ r, ¬ SplitRG r → c3.nreg r = c2.nreg r := fun r h => hr3 r (fun h' => h (by
    unfold ClimbRG GoodRG at h'; unfold SplitRG; omega))
  have hR3 : S.Regs c3 := hR2.of_frame hfr3
  set f := c3.nreg 130344 with hf_def
  have hfN : f < N := by rw [← hN]; exact hf3
  -- the centroid
  have hgd : ∀ z, z < N → (GdF m S.bACT S.bFIRST S.bFPRE S.bFSZ lo hi z ↔
      BTree.GdN preE (fun g => (R.sub g).card) (fun i => preE (m (S.bFIRST + m (S.bACT + i))))
        lo hi z) := fun z hz => hSF.gdF_iff (fun i i1 i2 => hactμ i i1 i2) hz
  have hsorted : Sorted (fun i => preE (m (S.bFIRST + m (S.bACT + i)))) lo hi := by
    intro i i' h1 h2 h3
    have := hD.sorted _ List.mem_cons_self i i' h1 h2 h3
    rw [(hkey i h1 (by omega)).1, (hkey i' (by omega) h3).1] at this
    exact this
  have hres' : (BTree.GdN preE (fun g => (R.sub g).card)
        (fun i => preE ((fun v => m (S.bFIRST + v)) ((fun i => m (S.bACT + i)) i))) lo hi
        ((fun v => m (S.bFIRST + v)) ((fun i => m (S.bACT + i)) (lo + (hi - lo) / 2))) ∧
        f = (fun v => m (S.bFIRST + v)) ((fun i => m (S.bACT + i)) (lo + (hi - lo) / 2))) ∨
      ∃ x n, R.up^[n] ((fun v => m (S.bFIRST + v)) ((fun i => m (S.bACT + i))
          (lo + (hi - lo) / 2))) = x ∧
        ¬ BTree.GdN preE (fun g => (R.sub g).card)
          (fun i => preE ((fun v => m (S.bFIRST + v)) ((fun i => m (S.bACT + i)) i))) lo hi x ∧
        BTree.GdN preE (fun g => (R.sub g).card)
          (fun i => preE ((fun v => m (S.bFIRST + v)) ((fun i => m (S.bACT + i)) i))) lo hi
          (R.up x) ∧ f = R.up x := by
    rcases hres3 with ⟨hg, he⟩ | ⟨x, n, hx, hng, hg, he⟩
    · exact Or.inl ⟨(hgd y hyN).mp hg, he⟩
    · have hxN : x < N := by rw [← hx]; exact hupit n y hyN
      exact Or.inr ⟨x, n, hx, fun h => hng ((hgd x hxN).mpr h),
        (hgd _ (hupN x hxN)).mp hg, he⟩
  obtain ⟨hgood, hch⟩ := centroid_typed hSF.R_ok hSF.R_n hSF.R_up
    (by rw [hSF.R_root, hSF.r0]) hSF.R_pre (first := first)
    (firstN := fun v => m (S.bFIRST + v)) hSF.first (hD.sinv.inj _ hlv) (hD.sinv.lt _ hlv)
    hsorted hfN hres' (by omega)
  -- the window
  have hwin : ∀ x : Fin μ, (x : ℕ) ∈ items (fun i => m (S.bACT + i)) (lo, hi) →
      lbot ≤ T.level x ∧ T.level x ≤ ltop := by
    intro x hx
    have hsl := hD.sinv.inslab _ hlv _ hx _ (hmem lo le_rfl (by omega))
    have := hSF.win ⟨_, hlov⟩ x hsl
    rw [hlbot, hltop, hlev0]
    exact this
  have hwk : ltop + 1 - lbot ≤ k := by
    have := hSF.win_k ⟨_, hlov⟩
    rw [hlbot, hltop, hlev0]
    exact this
  -- the invariant after the split
  obtain ⟨hsum, news, fin', D', hD', hq2, hstat, hpot⟩ := dinv_split hSF hD
    (tp := 2 * rest.length) rfl hk hwin ⟨f, hfN⟩ hgood hch rfl
  -- the tail
  have hnspW : nsp + 1 ≤ W := by
    have h2 := hD.sinv.pot2
    have : nsp ≤ nsp * S.s := Nat.le_mul_of_pos_right _ hs
    omega
  obtain ⟨c4, k4, x4, hk4, hw4, hq4, hnsp4, hr4, hrr4, hrm4, ho4⟩ :=
    splitTail_exec (P := P) x3.wb_right hR3 hL (lo := lo) (hi := hi) (lbot := lbot) (ltop := ltop)
      (f := f) (tp := 2 * rest.length) (nsp := nsp) (up := upT)
      (by rw [hr3 _ (by unfold ClimbRG GoodRG; omega)]; exact hlo2)
      (by rw [hr3 _ (by unfold ClimbRG GoodRG; omega)]; exact hhi2)
      (by rw [hr3 _ (by unfold ClimbRG GoodRG; omega)]; exact hb2)
      (by rw [hr3 _ (by unfold ClimbRG GoodRG; omega)]; exact ht2) rfl
      (by rw [hr3 _ (by unfold ClimbRG GoodRG; omega), hr2 _ (by unfold SplitRG; omega)]; exact htp1)
      (by rw [hr3 _ (by unfold ClimbRG GoodRG; omega), hr2 _ (by unfold SplitRG; omega),
        hr1 _ (by omega) (by omega) (by omega) (by omega)]; exact hnsp)
      hlh (by rw [hμ]; exact hhi) (by rw [hN]; exact hfN)
      (by rw [hm3']; exact hSF.markMem)
      (fun d hd => by
        rw [hm3', hSF.vert ⟨d, by rw [← hN]; exact hd⟩, hμ]; exact Fin.isLt _)
      (by rw [hm3', hSF.opp ⟨f, hfN⟩, hN]; exact Fin.isLt _)
      (by rw [hm3', hSF.att ⟨f, hfN⟩, hN]; exact Fin.isLt _)
      (by rw [hm3']; exact hcp)
      (by rw [hm3', hSF.fp ⟨f, hfN⟩, hN]; exact Fin.isLt _)
      (fun v hv => by
        have := hSF.first ⟨v, by rw [← hμ]; exact hv⟩
        simp only at this
        rw [hm3', this, hN]; exact Fin.isLt _)
      (fun i i1 i2 => by rw [hm3', hμ]; exact hactμ i i1 i2)
      (by rw [hm3']; exact hsum)
      (by omega) hnspW
  rw [hm3'] at hq4
  refine ⟨c4, k1 + (k2 + (k3 + k4)), .seq x1 (.seq x2 (.seq x3 x4)), ?_, hw4, ?_,
    ⟨news, fin', D', ?_, ?_, hpot⟩, hnsp4, ?_, ?_, ?_, ?_, ?_⟩
  · unfold splitC
    omega
  · refine hR.of_frame2 (fun r h1 h2 h3 => ?_)
    rw [hr4 r h1 h2 h3, hfr3 r h1, hr2 r h1, hfr1 r h1 h2 h3]
  · have e : c4.nmem = (pushF S.bSTK S.s _ _ (pushF S.bSTK S.s _ _ (pushF S.bSTK S.s _ _
        (sepMem (passC _ S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo (hi - lo), 2 * rest.length)))).1 :=
      congrArg Prod.fst hq4
    rw [e]; exact hD'
  · have e := congrArg Prod.snd hq4
    simp only at e
    rw [e]; exact hq2
  · have e := congrArg Prod.fst hq4
    simp only at e
    rw [e]; exact hstat
  · intro r h1 h2 h3
    rw [hr4 r h1 h2 h3, hfr3 r h1, hr2 r h1, hfr1 r h1 h2 h3]
  · rw [hrr4, hrr3, hrr2, hrr1]
  · rw [hrm4, hrm3, hrm2, hrm1]
  · rw [ho4, ho3, ho2, ho1]

end body

end

end Chazelle.Core.Cluster
