module

public import Chazelle.MacT
public import Chazelle.Core.ClusterEulerRam
public import Chazelle.Core.ClusterPrimal
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Programs.Tactics

namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
structure SS where
  bACT : ℕ
  bFIRST : ℕ
  bFPRE : ℕ
  bPOW : ℕ
  bFSZ : ℕ
  bUP : ℕ
  L : ℕ
  N : ℕ
  bLEV : ℕ
  bUPT : ℕ
  bPV : ℕ
  bPOS : ℕ
  bDF : ℕ
  μ : ℕ
  bSO : ℕ
  bSF : ℕ
  bFPAR : ℕ
  bTMP : ℕ
  bHALF : ℕ
  bLBOT : ℕ
  bLTOP : ℕ
  bVERT : ℕ
  bOPP : ℕ
  bATT : ℕ
  bFP : ℕ
  s : ℕ
  bSTK : ℕ
namespace SS
variable (S : SS)

/-- The registers holding the static layout. -/
structure Regs (c : Config) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  -- the climb
  cACT : c.nreg 130320 = S.bACT
  cFIRST : c.nreg 130321 = S.bFIRST
  cFPRE : c.nreg 130322 = S.bFPRE
  cPOW : c.nreg 130323 = S.bPOW
  cLP : c.nreg 130324 = S.L
  cFSZ : c.nreg 130325 = S.bFSZ
  cUP : c.nreg 130326 = S.bUP
  cUPE : c.nreg 130327 = S.bUP + S.L * S.N
  cN : c.nreg 130328 = S.N
  cL : c.nreg 130345 = S.L
  -- the marks
  mLEV : c.nreg 130601 = S.bLEV
  mUPT : c.nreg 130602 = S.bUPT
  mPOW : c.nreg 130603 = S.bPOW
  mL : c.nreg 130604 = S.L
  mPV : c.nreg 130605 = S.bPV
  mPOS : c.nreg 130606 = S.bPOS
  mDF : c.nreg 130607 = S.bDF
  mμ : c.nreg 130608 = S.μ
  mend : c.nreg 130620 = S.bUPT + S.L * S.μ
  -- the class parameters
  pSO : c.nreg 130632 = S.bSO
  pSF : c.nreg 130633 = S.bSF
  pFPAR : c.nreg 130634 = S.bFPAR
  pPR : c.nreg 130635 = S.bFPRE
  pSZ : c.nreg 130636 = S.bFSZ
  -- the passes
  aTMP : c.nreg 130650 = S.bTMP
  aACT : c.nreg 130651 = S.bACT
  aPOS : c.nreg 130652 = S.bPOS
  aDF : c.nreg 130653 = S.bDF
  aFIRST : c.nreg 130654 = S.bFIRST
  aFPRE : c.nreg 130655 = S.bFPRE
  -- the rest
  rs : c.nreg 130674 = S.s
  rμ : c.nreg 130675 = S.μ
  rFP : c.nreg 130680 = S.bFP
  r2N : c.nreg 130681 = 2 * S.N
  rN : c.nreg 130682 = S.N
  rHALF : c.nreg 130692 = S.bHALF
  rLBOT : c.nreg 130694 = S.bLBOT
  rLTOP : c.nreg 130695 = S.bLTOP
  rVERT : c.nreg 130696 = S.bVERT
  rOPP : c.nreg 130697 = S.bOPP
  rATT : c.nreg 130698 = S.bATT
  rSTK : c.nreg 130700 = S.bSTK
end SS

/-- The registers the split step may write. -/
def SplitRG (r : ℕ) : Prop :=
  r = 130300 ∨ r = 130301 ∨ r = 130302 ∨ (130310 ≤ r ∧ r ≤ 130316) ∨ (130330 ≤ r ∧ r ≤ 130334) ∨
    r = 130340 ∨ ztneg ∨ r = 130600 ∨ (130609 ≤ r ∧ r ≤ 130619) ∨
    (130630 ≤ r ∧ r ≤ 130631) ∨ ztneh ∨ (130656 ≤ r ∧ r ≤ 130661) ∨
    (130550 ≤ r ∧ r ≤ 130556) ∨ (130676 ≤ r ∧ r ≤ 130679) ∨ (130670 ≤ r ∧ r ≤ 130673) ∨
    r = 130690 ∨ r = 130691 ∨ r = 130693 ∨ (130702 ≤ r ∧ r ≤ 130703)
theorem SS.Regs.of_frame {S : SS} {c c' : Config} (h : S.Regs c)
    (hr : ∀ r, ¬ SplitRG r → c'.nreg r = c.nreg r) : S.Regs c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ ztbmk]; assumption)

/-- The median face and the level window. -/
def medB : Stmt := block [.subN 130302 130301 130300, .addN 130690 130692 130302,
  .loadN 130690 130690, .addN 130690 130690 130300, .addN 130691 130320 130690,
  .loadN 130691 130691, .addN 130691 130321 130691, .loadN 130340 130691,
  .addN 130691 130320 130300, .loadN 130691 130691, .addN 130691 130601 130691,
  .loadN 130691 130691, .addN 130693 130694 130691, .loadN 130609 130693,
  .addN 130693 130695 130691, .loadN 130610 130693]

/-! ## The layout in slots -/

/-- **The slot layout**: every array of the split step lives in its own slot of `U` cells above
`A0` (three for the star arrays, two for the stack), the tables above the slots; the input arrays
lie below `A0`. -/
structure SS.Lay (S : SS) (A0 U W : ℕ) : Prop where
  hFIRST : S.bFIRST = A0 + 0 * U
  hLEV : S.bLEV = A0 + 3 * U
  hPV : S.bPV = A0 + 6 * U
  hFP : S.bFP = A0 + 7 * U
  hATT : S.bATT = A0 + 9 * U
  hSO : S.bSO = A0 + 11 * U
  hSF : S.bSF = A0 + 17 * U
  hFPAR : S.bFPAR = A0 + 26 * U
  hFSZ : S.bFSZ = A0 + 28 * U
  hFPRE : S.bFPRE = A0 + 29 * U
  hLBOT : S.bLBOT = A0 + 37 * U
  hLTOP : S.bLTOP = A0 + 38 * U
  hHALF : S.bHALF = A0 + 39 * U
  hPOW : S.bPOW = A0 + 40 * U
  hACT : S.bACT = A0 + 43 * U
  hPOS : S.bPOS = A0 + 44 * U
  hTMP : S.bTMP = A0 + 45 * U
  hSTK : S.bSTK = A0 + 46 * U
  hDF : S.bDF = A0 + 48 * U
  hUPT : S.bUPT = A0 + 54 * U
  hUP : S.bUP = A0 + 54 * U + S.L * U
  hμU : S.μ + 3 ≤ U
  hNU : S.N + 1 ≤ U
  hLU : S.L ≤ U
  hμN : S.μ ≤ S.N + 1
  hVERT : S.bVERT + S.N ≤ A0
  hOPP : S.bOPP + S.N ≤ A0
  hW : A0 + 54 * U + 2 * (S.L * U) ≤ W

/-- The selection predicate of a class pass, in terms of `inClass`. -/
def SelI (m : ℕ → ℕ) (S : SS) (X f i : ℕ) : Prop :=
  m ztzke ≠ 1 ∧
    inClass ztdoi ztdoh ztdoe
      ztdof ztdog 0 X f
      (m ztbapx)
section proofs
variable {P : Polygon} {W : ℕ}

/-- **The median face and the level window.** -/
theorem medB_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c) {lo hi : ℕ}
    (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hwH : S.bHALF + ztcw ≤ W)
    (hwm : S.bACT + ztxgm ≤ W)
    (hwf : S.bFIRST + c.nmem ztbari ≤ W)
    (hwa : S.bACT + lo ≤ W) (hwl : S.bLEV + c.nmem zttcc ≤ W)
    (hwb : S.bLBOT + c.nmem ztdyu ≤ W)
    (hwt : S.bLTOP + c.nmem ztdyu ≤ W) :
    ∃ c' k, Exec P W medB c c' k ∧ k = 16 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130302 = hi - lo ∧
      c'.nreg 130340 = c.nmem (S.bFIRST + c.nmem ztbari) ∧
      c'.nreg 130609 = c.nmem (S.bLBOT + c.nmem ztdyu) ∧
      c'.nreg 130610 = c.nmem (S.bLTOP + c.nmem ztdyu) ∧
      c'.nreg 130300 = lo ∧ c'.nreg 130301 = hi ∧
      ztcqj ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold medB
  exec_block
  all_goals try (config_simp; simp only [hlo, hhi, hR.rHALF, hR.cACT, hR.cFIRST, hR.mLEV,
    hR.rLBOT, hR.rLTOP]; omega)
  refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [hlo, hhi, hR.rHALF, hR.cACT, hR.cFIRST, hR.mLEV,
    hR.rLBOT, hR.rLTOP]; done)
  zumwj; unfold SplitRG at hr; grind
end proofs

/-! ## The corners and their marks -/

/-- The corner `VERT[f]`. -/
def c0B : Stmt := block [.addN 130693 130696 130344, .loadN 130600 130693]
/-- The corner `VERT[OPP[f]]`. -/
def c1B : Stmt := block [.addN 130693 130697 130344, .loadN 130693 130693,
  .addN 130693 130696 130693, .loadN 130600 130693]
/-- The corner `VERT[ATT[f]]`. -/
def c2B : Stmt := block [.addN 130693 130698 130344, .loadN 130693 130693,
  .addN 130693 130696 130693, .loadN 130600 130693]

/-- **The marks of the three corners.** -/
def marksS : Stmt := .seq (.seq c0B markStmt) (.seq (.seq c1B markStmt) (.seq c2B markStmt))

/-- One corner's marks, as a memory transformer. -/
noncomputable def markStep (m : ℕ → ℕ) (S : SS) (lo hi lbot ltop : ℕ) (up : ℕ → ℕ) (u : ℕ) :
    ℕ → ℕ :=
  if lbot ≤ min ztyjl ltop then
    markMem m S.bPOS S.bDF lo hi up (up^[m zteoa - min ztyjl ltop] u)
      (min ztyjl ltop + 1 - lbot)
  else m
theorem markStep_other {m : ℕ → ℕ} {S : SS} {lo hi lbot ltop : ℕ} {up : ℕ → ℕ} {u : ℕ}
    (hup : ∀ x, x < S.μ → up x < S.μ) (hu : u < S.μ) {a : ℕ}
    (ha : ¬ ztbau) : markStep m S lo hi lbot ltop up u a = m a := by
  classical
  unfold markStep
  split_ifs
  · zulup
    zucjw
    rintro ⟨x, rfl, -, -, i', -, rfl⟩
    have := iterate_lt_of hup i' (iterate_lt_of hup (m zteoa - min ztyjl ltop) hu)
    omega
  · rfl
theorem MarkMem.congr {m m' : ℕ → ℕ} {W bLEV bUPT bPOW L bPV bPOS bDF μ : ℕ} {up : ℕ → ℕ}
    (h : MarkMem m W bLEV bUPT bPOW L bPV bPOS bDF μ up)
    (hm : ∀ a, ¬ (bDF ≤ a ∧ a < bDF + μ) → m' a = m a) :
    MarkMem m' W bLEV bUPT bPOW L bPV bPOS bDF μ up := by
  have dLEV := h.dLEV; have dUPT := h.dUPT; have dPOW := h.dPOW; have dPV := h.dPV
  refine ⟨h.up_lt, fun x hx => ?_, fun j hj x hx => ?_, fun j hj => ?_, fun x hx => ?_,
    fun x hx => ?_, h.wLEV, h.wUPT, h.wPOW, h.wPV, h.wPOS, h.wDF, h.dLEV, h.dUPT, h.dPOW, h.dPV,
    h.dPOS⟩
  · zvmzz; exact h.pv x hx
  · have : j * μ + μ ≤ L * μ := by
      have := Nat.mul_le_mul_right μ ztmnx; grind
    zvmzz; exact h.tab j hj x hx
  · zvmzz; exact h.pow j hj
  · zvmzz; exact h.lev_lt x hx
  · zvmzz; exact h.lev_mu x hx
section proofs
variable {P : Polygon} {W : ℕ}

/-- **The three corners and their marks.** -/
theorem marksS_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    {lo hi lbot ltop f : ℕ} {up : ℕ → ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hbot : c.nreg 130609 = lbot) (htop : c.nreg 130610 = ltop) (hf : c.nreg 130344 = f)
    (hM : MarkMem c.nmem W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ up)
    {u0 u1 u2 : ℕ} (hu0 : c.nmem zttcs = u0)
    (hu1 : c.nmem (S.bVERT + c.nmem ztfom) = u1)
    (hu2 : c.nmem (S.bVERT + c.nmem zthcl) = u2)
    (h0 : u0 < S.μ) (h1 : u1 < S.μ) (h2 : u2 < S.μ)
    (hw0 : S.bVERT + f ≤ W) (hw1 : S.bOPP + f ≤ W) (hw2 : S.bATT + f ≤ W)
    (hw1' : S.bVERT + c.nmem ztfom ≤ W) (hw2' : S.bVERT + c.nmem zthcl ≤ W)
    (hd : ∀ a, (a = S.bVERT + f ∨ a = S.bOPP + f ∨ a = S.bATT + f ∨
      a = S.bVERT + c.nmem ztfom ∨ a = S.bVERT + c.nmem zthcl) →
      ¬ ztbau) :
    ∃ c' k, Exec P W marksS c c' k ∧ k ≤ 3 * ztydl ∧
      WordsBounded W c' ∧
      c'.nmem = markStep (markStep (markStep c.nmem S lo hi lbot ltop up u0) S lo hi lbot ltop
        up u1) S lo hi lbot ltop up u2 ∧
      ztcqj ∧ c'.nreg 130344 = f ∧ c'.nreg 130300 = lo ∧
      c'.nreg 130301 = hi ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the marking context in every configuration of the frame
  have ctx : ∀ c1 : Config, ztivu →
      c1.nreg 130300 = lo → c1.nreg 130301 = hi → c1.nreg 130609 = lbot →
      c1.nreg 130610 = ltop →
      MarkCtx c1 lo hi S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ lbot ltop := by
    intro c1 hr h1 h2 h3 h4
    have hR1 := hR.of_frame hr
    exact ⟨hR1.one, hR1.zero, h1, h2, hR1.mLEV, hR1.mUPT, hR1.mPOW, hR1.mL, hR1.mPV, hR1.mPOS,
      hR1.mDF, hR1.mμ, h3, h4, hR1.mend⟩
  have hup := hM.up_lt
  -- a corner block followed by its marks
  have step : ∀ (cb : Stmt) (c1 : Config) (u : ℕ), WordsBounded W c1 →
      ztivu → c1.nreg 130300 = lo →
      c1.nreg 130301 = hi → c1.nreg 130609 = lbot → c1.nreg 130610 = ltop →
      c1.nreg 130344 = f → u < S.μ →
      (∀ a, ¬ ztbau → c1.nmem a = c.nmem a) →
      (∃ c2 k2, Exec P W cb c1 c2 k2 ∧ k2 ≤ 4 ∧ WordsBounded W c2 ∧ c2.nreg 130600 = u ∧
        (∀ r, r ≠ 130600 → r ≠ 130693 → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧
        c2.rmem = c1.rmem ∧ c2.output = c1.output ∧ c2.nmem = c1.nmem) →
      ∃ c3 k3, Exec P W (.seq cb markStmt) c1 c3 k3 ∧
        k3 ≤ 12 * S.L + 12 * ztgkx + 34 ∧ WordsBounded W c3 ∧
        c3.nmem = markStep c1.nmem S lo hi lbot ltop up u ∧
        (∀ r, ¬ SplitRG r → c3.nreg r = c.nreg r) ∧ c3.nreg 130300 = lo ∧
        c3.nreg 130301 = hi ∧ c3.nreg 130609 = lbot ∧ c3.nreg 130610 = ltop ∧
        c3.nreg 130344 = f ∧ c3.rreg = c1.rreg ∧ c3.rmem = c1.rmem ∧ c3.output = c1.output := by
    intro cb c1 u hw1 hr1 h1 h2 h3 h4 h5 hu hm1 ⟨c2, k2, e2, hk2, hw2, h2u, h2r, hrr2, hrm2, ho2,
      hm2⟩
    have hr2 := fun r hr =>
      (h2r r zthc zthc).trans (hr1 r hr)
    have hC2 := ctx c2 hr2 by_grind
      by_grind by_grind
      by_grind
    have hM2 : MarkMem c2.nmem W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ up :=
      hM.congr ztxl
    obtain ⟨c3, k3, e3, hk3, hw3, hm3, h3r, hrr3, hrm3, ho3⟩ := markStmt_exec (P := P) hw2 hC2 hM2
      h2u hu
    refine ⟨c3, k2 + k3, .seq e2 e3, by_omega, hw3, by zuohv; rfl, fun r hr => ?_, ?_, ?_,
      ?_, ?_, ?_, hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2⟩
    · rw [h3r r (by unfold MarkRG; unfold SplitRG at hr; omega)]; grind
    all_goals rw [h3r _ ztqgc, h2r _ by_omega by_omega]; assumption
  have hmr : ∀ (m : ℕ → ℕ), (∀ a, ¬ ztbau → m a = c.nmem a) →
      ∀ u, u < S.μ → ∀ a, ¬ ztbau →
        markStep m S lo hi lbot ltop up u a = c.nmem a := fun m hm u hu a ha => by
    rw [markStep_other hup hu ha]; grind
  -- corner 0
  obtain ⟨c3, k3, e3, hk3, hw3, hm3, hr3, h3lo, h3hi, h3b, h3t, h3f, hrr3, hrm3, ho3⟩ :=
    step c0B c u0 hw ztcj hlo hhi hbot htop hf h0 ztcj (by
      unfold c0B
      exec_block
      · rw [hR.rVERT, hf]; omega
      · refine ⟨by_omega, by_omega, by config_simp; rw [hR.rVERT, hf, hu0], fun r h1 h2 => ?_, rfl, rfl,
          rfl, rfl⟩
        zuncp)
  -- corner 1
  have hm3' : ∀ a, ¬ ztbau → c3.nmem a = c.nmem a := by
    rw [hm3]; exact hmr c.nmem by_omega u0 h0
  have hR3 := hR.of_frame hr3
  obtain ⟨c4, k4, e4, hk4, hw4, hm4, hr4, h4lo, h4hi, h4b, h4t, h4f, hrr4, hrm4, ho4⟩ :=
    step c1B c3 u1 hw3 hr3 h3lo h3hi h3b h3t h3f h1 hm3' (by
      have r1 := hm3' _ (hd _ ztwiz)
      have r2 := hm3' _ (hd _ ztbaje)
      unfold c1B
      exec_block
      all_goals try (config_simp; simp only [hR3.rOPP, hR3.rVERT, h3f, r1]; omega)
      refine ⟨by_omega, by_omega, by config_simp; simp only [hR3.rOPP, hR3.rVERT, h3f, r1, r2, hu1],
        fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      zuncp)
  -- corner 2
  have hm4' : ∀ a, ¬ ztbau → c4.nmem a = c.nmem a := by
    rw [hm4]; exact hmr c3.nmem hm3' u1 h1
  have hR4 := hR.of_frame hr4
  obtain ⟨c5, k5, e5, hk5, hw5, hm5, hr5, h5lo, h5hi, h5b, h5t, h5f, hrr5, hrm5, ho5⟩ :=
    step c2B c4 u2 hw4 hr4 h4lo h4hi h4b h4t h4f h2 hm4' (by
      have r1 := hm4' _ (hd _ ztbajm)
      have r2 := hm4' _ (hd _ ztbakw)
      unfold c2B
      exec_block
      all_goals try (config_simp; simp only [hR4.rATT, hR4.rVERT, h4f, r1]; omega)
      refine ⟨by_omega, by_omega, by config_simp; simp only [hR4.rATT, hR4.rVERT, h4f, r1, r2, hu2],
        fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      zuncp)
  refine ⟨c5, k3 + zttqj, .seq e3 ztncj, by_omega, hw5, by rw [hm5, hm4, hm3], hr5,
    h5f, h5lo, h5hi, by rw [hrr5, hrr4, hrr3], by rw [hrm5, hrm4, hrm3], by rw [ho5, ho4, ho3]⟩

/-- A class pass: the class parameters of `X`, then the pass. -/
def classPass : Stmt := .seq cpStmt passStmt

/-- The pass memory facts from the slot layout. -/
theorem SS.Lay.passMem {S : SS} {A0 U W : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {lo hi : ℕ}
    (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m ztid < S.μ)
    (hfirst : ∀ v, v < S.μ → m ztbgv < S.N) :
    PassMem m W lo hi S.bTMP S.bACT S.bPOS S.bDF S.bFIRST S.bFPRE S.μ S.N := by
  have := hL.hFIRST; have := hL.hFPRE; have := hL.hACT; have := hL.hPOS; have := hL.hTMP
  have := hL.hDF; have := hL.hμU; have := hL.hNU; have := hL.hW
  zujvs
  refine ⟨hlh, hit, hfirst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

/-- **A class pass.** -/
theorem classPass_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    (hL : S.Lay A0 U W) {lo hi X f e : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hX : c.nreg 130630 = X) (hf : c.nreg 130631 = f) (he : c.nreg 130656 = e)
    (hXN : X < 3 * S.N) (hfN : f < S.N)
    (hCp : CpMem c.nmem W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → c.nmem ztid < S.μ)
    (hfirst : ∀ v, v < S.μ → c.nmem ztbgv < S.N) (hloe : lo ≤ e)
    (hfin : (passMem c.nmem ztjms S.bACT S.bPOS S.bTMP lo e ztcw).2 ≤ hi) :
    ∃ c' k, Exec P W classPass c c' k ∧ k ≤ 32 * ztcw + 48 ∧ WordsBounded W c' ∧
      c'.nmem = (passMem c.nmem ztjms S.bACT S.bPOS S.bTMP lo e ztcw).1 ∧
      c'.nreg 130656 = (passMem c.nmem ztjms S.bACT S.bPOS S.bTMP lo e
        ztcw).2 ∧
      (∀ r, ¬ ztpwx → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hr1, hrr1, hrm1, ho1, htest⟩ := cpStmt_exec (P := P) hw
    hR.zero hX hf hR.pSO hR.pSF hR.pFPAR hR.pPR hR.pSZ hCp hXN hfN
  have hsel : SelP c.nmem S.bTMP S.bDF S.bFIRST S.bFPRE ztvkg ztvkh
      ztvki = SelI c.nmem S X f := by
    funext i
    unfold SelP SelI
    simp_all
  have r1 := hr1
  have hC : PassCtx c1 lo hi ztvkg ztvkh ztvki S.bTMP S.bACT
      S.bPOS S.bDF S.bFIRST S.bFPRE := by
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      zuoie
    exacts [hR.one, hR.zero, hlo, hhi, hR.aTMP, hR.aACT, hR.aPOS, hR.aDF, hR.aFIRST, hR.aFPRE]
  have hPM := hL.passMem (m := c1.nmem) hlh hhiμ by_simp_all
    by_simp_all
  rw [← hm1] at hsel
  obtain ⟨c2, k2, e2, hk2, hw2, hm2, hp2, hr2, hrr2, hrm2, ho2⟩ := passStmt_exec (P := P) hw1 hC hPM
    hloe (by zuoie; exact he) by_simp_all
  refine ⟨c2, k1 + k2, .seq e1 e2, by_omega, hw2, by_simp_all, by_simp_all,
    fun r hr => ?_, hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
  simp_all

/-- **The selection only reads the static arrays, `TMP` and `DF`.** -/
theorem SelI_congr {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m m' : ℕ → ℕ}
    (hCp : CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N) {lo hi X f : ℕ}
    (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m ztid < S.μ)
    (hfirst : ∀ v, v < S.μ → m ztbgv < S.N) (hXN : X < 3 * S.N) (hfN : f < S.N)
    (hm : ∀ a, ¬ ztbvl → ¬ ztbvm →
      m' a = m a) :
    ∀ i, lo ≤ i → i < hi → ztihq := by
  zusx
  have := hL.hFIRST; have := hL.hFPRE; have := hL.hACT; have := hL.hPOS; have := hL.hTMP
  have := hL.hDF; have := hL.hμU; have := hL.hNU; have := hL.hSO; have := hL.hSF
  have := hL.hFPAR; have := hL.hFSZ
  zuesl
  have e1 : m' _ = m ztid := hm _ by_omega by_omega
  have e2 : m' _ = m ztzke := hm _ by_omega by_omega
  have hfv := hfirst _ hv
  have e3 : m' _ = m ztyea :=
    hm _ by_omega by_omega
  have e4 : m' _ =
      m ztbapx := hm _ by_omega by_omega
  have hso := hCp.so_lt X hXN
  have e5 : m' _ = m zthcm := hm _ by_omega by_omega
  have hsf := hCp.sf_lt _ hso
  have e6 : m' _ = m (S.bSF + m zthcm) := hm _ by_omega by_omega
  have e7 : ∀ g, g < S.N → m' _ = m ztnoz ∧
      m' _ = m ztjmk ∧ m' _ = m ztnpa := fun g hg =>
    ⟨hm _ by_omega by_omega, hm _ by_omega by_omega, hm _ by_omega by_omega⟩
  obtain ⟨g1, g2, g3⟩ := e7 _ hsf
  obtain ⟨f1, f2, f3⟩ := e7 f hfN
  have hfp := hCp.fp_lt f hfN
  have e8 : m' _ = m (S.bSO + m zttce) :=
    hm _ by_omega by_omega
  unfold SelI inClass
  simp only [e1, e2, e3, e4, e5, e6, g1, g2, g3, f1, f2, f3, e8]
theorem CpMem.congr_lay {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m m' : ℕ → ℕ}
    (hCp : CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hm : ∀ a, ¬ ztbvl → ¬ ztbvm →
      m' a = m a) : CpMem m' W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N := by
  have := hL.hFPRE; have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hNU
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ
  refine ⟨hCp.wSO, hCp.wSF, hCp.wFP, hCp.wPR, hCp.wSZ, fun x hx => ?_, fun x hx => ?_,
    fun g hg => ?_, fun g hg => ?_⟩
  · zunjn; exact hCp.so_lt x hx
  · zunjn; exact hCp.sf_lt x hx
  · zunjn; exact hCp.fp_lt g hg
  · rw [hm _ by_omega by_omega, hm _ by_omega by_omega]; exact hCp.prsz g hg

/-- A pass keeps everything outside `ACT` and `POS`. -/
theorem passMem_out {S : SS} {A0 U : ℕ} (_hL : S.Lay A0 U W) {m : ℕ → ℕ} {sel : ℕ → Prop}
    {lo hi e : ℕ} (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m ztid < S.μ)
    (hle : e + cntS sel lo hi ≤ hi) (hlh : lo ≤ hi) :
    ∀ a, ¬ ztbvl → ¬ ztbvm →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e ztcw).1 a = m a := by
  zujau
  refine passMem_other m sel _ by_simp_all ⟨fun h => h1 ?_, h2⟩
  rw [passMem_ptr_eq, show lo + ztcw = hi by omega] at h
  omega

/-- The three class passes. -/
def pB0 : Stmt := block [.copyN 130656 130300, .copyN 130670 130656, .copyN 130630 130344,
  .copyN 130631 130344]
/-- The dart `2N + FP[f]`. -/
def pB1 : Stmt := block [.copyN 130671 130656, .addN 130693 130680 130344, .loadN 130693 130693,
  .addN 130630 130681 130693]
/-- The dart `N + f`. -/
def pB2 : Stmt := block [.copyN 130672 130656, .addN 130630 130682 130344]
/-- The end of the last class. -/
def pB3 : Stmt := .instr (.copyN 130673 130656)

/-- **The three class passes.** -/
def passesS : Stmt := .seq pB0 (.seq classPass (.seq pB1 (.seq classPass (.seq pB2
  (.seq classPass pB3)))))

/-- The memories of the three passes. -/
noncomputable def passA (m : ℕ → ℕ) (S : SS) (lo hi f : ℕ) : ztjx × ℕ :=
  passMem m ztqcn S.bACT S.bPOS S.bTMP lo lo ztcw
/-- The second pass. -/
noncomputable def passB (m : ℕ → ℕ) (S : SS) (lo hi f : ℕ) : ztjx × ℕ :=
  passMem (passA m S lo hi f).1 ztbape S.bACT S.bPOS S.bTMP lo
    (passA m S lo hi f).2 ztcw
/-- The third pass. -/
noncomputable def passC (m : ℕ → ℕ) (S : SS) (lo hi f : ℕ) : ztjx × ℕ :=
  passMem (passB m S lo hi f).1 ztzdb S.bACT S.bPOS S.bTMP lo
    (passB m S lo hi f).2 ztcw

/-- **The three class passes.** -/
theorem passesS_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    (hL : S.Lay A0 U W) {lo hi f : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hf : c.nreg 130344 = f) (hfN : f < S.N) (hfp : c.nmem ztwk < S.N)
    (hCp : CpMem c.nmem W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → c.nmem ztid < S.μ)
    (hfirst : ∀ v, v < S.μ → c.nmem ztbgv < S.N)
    (hsum : cntS ztges lo hi + cntS ztwxt
      lo hi + cntS ztzda lo hi ≤ hi - lo) :
    ∃ c' k, Exec P W passesS c c' k ∧ k ≤ 3 * ztzbe + 20 ∧ WordsBounded W c' ∧
      c'.nmem = (passC c.nmem S lo hi f).1 ∧ c'.nreg 130670 = lo ∧
      c'.nreg 130671 = lo + cntS ztges lo hi ∧
      c'.nreg 130672 = lo + cntS ztges lo hi +
        cntS ztwxt lo hi ∧
      c'.nreg 130673 = lo + cntS ztges lo hi +
        cntS ztwxt lo hi +
        cntS ztzda lo hi ∧
      ztcqj ∧ c'.nreg 130344 = f ∧ c'.nreg 130300 = lo ∧
      c'.nreg 130301 = hi ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set m := c.nmem with hmdef
  set X1 := 2 * S.N + m ztwk
  set sl0 := SelI m S f f
  set sl1 := SelI m S X1 f
  set sl2 := SelI m S ztbpq f
  have := hL.hFP; have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hNU
  have := hL.hTMP; have := hL.hFIRST; have := hL.hW
  have hfr : ∀ (c1 c2 : Config), (∀ r, ¬ ztpwx → c2.nreg r = c1.nreg r) →
      ∀ r, ¬ SplitRG r → c2.nreg r = c1.nreg r := fun c1 c2 h r hr =>
    h r (by unfold CpRG PassRG; unfold SplitRG at hr; omega)
  -- the congruences for memories changed only in `ACT` and `POS`
  have transfer : ∀ m' : ℕ → ℕ, (∀ a, ¬ ztbvl →
      ¬ ztbvm → m' a = m a) →
      CpMem m' W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N ∧
      (∀ i, lo ≤ i → i < hi → m' ztid < S.μ) ∧
      (∀ v, v < S.μ → m' ztbgv < S.N) ∧ m' ztwk = m ztwk ∧
      ∀ X, X < 3 * S.N → ∀ i, lo ≤ i → i < hi → ztihq := by
    zubxa
    refine ⟨CpMem.congr_lay hL hCp hm', fun i h1 h2 => ?_, fun v hv => ?_, by_grind, fun X hX => SelI_congr hL hCp hhiμ hit hfirst hX hfN hm'⟩
    · grind
    grind
  have hX1 : X1 < 3 * S.N := by_grind
  have hs0 : lo + cntS sl0 lo hi ≤ hi := by_omega
  have hs1 : lo + cntS sl0 lo hi + cntS sl1 lo hi ≤ hi := by_omega
  have hs2 : lo + cntS sl0 lo hi + cntS sl1 lo hi + cntS sl2 lo hi ≤ hi := by_omega
  have hX2 : S.N + f < 3 * S.N := by_omega
  have hsp : ∀ (sel : ℕ → Prop) (m' : ℕ → ℕ) (e : ℕ),
      (passMem m' sel S.bACT S.bPOS S.bTMP lo e ztcw).2 = e + cntS sel lo hi := by
    intro sel m' e
    zuezb
  -- block 0
  obtain ⟨c1, k1, e1, hk1, hw1, h1a, h1b, h1c, h1d, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      pB0 c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 130656 = lo ∧ c1.nreg 130670 = lo ∧
      c1.nreg 130630 = f ∧ c1.nreg 130631 = f ∧
      (∀ r, r ≠ 130656 → r ≠ 130670 → r ≠ 130630 → r ≠ 130631 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    unfold pB0
    exec_block
    refine ⟨rfl, by_omega, by_tauto, by_tauto, by_tauto,
      by tauto, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
    zueeo
  have hR1 := hR.of_frame (fun r hr => h1r r zthc
    zthc zthc
    zthc)
  have g1 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 → c1.nreg r = c.nreg r := by_grind
  -- pass 0
  obtain ⟨c2, k2, e2, hk2, hw2, hm2, hp2, hr2, hrr2, hrm2, ho2⟩ := classPass_exec (P := P) hw1 hR1
    hL by_grind by_grind h1c h1d h1a
    by_omega hfN by_grind hlh hhiμ by_grind
    by_grind le_rfl by_grind
  zvmxz at hm2 hp2
  rw [hsp] at hp2
  have hA : (passA m S lo hi f).2 = lo + cntS sl0 lo hi := by unfold passA; rw [hsp]
  have hm2' := hm2
  have hout1 : ∀ a, ¬ ztbvl → ¬ ztbvm →
      c2.nmem a = m a := by
    rw [hm2]; exact passMem_out hL hhiμ hit hs0 hlh
  obtain ⟨cp1, it1, fi1, fp1, se1⟩ := transfer _ hout1
  have hR2 := hR1.of_frame (hfr c1 c2 hr2)
  have g2 :=
    fun r hr => hr2 r ztcyw
  -- block 1
  obtain ⟨c3, k3, e3, hk3, hw3, h3a, h3b, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
      pB1 c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧ c3.nreg 130671 = lo + cntS sl0 lo hi ∧
      c3.nreg 130630 = X1 ∧
      (∀ r, r ≠ 130671 → r ≠ 130693 → r ≠ 130630 → c3.nreg r = c2.nreg r) ∧
      c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
    have hf2 : c2.nreg 130344 = f := by rw [g2 _ by_omega, g1 _ by_omega]; exact hf
    unfold pB1
    exec_block
    all_goals try (config_simp; zunnu; omega)
    refine ⟨rfl, by_omega, by config_simp; omega, by
      config_simp; zunnu; rfl, fun r h1 h2 h3 => ?_, rfl, rfl,
      rfl, rfl⟩
    simp only [Machine.upd_apply, h1, h2, h3, ite_false]
  have hR3 := hR2.of_frame (fun r hr => h3r r zthc
    zthc zthc)
  have g3 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 ∨ r = 130656 →
      c3.nreg r = c2.nreg r := fun r hr => h3r r by_omega by_omega by_omega
  -- pass 1
  have hsel1 : ∀ i, lo ≤ i → i < lo + ztcw → (SelI c2.nmem S X1 f i ↔ sl1 i) :=
    fun i h1 h2 => se1 X1 hX1 i h1 by_omega
  have hpc1 := passMem_congr_sel (m0 := c2.nmem) (bACT := S.bACT) (bPOS := S.bPOS)
    (bTMP := S.bTMP) (e := lo + cntS sl0 lo hi) _ hsel1
  have hcnt1 : cntS _ lo hi = cntS sl1 lo hi :=
    cntS_congr (fun i h1 h2 => hsel1 i h1 by_omega)
  obtain ⟨c4, k4, e4, hk4, hw4, hm4, hp4, hr4, hrr4, hrm4, ho4⟩ := classPass_exec (P := P)
    (lo := lo) (hi := hi) (X := X1) (f := f) (e := lo + cntS sl0 lo hi) hw3 hR3 hL ztgfr
    ztgfr h3b
    (by rw [h3r _ by_omega by_omega by_omega, hr2 _ ztcyw]; omega)
    (by rw [g3 _ by_omega]; omega) hX1 hfN by_grind hlh hhiμ
    ztntw ztntw by_omega
    (by rw [hm3, hsp, hcnt1]; omega)
  rw [hm3, hpc1] at hm4 hp4
  rw [hsp] at hp4
  have hm4' : c4.nmem = (passB m S lo hi f).1 := by rw [hm4, hm2', ← hA]; rfl
  have hout2 : ∀ a, ¬ ztbvl → ¬ ztbvm →
      c4.nmem a = m a := by
    zujau
    rw [hm4, passMem_out hL hhiμ it1 by_omega hlh a h1 h2]
    exact hout1 a h1 h2
  obtain ⟨cp2, it2, fi2, fp2, se2⟩ := transfer _ hout2
  have hR4 := hR3.of_frame (hfr c3 c4 hr4)
  have g4 := fun r hr => hr4 r ztcyw
  -- block 2
  obtain ⟨c5, k5, e5, hk5, hw5, h5a, h5b, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
      pB2 c4 c5 k5 ∧ k5 = 2 ∧ WordsBounded W c5 ∧
      c5.nreg 130672 = lo + cntS sl0 lo hi + cntS sl1 lo hi ∧ c5.nreg 130630 = S.N + f ∧
      (∀ r, r ≠ 130672 → r ≠ 130630 → c5.nreg r = c4.nreg r) ∧
      c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output ∧ c5.nmem = c4.nmem := by
    have hf4 : c4.nreg 130344 = f := by
      rw [g4 _ by_omega, g3 _ by_omega, g2 _ by_omega, g1 _ by_omega]; exact hf
    unfold pB2
    exec_block
    · config_simp; zuoif; omega
    · refine ⟨rfl, by_omega, by config_simp; omega, by config_simp; zuoif,
        fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      zughc
  have hR5 := hR4.of_frame (fun r hr => h5r r zthc
    zthc)
  have g5 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 ∨ r = 130671 ∨ r = 130656 →
      c5.nreg r = c4.nreg r := fun r hr => h5r r by_omega by_omega
  -- pass 2
  have hsel2 : ∀ i, lo ≤ i → i < lo + ztcw → (SelI c4.nmem S _ f i ↔ sl2 i) :=
    fun i h1 h2 => se2 _ hX2 i h1 by_omega
  have hpc2 := passMem_congr_sel (m0 := c4.nmem) (bACT := S.bACT) (bPOS := S.bPOS)
    (bTMP := S.bTMP) (e := lo + cntS sl0 lo hi + cntS sl1 lo hi) _ hsel2
  have hcnt2 : cntS _ lo hi = cntS sl2 lo hi :=
    cntS_congr (fun i h1 h2 => hsel2 i h1 by_omega)
  obtain ⟨c6, k6, e6, hk6, hw6, hm6, hp6, hr6, hrr6, hrm6, ho6⟩ := classPass_exec (P := P)
    (lo := lo) (hi := hi) (X := S.N + f) (f := f) (e := lo + cntS sl0 lo hi + cntS sl1 lo hi)
    hw5 hR5 hL (by rw [g5 _ by_omega, g4 _ by_omega, g3 _ by_omega, g2 _ by_omega,
      g1 _ by_omega]; omega)
    (by rw [g5 _ by_omega, g4 _ by_omega, g3 _ by_omega, g2 _ by_omega, g1 _ by_omega]; omega)
    h5b
    (by rw [h5r _ by_omega by_omega, hr4 _ ztcyw,
      h3r _ by_omega by_omega by_omega, hr2 _ ztcyw]; omega)
    (by rw [g5 _ by_omega]; omega) hX2 hfN zthev hlh hhiμ
    zthev zthev by_omega
    (by rw [hm5, hsp, hcnt2]; omega)
  rw [hm5, hpc2] at hm6 hp6
  rw [hsp] at hp6
  have hB : (passB m S lo hi f).2 = lo + cntS sl0 lo hi + cntS sl1 lo hi := by
    unfold passB; rw [hsp, hA]
  have hm6' : c6.nmem = (passC m S lo hi f).1 := by rw [hm6, hm4', ← hB]; rfl
  have hR6 := hR5.of_frame (hfr c5 c6 hr6)
  have g6 := fun r hr => hr6 r ztcyw
  -- block 3
  have e7 := Exec.copyN (P := P) hw6 130673 130656
  have kk6 : ∀ r, r ≠ 130673 → upd c6.nreg 130673 (c6.nreg 130656) r = c6.nreg r :=
    fun r hr => Machine.upd_other _ _ _ hr
  have r344 : c6.nreg 130344 = f := by
    rw [g6 _ by_omega, g5 _ by_omega, g4 _ by_omega, g3 _ by_omega, g2 _ by_omega,
      g1 _ by_omega]; exact hf
  have r300 : c6.nreg 130300 = lo := by
    rw [g6 _ by_omega, g5 _ by_omega, g4 _ by_omega, g3 _ by_omega, g2 _ by_omega,
      g1 _ by_omega]; omega
  have r301 : c6.nreg 130301 = hi := by
    rw [g6 _ by_omega, g5 _ by_omega, g4 _ by_omega, g3 _ by_omega, g2 _ by_omega,
      g1 _ by_omega]; omega
  have r670 : c6.nreg 130670 = lo := by
    rw [g6 _ by_omega, g5 _ by_omega, g4 _ by_omega, g3 _ by_omega, g2 _ by_omega]
    omega
  have r671 : c6.nreg 130671 = lo + cntS sl0 lo hi := by
    rw [g6 _ by_omega, g5 _ by_omega, g4 _ by_omega]; omega
  have r672 : c6.nreg 130672 = lo + cntS sl0 lo hi + cntS sl1 lo hi := by
    zunfs; omega
  have hframe : ∀ r, ¬ SplitRG r → c6.nreg r = c.nreg r := fun r hr => by
    rw [hfr c5 c6 hr6 r hr, h5r r zthc zthc,
      hfr c3 c4 hr4 r hr, h3r r zthc zthc
      zthc, hfr c1 c2 hr2 r hr, h1r r zthc
      zthc zthc
      zthc]
  zumqc
  refine ⟨_, 4 + (k2 + (4 + (k4 + (2 + zttql)))), .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
    ztsqa)))), by_omega, e7.wb_right, hm6', by dsimp only; zunat; omega,
    by dsimp only; zunat; omega,
    by dsimp only; zunat; omega,
    by dsimp only; zumzo; rw [hp6], fun r hr => by
      dsimp only; rw [kk6 r zthc]; exact hframe r hr,
    by dsimp only; zunat; omega, by dsimp only; zunat; omega,
    by dsimp only; zunat; omega, ?_, ?_, ?_⟩
  · show c6.rreg = c.rreg; rw [hrr6, hrr5, hrr4, hrr3, hrr2, hrr1]
  · show c6.rmem = c.rmem; rw [hrm6, hrm5, hrm4, hrm3, hrm2, hrm1]
  · show c6.output = c.output; rw [ho6, ho5, ho4, ho3, ho2, ho1]

/-- Copy the segment to `TMP`. -/
def copyS : Stmt := .seq (block [.addN 130550 130650 130300, .addN 130551 130320 130300,
  .subN 130552 130301 130300, .copyN 130553 130009]) shStmt

/-- **Copy the segment to `TMP`.** -/
theorem copyS_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    (hL : S.Lay A0 U W) {lo hi : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) :
    ∃ c' k, Exec P W copyS c c' k ∧ k ≤ 8 * ztcw + 7 ∧ WordsBounded W c' ∧
      (∀ a, c'.nmem a = if S.bTMP + lo ≤ a ∧ a < S.bTMP + hi then
        c.nmem ztnoy else c.nmem a) ∧
      ztcqj ∧
      (∀ r, r = 130300 ∨ r = 130301 ∨ r = 130302 ∨ r = 130344 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hL.hACT; have := hL.hTMP; have := hL.hμU; have := hL.hW
  zujvs
  obtain ⟨c1, k1, e1, hk1, hw1, h1o, h1i, h1n, h1a, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130550 130650 130300, .addN 130551 130320 130300, .subN 130552 130301 130300,
        .copyN 130553 130009]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧
      c1.nreg 130550 = S.bTMP + lo ∧ c1.nreg 130551 = S.bACT + lo ∧ c1.nreg 130552 = hi - lo ∧
      c1.nreg 130553 = 0 ∧ (∀ r, r ≠ 130550 → r ≠ 130551 → r ≠ 130552 → r ≠ 130553 →
        c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧
      c1.nmem = c.nmem := by
    exec_block
    all_goals try (config_simp; simp only [hR.aTMP, hR.cACT, hlo]; omega)
    refine ⟨rfl, by_omega, by config_simp; simp only [hR.aTMP, hlo], by
      config_simp; simp only [hR.cACT, hlo], by_simp_all, by
      config_simp; exact hR.zero, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
    simp_all
  have h11 := (h1r _ by_omega by_omega by_omega by_omega).trans hR.one
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hm2⟩ := shStmt_exec (P := P) hw1 h11 h1o h1i h1n h1a
    by_omega by_omega by_omega (fun i hi => by have := hw1.2 (S.bACT + lo + i); omega)
  refine ⟨c2, k1 + k2, .seq e1 e2, by_omega, hw2, fun a => ?_, fun r hr => ?_, fun r hr => ?_,
    by rw [hf2.2.1, hrr1], by rw [hf2.2.2.1, hrm1], by rw [hf2.2.2.2.1, ho1]⟩
  · split_ifs with ha
    · have := hm2 (a - (S.bTMP + lo)) by_omega
      grind
    · rw [hf2.2.2.2.2 a by_omega, hm1]
  · rw [hf2.1 r (by unfold ArrRG; unfold SplitRG at hr; omega)]
    exact h1r r zthc zthc
      zthc zthc
  · rw [hf2.1 r ztxf]
    grind

/-- Push the large classes. -/
def pushS : Stmt := .seq (pushOne 0) (.seq (pushOne 1) (pushOne 2))

/-- One push, as a function of the memory and the stack top. -/
noncomputable def pushF (bS s a b : ℕ) (q : ztjx × ℕ) : ztjx × ℕ :=
  if s < b - a then (upd ztgmr ztjoh b, q.2 + 2) else q
theorem pushF_snd_le (bS s a b : ℕ) (q : ztjx × ℕ) : (pushF bS s a b q).2 ≤ q.2 + 2 := by
  unfold pushF; grind

/-- **Push the large classes.** -/
theorem pushS_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    {e0 e1 e2 e3 tp : ℕ} (h0 : c.nreg 130670 = e0) (h1 : c.nreg 130671 = e1)
    (h2 : c.nreg 130672 = e2) (h3 : c.nreg 130673 = e3) (htp : c.nreg 130701 = tp)
    (hwS : S.bSTK + tp + 6 ≤ W) :
    ∃ c' k, Exec P W pushS c c' k ∧ k ≤ 27 ∧ WordsBounded W c' ∧
      ztrlc = pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2
        (pushF S.bSTK S.s e0 e1 (c.nmem, tp))) ∧
      ztfjm ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have step : ∀ (t : ℕ) (c1 : Config) (a b : ℕ), t < 3 → WordsBounded W c1 →
      (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130703 → c1.nreg r = c.nreg r) →
      c1.nreg ztekj = a → c1.nreg ztekk = b → S.bSTK + c1.nreg 130701 + 2 ≤ W →
      ∃ c2 k2, Exec P W ztwbz c1 c2 k2 ∧ k2 ≤ 9 ∧ WordsBounded W c2 ∧
        (c2.nmem, c2.nreg 130701) = pushF S.bSTK S.s a b ztrmp ∧
        ztfjn ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    intro t c1 a b ht hw1 hr1 ha hb hwS1
    obtain ⟨c2, k2, e2, hk2, hw2, hm2, htp2, hr2, hrr2, hrm2, ho2⟩ := pushOne_exec (P := P) hw1 t ht
      ((hr1 _ by_omega by_omega by_omega).trans hR.one) ha hb
      ((hr1 _ by_omega by_omega by_omega).trans hR.rs)
      ((hr1 _ by_omega by_omega by_omega).trans hR.rSTK) rfl hwS1
    refine ⟨c2, k2, e2, hk2, hw2, ?_, by_simp_all,
      hrr2, hrm2, ho2⟩
    unfold pushF
    grind
  obtain ⟨c1, k1, x1, hk1, hw1, hq1, hr1, hrr1, hrm1, ho1⟩ := step 0 c e0 e1 by_omega hw
    ztcnd h0 h1 by_omega
  have hq1' := pushF_snd_le S.bSTK S.s e0 e1 (c.nmem, c.nreg 130701)
  rw [← hq1] at hq1'
  simp only at hq1'
  obtain ⟨c2, k2, x2, hk2, hw2, hq2, hr2, hrr2, hrm2, ho2⟩ := step 1 c1 e1 e2 by_omega hw1 hr1
    by_grind
    by_grind by_omega
  have hq2' := pushF_snd_le S.bSTK S.s e1 e2 ztrmp
  rw [← hq2] at hq2'
  simp only at hq2'
  obtain ⟨c3, k3, x3, hk3, hw3, hq3, hr3, hrr3, hrm3, ho3⟩ := step 2 c2 e2 e3 by_omega hw2 hr2
    by_grind
    by_grind by_omega
  refine ⟨c3, k1 + ztdve, .seq x1 (.seq x2 x3), by_omega, hw3, ?_, hr3, by_grind,
    by grind, by_grind⟩
  grind
end proofs
def StaticEq (A0 U : ℕ) (m m' : ℕ → ℕ) : Prop :=
  ∀ a, (a < A0 + 43 * U ∨ A0 + 49 * U ≤ a) → m' a = m a
theorem StaticEq.refl (A0 U : ℕ) (m : ℕ → ℕ) : StaticEq A0 U m m := fun _ _ => rfl
theorem StaticEq.trans {A0 U : ℕ} {m1 m2 m3 : ℕ → ℕ} (h1 : StaticEq A0 U m1 m2)
    (h2 : StaticEq A0 U m2 m3) : StaticEq A0 U m1 m3 := fun a ha => (h2 a ha).trans (h1 a ha)
section
variable {W : ℕ} {S : SS} {A0 U : ℕ}
theorem CpMem.of_static (hL : S.Lay A0 U W) {m m' : ℕ → ℕ} (h : StaticEq A0 U m m')
    (hCp : CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N) :
    CpMem m' W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N := by
  have := hL.hFPRE; have := hL.hμU; have := hL.hNU
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ
  refine ⟨hCp.wSO, hCp.wSF, hCp.wFP, hCp.wPR, hCp.wSZ, fun x hx => ?_, fun x hx => ?_,
    fun g hg => ?_, fun g hg => ?_⟩
  · zunnv; exact hCp.so_lt x hx
  · zunnv; exact hCp.sf_lt x hx
  · zunnv; exact hCp.fp_lt g hg
  · rw [h _ by_omega, h _ by_omega]; exact hCp.prsz g hg
end

/-- The marks of the three corners of `f`, as a memory. -/
noncomputable def marksF (m0 : ℕ → ℕ) (S : SS) (lo hi lbot ltop : ℕ) (up : ℕ → ℕ) (f : ℕ) :
    ℕ → ℕ :=
  markStep (markStep (markStep m0 S lo hi lbot ltop up (m0 zttcs)) S lo hi lbot ltop up
    (m0 ztzkg)) S lo hi lbot ltop up (m0 (S.bVERT + m0 (S.bATT + f)))

/-- The copy of the segment to `TMP`. -/
def copyF (m1 : ℕ → ℕ) (S : SS) (lo hi : ℕ) : ℕ → ℕ := fun a =>
  if S.bTMP + lo ≤ a ∧ a < S.bTMP + hi then m1 ztnoy else m1 a

/-- The split counter. -/
def nspI : Stmt := .instr (.addN 130704 130704 130001)

/-- **The tail of the split step.** -/
def splitTail : Stmt := .seq marksS (.seq copyS (.seq passesS (.seq sepStmt (.seq pushS nspI))))

/-- A pass does not touch `TMP`. -/
theorem passMem_tmp {W : ℕ} {S : SS} {A0 U : ℕ} (_hL : S.Lay A0 U W) {m0 : ℕ → ℕ}
    {sel : ℕ → Prop} {lo hi e : ℕ} (hhi : hi ≤ S.μ) (he : e ≤ hi)
    (hit : ∀ i, lo ≤ i → i < hi → m0 ztid < S.μ) {x : ℕ}
    (hx : ¬ ztjmg ∧ ¬ ztclw) :
    (passMem m0 sel S.bACT S.bPOS S.bTMP lo e ztcw).1 x = m0 x := by
  have := passMem_ptr m0 sel S.bACT S.bPOS S.bTMP lo e ztcw
  refine passMem_other m0 sel ztcw (fun i a b => hit i a by_omega) ⟨fun h => hx.1 ?_, hx.2⟩
  omega
theorem passC_tmp {W : ℕ} {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {lo hi f : ℕ}
    (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m ztid < S.μ) {x : ℕ}
    (hx : ¬ ztjmg ∧ ¬ ztclw)
    (hsum : (passB m S lo hi f).2 ≤ hi ∧ (passA m S lo hi f).2 ≤ hi) :
    (passC m S lo hi f).1 x = m x := by
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hμU
  have tA : ztxav :=
    fun i h1 h2 => passMem_tmp hL hhi hlh hit ztgy
  have tB : ztxaw := by
    zusx
    unfold passB
    rw [passMem_tmp hL hhi hsum.2 ztfhi
      ⟨by_omega, by_omega⟩]
    simp_all
  unfold passC
  rw [passMem_tmp hL hhi hsum.1 ztfhi hx]
  unfold passB
  rw [passMem_tmp hL hhi hsum.2 ztfhi hx]
  exact passMem_tmp hL hhi hlh hit hx
section proofs
variable {P : Polygon} {W : ℕ}

/-- **The tail of the split step.** -/
theorem splitTail_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : S.Regs c) (hL : S.Lay A0 U W) {lo hi lbot ltop f tp nsp : ℕ} {up : ℕ → ℕ}
    (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi) (hbot : c.nreg 130609 = lbot)
    (htop : c.nreg 130610 = ltop) (hf : c.nreg 130344 = f) (htp : c.nreg 130701 = tp)
    (hnsp : c.nreg 130704 = nsp) (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) (hfN : f < S.N)
    (hM : MarkMem c.nmem W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ up)
    (hvert : ∀ d, d < S.N → c.nmem ztnpd < S.μ)
    (hopp : c.nmem ztfom < S.N) (hatt : c.nmem zthcl < S.N)
    (hCp : CpMem c.nmem W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hfp : c.nmem ztwk < S.N) (hfirst : ∀ v, v < S.μ → c.nmem ztbgv < S.N)
    (hact : ∀ i, lo ≤ i → i < hi → c.nmem ztde < S.μ)
    (hsum : let m2 := copyF ztftf S lo hi
      cntS ztqco lo hi + cntS ztbapf lo hi +
        cntS ztzdc lo hi ≤ hi - lo)
    (hwS : S.bSTK + tp + 6 ≤ W) (hnspW : nsp + 1 ≤ W) :
    let m2 := copyF ztftf S lo hi
    let s0 := SelI m2 S f f
    let s1 := SelI m2 S ztwmt f
    let s2 := SelI m2 S ztbpq f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    ∃ c' k, Exec P W splitTail c c' k ∧
      k ≤ 3 * ztydl + 8 * ztcw + 7 +
        (3 * ztzbe + 20) + (15 * ztcw + 3) + 27 + 1 ∧ WordsBounded W c' ∧
      ztrlc = pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2
        (pushF S.bSTK S.s lo e1 (sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo
          ztcw, tp))) ∧
      c'.nreg 130704 = nsp + 1 ∧ (∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 →
        c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro m2 s0 s1 s2 e1 e2 e3
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU
  have := hL.hNU; have := hL.hVERT; have := hL.hOPP; have := hL.hATT; have := hL.hW
  have := hL.hFIRST; have := hL.hLEV; have := hL.hPV; have := hL.hFP; have := hL.hSTK
  have := hL.hμN
  zuiwl
  -- the marks
  obtain ⟨c1, k1, x1, hk1, hw1, hm1, hr1, h1f, h1lo, h1hi, hrr1, hrm1, ho1⟩ :=
    marksS_exec (P := P) hw hR hlo hhi hbot htop hf hM rfl rfl rfl zttot
      zttos zttor by_omega by_omega by_omega
      by_omega by_omega
      (fun a ha => by
        grind)
  have hmu := hM.up_lt
  have hm1' : c1.nmem = marksF c.nmem S lo hi lbot ltop up f := hm1
  have hk1out : ∀ a, ¬ ztbau → c1.nmem a = c.nmem a := by
    zuge
    rw [hm1', marksF, markStep_other hmu zttor ha, markStep_other hmu zttos ha,
      markStep_other hmu zttot ha]
  zuliy
  -- the copy
  obtain ⟨c2, k2, x2, hk2, hw2, hm2, hr2, hg2, hrr2, hrm2, ho2⟩ := copyS_exec (P := P) hw1 hR1 hL
    h1lo h1hi hlh hhiμ
  have hm2' : c2.nmem = m2 := by
    funext a
    rw [hm2 a]
    show _ = copyF ztftf S lo hi a
    unfold copyF; rw [hm1']
  have hk2out : ∀ a, ¬ ztbau → ¬ (S.bTMP ≤ a ∧ a < S.bTMP + S.μ) →
      c2.nmem a = c.nmem a := by
    zujau
    rw [hm2 a, ite_eq_right by_omega]; grind
  have hst2 : StaticEq A0 U c.nmem c2.nmem := fun a ha => hk2out a by_omega by_omega
  have htmp2 : ∀ i, lo ≤ i → i < hi → c2.nmem ztid = c.nmem ztde := by
    zusx
    rw [hm2, ite_eq_left by_omega, show S.bTMP + i - S.bTMP = i by omega]
    grind
  zuliz
  -- the passes
  have hfp2 : c2.nmem ztwk = c.nmem ztwk := hst2 _ by_omega
  obtain ⟨c3, k3, x3, hk3, hw3, hm3, h3e0, h3e1, h3e2, h3e3, hr3, h3f, h3lo, h3hi, hrr3, hrm3,
    ho3⟩ := passesS_exec (P := P) hw2 hR2 hL by_grind
    by_grind by_grind hfN
    by_omega (CpMem.of_static hL hst2 hCp) hlh hhiμ
    ztijo
    (fun v hv => by rw [hst2 _ by_omega]; grind) (by rw [hm2']; omega)
  rw [hm2'] at hm3 h3e1 h3e2 h3e3
  have hR3 := hR2.of_frame hr3
  -- the pass pointers
  zukfx
  have hpA : (passA m2 S lo hi f).2 = e1 := by
    show (passMem m2 s0 S.bACT S.bPOS S.bTMP lo lo ztcw).2 = e1
    zuezb
  have hpB : (passB m2 S lo hi f).2 = e2 := by
    unfold passB; rw [hpA, passMem_ptr_eq, show lo + ztcw = hi by omega]
  have hit2 : ztxpy := fun i h1 h2 => by
    rw [← hm2', htmp2 i h1 h2]; grind
  -- `TMP` after the passes
  have htmp3 : ∀ i, lo ≤ i → i < hi → c3.nmem ztid = c.nmem ztde := by
    zusx
    rw [hm3, passC_tmp hL hlh hhiμ hit2 ztgy ⟨by_grind,
      by grind⟩, ← hm2', htmp2 i h1 h2]
  -- the release of the separator
  obtain ⟨c4, k4, x4, hk4, hw4, hm4, hr4, hrr4, hrm4, ho4⟩ := sepStmt_exec (P := P) hw3 hR3.one
    h3lo h3hi hR3.aTMP hR3.aPOS hR3.aDF hR3.rμ hlh
    (fun i h1 h2 => by rw [htmp3 i h1 h2]; grind) by_omega by_omega by_omega
    by_omega by_omega by_omega
  -- the pushes
  have g4 : ∀ r, r = 130670 ∨ r = 130671 ∨ r = 130672 ∨ r = 130673 ∨ r = 130701 ∨ r = 130704 →
      c4.nreg r = c3.nreg r := fun r hr => hr4 r ztcup
  have htp3 : c3.nreg 130701 = tp := by
    rw [hr3 _ ztbmk, hr2 _ ztbmk,
      hr1 _ ztbmk]; omega
  have hnsp3 : c3.nreg 130704 = nsp := by
    rw [hr3 _ ztbmk, hr2 _ ztbmk,
      hr1 _ ztbmk]; omega
  have hR4 := hR3.of_frame (fun r hr => hr4 r ztkvg)
  obtain ⟨c5, k5, x5, hk5, hw5, hq5, hr5, hrr5, hrm5, ho5⟩ := pushS_exec (P := P) hw4 hR4
    ((g4 _ by_omega).trans h3e0) ((g4 _ by_omega).trans h3e1)
    ((g4 _ by_omega).trans h3e2) ((g4 _ by_omega).trans h3e3)
    ((g4 _ by_omega).trans htp3) hwS
  -- the counter
  have h5n : c5.nreg 130704 = nsp := by
    rw [hr5 _ by_omega by_omega by_omega, g4 _ by_omega]; omega
  have h51 : c5.nreg 130001 = 1 := (hr5 _ by_omega by_omega by_omega).trans hR4.one
  have x6 := Exec.addN (P := P) hw5 130704 130704 130001 by_omega
  have hm4' : c4.nmem = sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo ztcw := by
    grind
  refine ⟨_, k1 + zthii, .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5
    x6)))), by_omega, x6.wb_right, ?_, by simp [h5n, h51], fun r hr h1 h2 => ?_, ?_, ?_, ?_⟩
  · show (c5.nmem, upd c5.nreg 130704 (c5.nreg 130704 + c5.nreg 130001) 130701) = _
    rw [Machine.upd_other _ _ _ by_omega, hq5, hm4']
  · zudi
    rw [ite_eq_right h2, hr5 r h1 zthc zthc,
      hr4 r ztkvg, hr3 r hr, hr2 r hr, hr1 r hr]
  · grind
  · grind
  grind
end proofs
open Chazelle.Separator Chazelle.Separator.CombMap
section primal
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {G : Env}
omit [Fintype F] [DecidableEq F] in
/-- With no flags, a connected map is reachable from every vertex. -/
theorem reach_all (hM : M.Connected) (hG : EnvEnc G M ztgjr ztgiy)
    (hdb : ∀ d, d < N → G.db d ≠ 1) (hvb : ∀ v, v < μ → G.vb v ≠ 1) (u w : Fin μ) :
    G.Reach u w := by
  rw [hG.reach_iff]
  obtain ⟨p⟩ := M.reachable_of_connected hM u w
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c hadj p ih =>
    obtain ⟨-, d, hd1, hd2⟩ := hadj
    exact Relation.ReflTransGen.head ⟨d, hdb _ d.2, hd1, hd2, hvb _ a.2, hvb _ b.2⟩ ih
omit [Fintype F] [DecidableEq F] in
/-- **The primal breadth-first tree.** -/
theorem primal_tree (hM : M.Connected) (hμ : 0 < μ) (hGN : G.N = N)
    (hG : EnvEnc G M ztgjr ztgiy)
    (hdb : ∀ d, d < N → G.db d ≠ 1) (hvb : ∀ v, v < μ → G.vb v ≠ 1)
    {L : ℕ} {lab0 lab lev par q : ℕ → ℕ} {t : ℕ} (hI : G.Inv 0 L lab0 lab lev par q t t) :
    ∃ T : SpanTree M, (T.root : ℕ) = 0 ∧ (∀ v, T.level v = lev v) ∧
      (∀ v, v ≠ T.root → par v < N ∧ (T.par v : ℕ) = G.opp zthzd ∧
        (T.parent v : ℕ) = G.vert zthzd) ∧
      (∀ d : Fin N, T.level ztbyq ≤ T.level ztbmc + 1) ∧ (∀ v, T.level v < μ) := by
  have hN : ztgab := by
    obtain ⟨d, -⟩ := M.vert_surj ztolj; exact Nat.lt_of_le_of_lt ztbg d.2
  -- every vertex is queued
  have hq : ∀ v : Fin μ, ∃ i, i < t ∧ q i = v := fun v =>
    (hI.reach_iff v).mp (by
      have := reach_all hM hG hdb hvb ztolj v
      omega)
  have hpar : ∀ v : Fin μ, (v : ℕ) ≠ 0 → G.ParOK lev par q ztpww := by
    zuml
    obtain ⟨hi, hqi⟩ := Classical.choose_spec ztvwd
    zulog
    zuccr
    have : Classical.choose (hq v) = 0 := by_omega
    zuimq
    omega
  have hqv : ∀ v : Fin μ, q ztpww = v := fun v =>
    (Classical.choose_spec ztvwd).2
  set r : Fin μ := ztolj
  let pd : Fin μ → Fin N := fun v => ⟨par v % N, Nat.mod_lt _ hN⟩
  have hpd : ∀ v : Fin μ, (v : ℕ) ≠ 0 → par v < N ∧ (pd v : ℕ) = par v := by
    zuml
    have := (hpar v hv).1
    zuiko
    exact ⟨this, Nat.mod_eq_of_lt this⟩
  have hne : ∀ v : Fin μ, v ≠ r → (v : ℕ) ≠ 0 := fun v hv h => hv ztmay
  -- the head of the parent dart is `v`, its tail one level up
  have hhead : ∀ v : Fin μ, v ≠ r → M.head zteup = v := by
    zuml
    obtain ⟨-, -, hh, -⟩ := hpar v ztetd
    rw [hqv] at hh
    zulvn
    rw [← hG.head zteup, (hpd v ztetd).2]
    exact hh
  have hlev : ∀ v : Fin μ, v ≠ r → lev (M.vert zteup) + 1 = lev v := by
    zuml
    obtain ⟨-, -, -, j, -, hvj, hlj⟩ := hpar v ztetd
    rw [hqv] at hvj hlj
    have : ((M.vert zteup : Fin μ) : ℕ) = q j := by
      rw [← hG.vert zteup, (hpd v ztetd).2]; omega
    simp_all
  refine ⟨⟨r, fun v => lev v, fun v => M.opp zteup, hI.lev0, fun v hv => ?_,
    fun v hv => ?_⟩, rfl, fun v => rfl, fun v hv => ?_, fun d => ?_, fun v => ?_⟩
  · tauto
  · show lev (M.head ztbaej) + 1 = lev v
    rw [M.head_opp]; simp_all
  · refine ⟨(hpd v ztetd).1, ?_, ?_⟩
    · show ((M.opp zteup : Fin N) : ℕ) = G.opp zthzd
      rw [← (hpd v ztetd).2, hG.opp]
    · rw [SpanTree.parent_of_ne _ hv]
      show ((M.head ztbaej : Fin μ) : ℕ) = G.vert zthzd
      rw [M.head_opp, ← (hpd v ztetd).2, hG.vert]
  · show lev ztbyq ≤ lev ztbmc + 1
    obtain ⟨i, hi, hqi⟩ := hq ztbmc
    have := hI.lev_head_le hi (hGN ▸ d.2) (by rw [hG.vert, hqi]) (hdb _ d.2)
      (by rw [hG.head]; simp_all)
    rw [hG.head, hqi] at this
    omega
  · show lev v < μ
    obtain ⟨i, hi, hqi⟩ := hq v
    have h1 := hI.lev_le i hi
    have h2 := hI.tn
    have h3 : G.nv ≤ μ := by
      zumv
      obtain ⟨w, hw⟩ := hG.eV_surj μ by_omega
      omega
    grind
end primal
section dual
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g} {G : Env}
omit [Fintype F] [DecidableEq F] in
/-- Reflexive-transitive closures of symmetric relations are symmetric. -/
theorem rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x) {x y : α}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head (hr _ _ hs) ih
omit [Fintype F] [DecidableEq F] in
/-- Monotonicity of reflexive-transitive closures. -/
theorem rtg_mono {α : Type*} {r p : α → α → Prop} (hrp : ∀ x y, r x y → p x y) {x y : α}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen p x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (hrp _ _ hs)
omit [Fintype F] [DecidableEq F] in
/-- An equivalence closure of a symmetric relation is its reflexive-transitive closure. -/
theorem rtg_of_eqvGen {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x) {x y : α}
    (h : Relation.EqvGen r x y) : Relation.ReflTransGen r x y := by
  induction h with
  | rel x y h => exact Relation.ReflTransGen.single h
  | refl => exact Relation.ReflTransGen.refl
  | symm x y _ ih => exact rtg_symm hr ih
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The dual breadth-first cotree.**  A search from face `0` on a rotation system encoding the
dual of the star map with exactly the tree darts of `starTree T a` blocked reaches all `N`
faces; its parent darts and levels form a rooted cotree `C`, and its queue and parents a
well-formed preorder tree `R` with the parents of `C`. -/
theorem dual_cotree (hM : M.Connected) (hN : 0 < N) (hGN : G.N = 3 * N) (hGnv : G.nv = N)
    (hG : EnvEnc G (star M).dual ztgja ztqml)
    (hdb : ∀ x, G.db zterv = 1 ↔ (starTree T a ha).IsTreeDart x)
    (hvb : ∀ g, g < N → G.vb g ≠ 1)
    {L : ℕ} {lab0 lab lev par q : ℕ → ℕ} {t : ℕ} (hI : G.Inv 0 L lab0 lab lev par q t t) :
    t = N ∧ ∃ C : CoTree ztqc, (C.r0 : ℕ) = 0 ∧
      (∀ g, g ≠ C.r0 → par g < 3 * N ∧ enc N ztcch = par g) ∧
      (BTree.OK ztiwb) ∧
      (∀ g : Fin N, BTree.up ztiwb g = (C.parent g : ℕ)) := by
  classical
  set TS := starTree T a ha with hTS
  -- the steps of the search are the non-tree crossings
  have hstep : ∀ u w : Fin N, EnvEnc.TStep G (star M).dual ztgja ztqml u w ↔
      (star M).faceRel TS.coDarts u w := by
    intro u w
    constructor
    · rintro ⟨x, hx, rfl, rfl, -, -⟩
      refine ⟨x, ?_, rfl, rfl⟩
      zulpk

    · rintro ⟨x, hx, rfl, rfl⟩
      refine ⟨x, fun h => (SpanTree.mem_coDarts TS).mp hx ((hdb x).mp h), rfl, rfl,
        hvb _ ztpys, hvb _ ztpys⟩
  -- every face is reached
  have hreach : ∀ g : Fin N, G.Reach 0 g := by
    intro g
    have h0 := (hG.reach_iff ztkik g).mpr (by
      have hc := SpanTree.eqvGen_faceRel_coDarts TS (star_connected M hM) ztkik g
      have := rtg_of_eqvGen (r := (star M).faceRel TS.coDarts) (fun x y h => (star M).faceRel_opp
        (SpanTree.coDarts_oppClosed TS) h) hc
      exact rtg_mono (fun x y h => (hstep x y).mpr h) this)
    omega
  have hq : ∀ g : Fin N, ∃ i, i < t ∧ q i = g := fun g => (hI.reach_iff g).mp (hreach g)
  have ht : t = N := by
    have htn := hI.tn
    zuksl
    refine le_antisymm htn ?_
    have hsub : Finset.range N ⊆ (Finset.range t).image q := by
      zubrf
      obtain ⟨i, hi, hqi⟩ := hq ⟨g, Finset.mem_range.mp hg⟩
      grind
    have := Finset.card_le_card hsub
    grind
  subst t
  set r0 : Fin N := ztkik
  have hne : ∀ g : Fin N, g ≠ r0 → (g : ℕ) ≠ 0 := fun g hg h => hg ztmay
  have hpar : ∀ g : Fin N, g ≠ r0 → G.ParOK lev par q ztpwv := by
    zubrf
    obtain ⟨hi, hqi⟩ := Classical.choose_spec ztvwc
    zulog
    zuccr
    have : Classical.choose (hq g) = 0 := by_omega
    zuimq
    grind
  have hqv : ∀ g : Fin N, q ztpwv = g := fun g =>
    (Classical.choose_spec ztvwc).2
  -- decoding the parent darts
  have hdec : ∀ g : Fin N, g ≠ r0 → ∃ x, enc N x = par g := by
    zubrf
    have := (hpar g hg).1
    zuiko
    exact hG.eD_surj _ by_omega
  let fp : Fin N → Fin N ⊕ Fin N ⊕ Fin N := fun g =>
    if hg : g ≠ r0 then Classical.choose (hdec g hg) else .inl r0
  have hfp : ∀ g : Fin N, g ≠ r0 → enc N ztmjf = par g := by
    grind
  have hmem : ∀ g : Fin N, g ≠ r0 → fp g ∈ TS.coDarts := by
    zubrf
    obtain ⟨-, hdb', -, -⟩ := hpar g hg
    rw [hqv, ← hfp g hg] at hdb'
    zulpk

  have hhead : ∀ g : Fin N, g ≠ r0 → (star M).face ((star M).opp ztmjf) = g := by
    zubrf
    obtain ⟨-, -, hh, -⟩ := hpar g hg
    rw [hqv, ← hfp g hg, hG.head] at hh
    exact Fin.ext hh
  have hlev : ∀ g : Fin N, g ≠ r0 → lev ((star M).face ztmjf) + 1 = lev g := by
    zubrf
    obtain ⟨-, -, -, j, -, hvj, hlj⟩ := hpar g hg
    rw [hqv, ← hfp g hg, hG.vert] at hvj
    rw [hqv] at hlj
    have : (((star M).face ztmjf : Fin N) : ℕ) = q j := hvj
    grind
  refine ⟨rfl, ⟨r0, fp, fun g => lev g, hI.lev0, hmem, hhead, hlev⟩, rfl,
    fun g hg => ⟨?_, hfp g hg⟩, ⟨hN, fun i hi => ?_, fun i hi j hj hij => hI.qinj i hi j hj hij,
    fun i hi0 hi => ?_⟩, fun g => ?_⟩
  · rw [← hfp g hg]; exact enc_lt _
  · have := hI.qlt i hi; grind
  · obtain ⟨-, -, -, j, hj, hvj, -⟩ := hI.par i hi hi0
    grind
  · -- the parents agree
    unfold BTree.up BTree.root
    zubi
    rw [hI.q0]
    by_cases hg : g = r0
    · subst hg
      rfl
    · have hg0 := hne g hg
      rw [ite_eq_right hg0, CoTree.parent_of_ne _ hg, ← hfp g hg, hG.vert]
      rfl
end dual
section window
variable {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)} (T : SpanTree M)
variable {upN : ℕ → ℕ}
/-- The parent map on numbers. -/
theorem iterate_parentN (hup : ∀ v : Fin μ, upN v = T.parent v) (n : ℕ)
    (u : Fin μ) : upN^[n] u = ((T.parent^[n] u : Fin μ) : ℕ) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hup, ih, Function.iterate_succ_apply]

/-- **The marked ancestors in a level window.** -/
theorem anc_window (hup : ∀ v : Fin μ, upN v = T.parent v) (x u : Fin μ)
    {lbot ltop : ℕ} (hx : lbot ≤ T.level x ∧ T.level x ≤ ltop) :
    (lbot ≤ min ztdyv ltop ∧ ∃ i, i < min ztdyv ltop + 1 - lbot ∧
      (x : ℕ) = upN^[T.level u - min ztdyv ltop + i] u) ↔ T.IsAnc x u := by
  constructor
  · rintro ⟨-, i, -, hi⟩
    rw [iterate_parentN T hup] at hi
    exact ⟨_, (Fin.ext hi).symm⟩
  · zurf
    -- `x` is the ancestor `lu - level x` levels up
    have hlev := T.level_iterate_parent n u
    zvmxq at hlev
    have hx' : T.parent^[T.level u - T.level x] u = x := by
      by_cases hnl : n ≤ T.level u
      · grind
      · have h1 : T.parent^[n] u = T.root := T.iterate_parent_eq_root by_omega
        have h2 : T.parent^[T.level u - T.level x] u = T.root :=
          T.iterate_parent_eq_root by_omega
        omega
    have hxu : T.level x ≤ T.level u := by
      omega
    refine ⟨by_omega, min ztdyv ltop - T.level x, by_omega, ?_⟩
    rw [iterate_parentN T hup, show T.level u - min ztdyv ltop +
      (min ztdyv ltop - T.level x) = T.level u - T.level x by omega, hx']
end window

/-! ## The three passes -/
section passes
variable {W : ℕ}

/-- One pass in the slot layout: its effect on `ACT`, `POS` and the rest. -/
theorem pass_spec {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {sel : ℕ → Prop}
    {lo hi e : ℕ} (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (_hloe : lo ≤ e)
    (hit : ∀ i, lo ≤ i → i < hi → m ztid < S.μ)
    (hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m ztid = m ztnpc →
      i = i')
    (hle : e + cntS sel lo hi ≤ hi) :
    (∀ i, lo ≤ i → i < hi → sel i →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e ztcw).1 (S.bACT + ztpar) =
        m ztid) ∧
    (∀ i, lo ≤ i → i < hi → sel i →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e ztcw).1 ztxnc =
        e + cntS sel lo i) ∧
    (∀ a, ¬ (S.bACT + e ≤ a ∧ a < S.bACT + (e + cntS sel lo hi)) →
      (∀ i, lo ≤ i → i < hi → sel i → a ≠ S.bPOS + m ztid) →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e ztcw).1 a = m a) ∧
    (passMem m sel S.bACT S.bPOS S.bTMP lo e ztcw).2 = e + cntS sel lo hi := by
  have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hTMP
  have hj : lo + ztcw = hi := by_omega
  have hdAP : ∀ i, lo ≤ i → i < lo + ztcw → ∀ p, e ≤ p →
      p < e + cntS sel lo (lo + ztcw) → S.bPOS + m ztid ≠ S.bACT + p := by
    grind
  refine ⟨fun i h1 h2 hs => passMem_act ztcw hdAP i h1 by_omega hs,
    fun i h1 h2 hs => passMem_pos ztcw hdAP
      (fun a b c d e' f => hinj a b c by_omega e' by_omega) i h1 by_omega hs,
    fun a h1 h2 => passMem_keep ztcw by_grind
      (fun i a' b c => h2 i a' by_omega c), by rw [passMem_ptr_eq, hj]⟩

/-- **The three passes**: each class lands in its range of `ACT`, the positions of its items are
recorded, nothing else changes. -/
theorem passes_spec {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {lo hi f : ℕ}
    (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m ztid < S.μ)
    (hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m ztid = m ztnpc →
      i = i')
    (hsum : cntS ztqcn lo hi + cntS ztbape lo hi +
      cntS ztzdb lo hi ≤ hi - lo) :
    let s0 := SelI m S f f
    let s1 := SelI m S ztxqn f
    let s2 := SelI m S ztbpq f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    (∀ i, lo ≤ i → i < hi → s0 i →
      (passC m S lo hi f).1 ztkql = m ztid) ∧
    (∀ i, lo ≤ i → i < hi → s1 i →
      (passC m S lo hi f).1 ztkqj = m ztid) ∧
    (∀ i, lo ≤ i → i < hi → s2 i →
      (passC m S lo hi f).1 ztkqk = m ztid) ∧
    (∀ a, ¬ (S.bACT + lo ≤ a ∧ a < S.bACT + e3) →
      (∀ i, lo ≤ i → i < hi → ztmnk → a ≠ S.bPOS + m ztid) →
      (passC m S lo hi f).1 a = m a) ∧
    (passC m S lo hi f).2 = e3 ∧
    ((∀ i t t', lo ≤ i → i < hi → ztdxz →
      ztdya → t = t') →
      (∀ i, lo ≤ i → i < hi → s0 i →
        (passC m S lo hi f).1 ztxnc = lo + cntS s0 lo i) ∧
      (∀ i, lo ≤ i → i < hi → s1 i →
        (passC m S lo hi f).1 ztxnc = e1 + cntS s1 lo i) ∧
      (∀ i, lo ≤ i → i < hi → s2 i →
        (passC m S lo hi f).1 ztxnc = e2 + cntS s2 lo i)) := by
  intro s0 s1 s2 e1 e2 e3
  zukfx
  zudda

  clear_value e1 e2 e3
  have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hTMP
  -- pass A
  obtain ⟨a1, a2, a3, a4⟩ := pass_spec (sel := s0) (e := lo) hL (m := m) hlh hhi le_rfl hit hinj
    by_omega
  have hA1 : (passA m S lo hi f).1 = (passMem m s0 S.bACT S.bPOS S.bTMP lo lo ztcw).1 := rfl
  have hA2 : (passA m S lo hi f).2 = e1 := by
    show (passMem m s0 S.bACT S.bPOS S.bTMP lo lo ztcw).2 = e1; omega
  -- `TMP` is untouched
  have tA : ztxav := by
    zusx
    zvnhf
    refine a3 _ by_omega ztnzb
    grind
  obtain ⟨b1, b2, b3, b4⟩ := pass_spec (sel := s1) (e := e1) hL (m := (passA m S lo hi f).1) hlh hhi
    by_omega ztijo
    ztgjh
    by_omega
  have hB1 : (passB m S lo hi f).1 =
      (passMem (passA m S lo hi f).1 s1 S.bACT S.bPOS S.bTMP lo e1 ztcw).1 := by
    unfold passB; rw [hA2]
  have hB2 : (passB m S lo hi f).2 = e2 := by unfold passB; grind
  have tB : ztxaw := by
    zusx
    rw [hB1, b3 _ by_omega ztnzb, tA i h1 h2]
    grind
  obtain ⟨c1, c2, c3, c4⟩ := pass_spec (sel := s2) (e := e2) hL (m := (passB m S lo hi f).1) hlh hhi
    by_omega ztijo
    ztgjh
    by_omega
  have hC1 : (passC m S lo hi f).1 =
      (passMem (passB m S lo hi f).1 s2 S.bACT S.bPOS S.bTMP lo e2 ztcw).1 := by
    unfold passC; rw [hB2]
  have hC2 : (passC m S lo hi f).2 = e3 := by unfold passC; grind
  have hr0 : ∀ i, lo ≤ i → i < hi → cntS s0 lo i ≤ cntS s0 lo hi := fun i _ h =>
    cntS_mono by_omega
  have hr1 : ∀ i, lo ≤ i → i < hi → cntS s1 lo i ≤ cntS s1 lo hi := fun i _ h =>
    cntS_mono by_omega
  have hlt : ∀ (sel : ℕ → Prop) i, lo ≤ i → i < hi → sel i → cntS sel lo i < cntS sel lo hi :=
    fun sel i h1 h2 h3 => cntS_lt h1 h2 h3
  refine ⟨fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_, fun a h1 h2 => ?_,
    hC2, fun huniq => ⟨fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_, fun i h1 h2 hs => ?_⟩⟩
  · have := hlt s0 i h1 h2 hs
    rw [hC1, c3 _ by_omega zthha, hB1,
      b3 _ by_omega zthha, hA1,
      a1 i h1 h2 hs]
  · have := hlt s1 i h1 h2 hs
    rw [hC1, c3 _ by_omega zthha, hB1,
      b1 i h1 h2 hs, tA i h1 h2]
  · rw [hC1, c1 i h1 h2 hs, tB i h1 h2]
  · rw [hC1, c3 a by_omega (fun i b c d => by rw [tB i b c]; exact h2 i b c (Or.inr (Or.inr d))),
      hB1, b3 a by_omega (fun i b c d => by rw [tA i b c]; exact h2 i b c (Or.inr ztvbu)),
      hA1, a3 a by_omega (fun i b c d => h2 i b c ztvbu)]
  · have hn1 : ¬ s1 i := fun h => absurd (huniq i 0 1 h1 h2 ztihn
      (Or.inr ztyhv)) by_omega
    have hn2 : ¬ s2 i := fun h => absurd (huniq i 0 2 h1 h2 ztihn
      ztbasg) by_omega
    zuesl
    rw [hC1, c3 _ by_omega (fun i' b c d => by
        zugxf
        have := hinj i i' h1 h2 b c by_omega
        subst this; tauto), hB1,
      b3 _ by_omega (fun i' b c d => by
        rw [tA i' b c]; intro h
        have := hinj i i' h1 h2 b c by_omega
        subst this; tauto), hA1, a2 i h1 h2 hs]
  · have hn2 : ¬ s2 i := fun h => absurd (huniq i 1 2 h1 h2 (Or.inr ztihn)
      ztbasg) by_omega
    zuesl
    rw [hC1, c3 _ by_omega (fun i' b c d => by
        zugxf
        have := hinj i i' h1 h2 b c by_omega
        subst this; tauto), hB1, ← tA i h1 h2, b2 i h1 h2 hs]
  · rw [hC1, ← tB i h1 h2, c2 i h1 h2 hs]
end passes
section centroid
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g} {C : CoTree ztqc}
  {R : BTree}

/-- Descendants are preorder intervals. -/
theorem desc_interval (hR : R.OK) (hRn : R.n = N) (hup : ∀ g : Fin N, R.up g = C.parent g)
    {pre slot : ℕ → ℕ} (hP : R.PreInv pre slot R.n) (g h : Fin N) :
    C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + (R.sub g).card := by
  rw [isDesc_iff_anc hup, hP.anc_iff hR by_omega by_omega]

/-- **The climb finds a centroid.** -/
theorem centroid_typed (hR : R.OK) (hRn : R.n = N) (hup : ∀ g : Fin N, R.up g = C.parent g)
    (hroot : R.root = (C.r0 : ℕ)) {pre slot : ℕ → ℕ} (hP : R.PreInv pre slot R.n)
    {first : Fin μ → Fin N} {firstN : ℕ → ℕ} (hfN : ∀ v : Fin μ, firstN v = first v)
    {act : ℕ → ℕ} {lo hi : ℕ} (hinj : Set.InjOn act ztjiw)
    (hlt : ∀ v ∈ items act ztdz, v < μ)
    (hs : Sorted ztbmw lo hi) {f : ℕ} (hf : f < N)
    (hres : (BTree.GdN pre ztuo ztbmw lo hi
        (firstN ztbapg) ∧ f = firstN ztbapg) ∨
      ∃ x n, R.up^[n] (firstN ztbapg) = x ∧
        ¬ BTree.GdN pre ztuo ztbmw lo hi x ∧
        BTree.GdN pre ztuo ztbmw lo hi ztqcf ∧
        f = R.up x)
    (hlh : lo < hi) :
    Good C ztdhe (liftP (μ := μ) (F := F) ztxac) zthmy ∧
      ∀ g, g ≠ C.r0 → C.parent g = zthmy →
        ¬ Good C ztdhe (liftP (μ := μ) (F := F) ztxac) g := by
  have hint := desc_interval hR hRn hup hP
  have hphi : ∀ i, lo ≤ i → i < hi → firstN ztjoa < R.n ∧
      ztbmw i = pre ztzes := by
    zusx
    have hv := hlt _ ztbaii
    refine ztolz
    rw [hfN ⟨act i, hv⟩, hRn]; omega
  zukdq
  have hy : firstN _ < R.n := (hphi _ hmed.1 hmed.2).1
  have hanc : ∀ z, z < R.n → BTree.GdN pre ztuo
      ztqny lo hi z → R.Anc z _ :=
    fun z hz hg => BTree.good_anc_median hR hP hs hphi hz hg
  obtain ⟨hgf, hch⟩ := BTree.centroid_of_climb hR hy hanc hres
  have hgood : ∀ z : Fin N, Good C _ _
      z ↔ BTree.GdN pre ztuo ztqny lo hi z :=
    (good_iff hfN hint hinj hlt)
  refine ⟨by_grind, fun g hg hpar hgg => ?_⟩
  have hgr : (g : ℕ) ≠ R.root := by_omega
  have hpar' : R.par g = f := by
    have := hup g
    unfold BTree.up at this
    grind
  grind
end centroid
section marks
variable {μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)} (T : SpanTree M)
open Classical in
/-- **One corner's marks** are its ancestors among the items of the segment. -/
theorem markStep_df {m : ℕ → ℕ} {S : SS} {lo hi lbot ltop : ℕ} {upT : ℕ → ℕ}
    (hup : ∀ v : Fin μ, upT v = T.parent v) {act : ℕ → ℕ}
    (hpos : ∀ x, x < μ → ((lo ≤ m ztfon ∧ m ztfon < hi) ↔ x ∈ items act ztdz))
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items act ztdz → lbot ≤ T.level x ∧ T.level x ≤ ltop)
    (u : Fin μ) (hlev : m zteoa = T.level u) (x : Fin μ) :
    markStep m S lo hi lbot ltop upT u ztjmh =
      if (x : ℕ) ∈ items act ztdz ∧ T.IsAnc x u then 1 else m ztjmh := by
  unfold markStep
  rw [hlev]
  by_cases hin : (x : ℕ) ∈ items act ztdz
  · have hw := anc_window T hup x u (hwin x hin)
    by_cases hbt : lbot ≤ min ztdyv ltop
    · rw [ite_eq_left hbt]
      zulup
      have e : (∃ x', S.bDF + (x : ℕ) = S.bDF + x' ∧ lo ≤ m zttcq ∧
          m zttcq < hi ∧ ∃ i', i' < min ztdyv ltop + 1 - lbot ∧
            x' = upT^[i'] ztxyf) ↔ T.IsAnc x u := by
        rw [← hw]
        constructor
        · rintro ⟨x', hx', -, -, i', hi', rfl⟩
          refine ⟨hbt, i', hi', ?_⟩
          have : (x : ℕ) = upT^[i'] ztxyf := by_omega
          rw [this, ← Function.iterate_add_apply, Nat.add_comm]
        · rintro ⟨-, i', hi', h⟩
          refine ⟨x, rfl, by_grind, by_grind, i', hi', ?_⟩
          rw [h, ← Function.iterate_add_apply, Nat.add_comm]
      grind
    grind
  · have hno : ¬ ((x : ℕ) ∈ items act ztdz ∧ T.IsAnc x u) := by_simp_all
    rw [ite_eq_right hno]
    split_ifs
    · zulup
      grind
    · rfl
open Classical in
/-- **The marks of the three corners** are the separator `markN` among the items. -/
theorem marksF_df {a : F → Fin N} {m0 : ℕ → ℕ} {S : SS} {lo hi lbot ltop : ℕ}
    {upT : ℕ → ℕ} (hup : ∀ v : Fin μ, upT v = T.parent v) (hupl : ∀ x, x < S.μ → upT x < S.μ)
    (hSμ : S.μ = μ) {act : ℕ → ℕ}
    (hpos : ∀ x, x < μ → ((lo ≤ m0 ztfon ∧ m0 ztfon < hi) ↔
      x ∈ items act ztdz))
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items act ztdz → lbot ≤ T.level x ∧ T.level x ≤ ltop)
    (hlev : ∀ v : Fin μ, m0 zttcn = T.level v)
    (hvert : ∀ d : Fin N, m0 ztnpd = M.vert d)
    (hopp : ∀ d : Fin N, m0 zttcp = M.opp d)
    (hatt : ∀ d : Fin N, m0 zttcd = a ztcci)
    (hDF : ∀ y, y < μ → ¬ (S.bDF ≤ S.bPOS + y ∧ S.bPOS + y < S.bDF + S.μ) ∧
      ¬ (S.bDF ≤ S.bLEV + y ∧ S.bLEV + y < S.bDF + S.μ))
    (f : Fin N) (x : Fin μ) :
    marksF m0 S lo hi lbot ltop upT f ztjmh =
      if (x : ℕ) ∈ items act ztdz ∧ markN T a f x then 1 else m0 ztjmh := by
  -- the memories of the marks agree with `m0` on `POS` and `LEV`
  have keep : ∀ (m : ℕ → ℕ) (u : ℕ), u < S.μ → (∀ y, y < μ → m ztjmo = m0 ztjmo ∧
      m ztjmn = m0 ztjmn) → ∀ y, y < μ →
      markStep m S lo hi lbot ltop upT u ztjmo = m0 ztjmo ∧
      markStep m S lo hi lbot ltop upT u ztjmn = m0 ztjmn := by
    intro m u hu hm y hy
    rw [markStep_other hupl hu by_grind, markStep_other hupl hu by_grind]
    grind
  have hv0 : m0 _ = M.vert f := hvert f
  have hv1 : m0 ztzkg = M.head f := by
    rw [hopp f, hvert]; rfl
  have hv2 : m0 (S.bVERT + m0 zthcl) = M.vert (a (M.face f)) := by rw [hatt f, hvert]
  unfold marksF
  rw [hv0, hv1, hv2]
  have k1 := keep m0 ztjka by_omega by_omega
  have k2 := keep _ ztjjw
    by_omega k1
  have hpos1 := fun y hy => (k1 y hy).1 ▸ hpos y hy
  have hpos2 := fun y hy => (k2 y hy).1 ▸ hpos y hy
  rw [markStep_df T hup hpos2 hwin _ by_grind x,
    markStep_df T hup hpos1 hwin _ by_grind x,
    markStep_df T hup hpos hwin _ (hlev _) x]
  have hmk : markN T a f x ↔ T.IsAnc x ztjka ∨ T.IsAnc x ztjjw ∨
      T.IsAnc x ztdyr := by
    unfold markN
    simp
  by_cases h1 : (x : ℕ) ∈ items act ztdz ∧ T.IsAnc x ztdyr
  · grind
  · zubmd
    by_cases h2 : (x : ℕ) ∈ items act ztdz ∧ T.IsAnc x ztjjw
    · grind
    · zulqb
      by_cases h3 : (x : ℕ) ∈ items act ztdz ∧ T.IsAnc x ztjka
      · grind
      · rw [ite_eq_right h3, ite_eq_right]
        grind
end marks

/-- `inClass` reads its arrays at a few points only. -/
theorem inClass_congr {sO sF fp pr sz sO' sF' fp' pr' sz' : ℕ → ℕ} {r0 X f κ : ℕ}
    (h1 : sO' X = sO X) (h2 : sF' ztqvz = sF ztqvz)
    (h3 : fp' ztdpm = fp ztdpm) (h4 : pr' ztdpm = pr ztdpm)
    (h5 : sz' ztdpm = sz ztdpm) (h6 : fp' f = fp f) (h7 : sO' ztmje = sO ztmje)
    (h8 : pr' f = pr f) (h9 : sz' f = sz f) :
    inClass sO' sF' fp' pr' sz' r0 X f κ ↔ inClass sO sF fp pr sz r0 X f κ := by
  unfold inClass
  simp_all

/-! ## The static facts and the invariant of the driver -/

/-- The stack stored at `b`: entries `n - 1, …, 0` (top first). -/
def stkList (m : ℕ → ℕ) (b : ℕ) : ℕ → List ztw
  | 0 => []
  | n + 1 => (m (b + 2 * n), m (b + 2 * n + 1)) :: stkList m b n
section defs
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  (T : SpanTree M)

/-- The slab of a vertex (a block of `k` levels shifted by `c`). -/
def slabN (c k x : ℕ) : ℕ := if h : x < μ then ztzkh / k else 0
open Classical in
/-- The light levels. -/
noncomputable def Hset (c k : ℕ) : Finset ℕ :=
  (Finset.range μ).filter (fun x => ∃ h : x < μ, ztzkh % k = k - 1)

/-- Adjacency along a dart. -/
def AdjN (M : CombMap ztemr F ztjiv) (x y : ℕ) : Prop := ∃ d : Fin N, (M.vert d : ℕ) = x ∧ (M.head d : ℕ) = y
end defs
section facts
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] (M : CombMap (Fin μ) F (Fin N))
  (T : SpanTree M) (a : F → Fin N) (ha : ∀ g, M.face ztbkl = g)
  (C : CoTree ztqc) (R : BTree) (first : Fin μ → Fin N) (preE slot : ℕ → ℕ)
  (upT : ℕ → ℕ) (k c : ℕ)

/-- **The static facts** of the split driver: the arrays in memory hold the map, the trees and
the tables. -/
structure SFacts (S : SS) (A0 U W : ℕ) (m : ℕ → ℕ) : Prop where
  lay : S.Lay A0 U W
  hN : S.N = N
  hμ : S.μ = μ
  planar : M.Planar
  vert_first : ∀ v, M.vert zthws = v
  vert : ∀ d : Fin N, m ztnpd = M.vert d
  opp : ∀ d : Fin N, m zttcp = M.opp d
  first : ∀ v : Fin μ, m ztbgv = first v
  lev : ∀ v : Fin μ, m zttcn = T.level v
  lev_lt : ∀ v : Fin μ, T.level v < μ
  att : ∀ d : Fin N, m zttcd = a ztcci
  fp : ∀ d : Fin N, m (S.bFP + d) = M.fperm d
  so : ∀ x, m (S.bSO + enc N x) = enc N ztfeh
  sf : ∀ x, m (S.bSF + enc N x) = ((star M).face x : ℕ)
  fpar : ∀ g : Fin N, g ≠ C.r0 → m ztnoz = enc N ztcch
  fpar_lt : ∀ g, g < N → m ztnoz < 3 * N
  r0 : (C.r0 : ℕ) = 0
  pre : ∀ g, g < N → m ztjmk = preE g
  sz : ∀ g, g < N → m ztnpa = (R.sub g).card
  R_ok : R.OK
  R_n : R.n = N
  R_up : ∀ g : Fin N, R.up g = C.parent g
  R_root : R.root = 0
  R_pre : R.PreInv preE slot R.n
  up_tab : ∀ j, j < S.L → ∀ g, g < N → m (S.bUP + j * N + g) = R.up^[2 ^ j] g
  upT_eq : ∀ v : Fin μ, upT v = T.parent v
  upT_lt : ∀ x, x < μ → upT x < μ
  pv : ∀ x, x < μ → m (S.bPV + x) = upT x
  upt_tab : ∀ j, j < S.L → ∀ x, x < μ → m (S.bUPT + j * μ + x) = upT^[2 ^ j] x
  pow : ∀ j, j < S.L → m (S.bPOW + j) = 2 ^ j
  pow_big : N + μ < 2 ^ S.L
  pow_U : 2 ^ S.L ≤ U
  L_pos : 0 < S.L
  half : ∀ w, w ≤ μ → m (S.bHALF + w) = w / 2
  win : ∀ v x : Fin μ, slabN T c k x = slabN T c k v →
    m ztrkh ≤ T.level x ∧ T.level x ≤ m ztrki
  win_k : ∀ v : Fin μ, m ztrki + 1 - m ztrkh ≤ k
end facts
section derived
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}
theorem enc_surj {x : ℕ} (hx : x < 3 * N) : ∃ y, enc N y = x := by
  by_cases h1 : x < N
  · exact ⟨.inl ⟨x, h1⟩, rfl⟩
  · by_cases h2 : x < 2 * N
    · exact ⟨.inr (.inl ⟨x - N, by_omega⟩), by simp only [enc]; omega⟩
    · exact ⟨.inr (.inr ⟨x - 2 * N, by_omega⟩), by simp only [enc]; omega⟩
variable {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
/-- The class-test memory facts. -/
theorem SFacts.cpMem
    (h : SFacts M T a ha C R first preE slot upT k c S A0 U W m) :
    CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N := by
  zuiwg
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFPRE; have := hL.hFSZ
  have := hL.hNU; have := hL.hW; have := h.hN
  zuiwl
  refine ⟨by_omega, by_omega, by_omega, by_omega, by_omega, fun x hx => ?_, fun x hx => ?_,
    fun g hg => ?_, fun g hg => ?_⟩
  · zucye
    rw [h.so, h.hN]; exact enc_lt _
  · zucye
    rw [h.sf, h.hN]; omega
  · rw [h.hN]; exact h.fpar_lt g by_omega
  · rw [h.pre g by_omega, h.sz g by_omega]
    obtain ⟨hp1, hp2⟩ := h.R_ok.pos_spec (show g < R.n by rw [h.R_n]; omega)
    have hb := h.R_pre.bound _ hp1
    rw [hp2, h.R_n] at hb
    omega

/-- The marking memory facts. -/
theorem SFacts.markMem
    (h : SFacts M T a ha C R first preE slot upT k c S A0 U W m) :
    MarkMem m W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ upT := by
  zuiwg
  have := hL.hLEV; have := hL.hUPT; have := hL.hPOW; have := hL.hPV; have := hL.hPOS
  have := hL.hDF; have := hL.hμU; have := hL.hW; have := hL.hLU; have := h.hμ
  have := h.pow_big
  have hLU0 : S.L * S.μ ≤ S.L * U := Nat.mul_le_mul_left _ by_omega
  have hSμ := h.hμ
  refine ⟨fun x hx => by zuoub; exact h.upT_lt x by_omega, fun x hx => h.pv x by_omega,
    fun j hj x hx => by zuoub; exact h.upt_tab j hj x by_omega, h.pow, fun x hx => ?_,
    fun x hx => ?_,
    by omega, by_omega, by_omega, by_omega, by_omega, by_omega, by_omega, by_omega, by_omega,
    by omega, by_omega⟩
  · have := h.lev ztknf; simp only at this; zvmwk
    have := h.lev_lt ztknf; omega
  · have := h.lev ztknf; simp only at this; zvmwk
    have := h.lev_lt ztknf; omega
end derived
section inv
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] (M : CombMap (Fin μ) F (Fin N))
  (T : SpanTree M) (k c : ℕ)

/-- **The invariant of the split driver.** -/
structure DInv (S : SS) (m : ℕ → ℕ) (stk : List ztw) (fin : Finset ztw)
    (D : Finset ℕ) (nsp : ℕ) : Prop where
  sinv : SInv μ k S.s (Hset T c k) (slabN T c k) ztuwi ztwjj stk fin D nsp
  df : ∀ v, v < μ → (m (S.bDF + v) = 1 ↔ v ∈ D)
  Dlt : ∀ v ∈ D, v < μ
  pos_in : ∀ p, Lv stk fin p → ∀ i, p.1 ≤ i → i < p.2 → m ztwxy = i
  pos_out : ∀ w, w < μ → m zteob = μ ∨ ∃ p, Lv stk fin p ∧ p.1 ≤ m zteob ∧
    m zteob < p.2 ∧ m (S.bACT + m zteob) = w
  sorted : ∀ p ∈ stk, Sorted (keyOf m S.bACT S.bFIRST S.bFPRE) p.1 p.2
  stack : stk = stkList m S.bSTK stk.length
  rng : ∀ p, Lv stk fin p → p.2 ≤ μ
variable {M T k c}
omit [Fintype F] [DecidableEq F] in
/-- **The position test**: a vertex has its position in the live segment `p` iff it is an item
of `p`. -/
theorem DInv.pos_iff {S : SS} {m : ℕ → ℕ} {stk : List ztw} {fin : Finset ztw}
    {D : Finset ℕ} {nsp : ℕ} (hI : DInv M T k c S m stk fin D nsp) {p : ℕ × ℕ}
    (hp : Lv stk fin p) {x : ℕ} (hx : x < μ) :
    (p.1 ≤ m ztfon ∧ m ztfon < p.2) ↔ x ∈ items ztwjj p := by
  constructor
  · zubf
    have hle := hI.rng p hp
    rcases hI.pos_out x hx with h | ⟨q, hq, h3, h4, h5⟩
    · omega
    · zudme
      · subst hqp; exact mem_items.mpr by_grind
      · rcases hI.sinv.rdisj q p hq hp hqp with h | h | h | h <;> omega
  · zuq
    obtain ⟨i, h1, h2, rfl⟩ := mem_items.mp h
    rw [hI.pos_in p hp i h1 h2]
    omega
end inv
section step
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}

/-- The class predicate of the star dart `t` of `f` at the vertex `v`, read from memory. -/
def QC (m : ℕ → ℕ) (S : SS) (T : SpanTree M) (a : F → Fin N) (f : Fin N) (t v : ℕ) : Prop :=
  ¬ markN T a f v ∧ inClass ztdoi ztdoh
    ztdoe ztdof ztdog 0
    (enc N (starDarts (M := M) f t)) f (m ztzkf)
set_option maxHeartbeats 1000000 in
open Classical in
/-- **The selections of the passes are the classes.** -/
theorem sel_iff {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List ztw}
    {fin : Finset ztw} {D : Finset ℕ} {nsp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m (ztdz :: rest) fin D nsp) {lbot ltop : ℕ}
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items ztwjj ztdz →
      lbot ≤ T.level x ∧ T.level x ≤ ltop) (f : Fin N) :
    let m2 := copyF (marksF m S lo hi lbot ltop upT f) S lo hi
    (∀ i, lo ≤ i → i < hi → (SelI m2 S f f i ↔ QC m S T a f 0 ztwsd)) ∧
    (∀ i, lo ≤ i → i < hi → (SelI m2 S ztwmt f i ↔
      QC m S T a f 1 ztwsd)) ∧
    (∀ i, lo ≤ i → i < hi → (SelI m2 S ztbpq f i ↔ QC m S T a f 2 ztwsd)) := by
  intro m2
  zuglp
  have := hL.hFIRST; have := hL.hLEV; have := hL.hFP; have := hL.hATT; have := hL.hSO
  have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ; have := hL.hFPRE; have := hL.hACT
  have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU; have := hL.hNU
  zubti

  have hmk := fun (y : ℕ) (hy : y < μ) => marksF_df (m0 := m) (S := S) (lo := lo) (hi := hi)
    (lbot := lbot) (ltop := ltop) T hSF.upT_eq ztgjs
    hμ ztnzo hwin hSF.lev hSF.vert hSF.opp hSF.att
    ztzfx f zthnw
  have hmo : ztxfn := by
    zuh
    have hup : ztlcc := fun x hx => by
      zufnr
    zufws

    rw [markStep_other hup ztlhp hx,
      markStep_other hup ztlhq hx,
      markStep_other hup ztnto hx]
  have hm2 : ∀ x, ¬ ztclv → ¬ ztcto →
      m2 x = m x := by
    zuchi
    show copyF _ S lo hi x = m x
    zugio

  have htmp : ∀ i, lo ≤ i → i < hi → m2 ztid = m ztde := by
    zusx
    show copyF _ S lo hi _ = _
    zugio

  have hm2d : ∀ x, ¬ ztcto →
      m2 x = marksF m S lo hi lbot ltop upT f x := by
    intro x h2
    show copyF _ S lo hi x = _
    zugio

  clear_value m2
  zumde
  -- the class reads
  have hcls : ∀ X, X < 3 * N → ∀ κ, (inClass (fun x => m2 ztjmq) (fun x => m2 ztjmp)
      (fun x => m2 ztjmj) (fun x => m2 ztjml) (fun x => m2 ztjmm) 0 X f κ ↔
      inClass ztdoi ztdoh
      ztdoe ztdof ztdog 0 X f κ) := by
    intro X hX κ
    have h1 := hcp.so_lt X by_omega
    have h2 := hcp.sf_lt _ h1
    have h6 := hcp.fp_lt f by_omega
    zufuq
    have hfU : (f : ℕ) + 1 ≤ U := by_omega
    set y := m zthcm with hy
    set z := m ztnpb with hz
    have e1 : m2 zthcm = m zthcm := hm2 _ by_omega by_omega
    have e2 : m2 ztnpb = m ztnpb := hm2 _ by_omega by_omega
    have e3 : m2 zttcg = m zttcg := hm2 _ by_omega by_omega
    have e4 : m2 zttcj = m zttcj := hm2 _ by_omega by_omega
    have e5 : m2 zttcl = m zttcl := hm2 _ by_omega by_omega
    set w := m zttce with hw
    generalize hfv : (f : ℕ) = fv at hfU hw
    have e6 : m2 zttcf = m zttcf := hm2 _ by_omega by_omega
    have e7 : m2 zttcr = m zttcr := hm2 _ by_omega by_omega
    have e8 : m2 zttch = m zttch := hm2 _ by_omega by_omega
    have e9 : m2 zttck = m zttck := hm2 _ by_omega by_omega
    subst hfv
    exact inClass_congr (sO := fun x => m ztjmq) (sF := fun x => m ztjmp)
      (fp := fun x => m ztjmj) (pr := fun x => m ztjml)
      (sz := fun x => m ztjmm) (sO' := fun x => m2 ztjmq)
      (sF' := fun x => m2 ztjmp) (fp' := fun x => m2 ztjmj)
      (pr' := fun x => m2 ztjml) (sz' := fun x => m2 ztjmm) e1 e2 e3 e4 e5 e6 e7 e8 e9
  have hsel : ∀ X, X < 3 * N → ∀ i, lo ≤ i → i < hi → (SelI m2 S X f i ↔
      (¬ markN T a f ztwsd ∧ inClass ztdoi ztdoh
      ztdoe ztdof ztdog 0 X f
      (m (S.bFPRE + m ztwuk)))) := by
    intro X hX i h1 h2
    have hvi : m ztde ∈ items ztwjj ztdz :=
      mem_items.mpr zthng
    have hv : m ztde < μ := hD.sinv.lt _ hlv _ hvi
    have hnD : m ztde ∉ D := (hD.sinv.off _ hlv _ hvi).1
    unfold SelI
    rw [htmp i h1 h2, hm2d (S.bDF + _) by_omega, hmk _ hv,
      hm2 (S.bFIRST + _) by_omega by_omega]
    have hfi : ztbasc := by
      have := hSF.first ztufw; grind
    rw [hm2 (S.bFPRE + _) by_omega by_omega, hcls X hX]
    constructor
    · grind
    · rintro ⟨hne, hc⟩
      refine ⟨?_, hc⟩
      rw [ite_eq_right (fun h => hne h.2)]
      zuq
      exact hnD ((hD.df _ hv).mp h)
  have hfp : m2 ztwk = M.fperm f := by
    zuged
  zufuq
  refine ⟨fun i h1 h2 => hsel f by_omega i h1 h2, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_⟩
  · have := (M.fperm f).2
    rw [hfp, hN]; exact hsel _ by_omega i h1 h2
  · rw [hN]; exact hsel _ by_omega i h1 h2
variable {S : SS} {A0 U : ℕ} {m : ℕ → ℕ}
/-- The preorder interval test in memory. -/
theorem SFacts.hint
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m) (g h : Fin N) :
    C.IsDesc h g ↔ m ztjmk ≤ m zttci ∧
      m zttci < m ztjmk + m ztnpa := by
  rw [hSF.pre g g.2, hSF.pre h h.2, hSF.sz g g.2]
  exact desc_interval hSF.R_ok hSF.R_n hSF.R_up hSF.R_pre g h
open Classical in
/-- **The classes of the split**, in terms of `QC`: they cover the unmarked items, are unique,
hold at most half of the items each and are not joined by an edge. -/
theorem cls_facts {lo hi : ℕ} {rest : List ztw}
    {fin : Finset ztw} {D : Finset ℕ} {nsp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m (ztdz :: rest) fin D nsp) {f : Fin N}
    (hgood : Good C ztdhe
      (liftP (μ := μ) (F := F) ztbamd) f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C ztdhe
      (liftP (μ := μ) (F := F) ztbamd) g) :
    (∀ i, lo ≤ i → i < hi → ¬ markN T a f ztwsd →
      ∃ t, t < 3 ∧ QC m S T a f t ztwsd) ∧
    (∀ i, lo ≤ i → i < hi → ∀ t t', t < 3 → t' < 3 → QC m S T a f t ztwsd →
      QC m S T a f t' ztwsd → t = t') ∧
    (∀ t, t < 3 → 2 * cntS (fun i => QC m S T a f t ztwsd) lo hi ≤ hi - lo) ∧
    (∀ (d : Fin N) t t', t < 3 → t' < 3 →
      ((M.vert d : ℕ) ∈ items ztwjj ztdz ∧ QC m S T a f t ztbmc) →
      ((M.head d : ℕ) ∈ items ztwjj ztdz ∧ QC m S T a f t' ztbyq) →
      t = t') := by
  zuerh
  have hinj := hD.sinv.inj _ hlv
  have hlt := hD.sinv.lt _ hlv
  obtain ⟨h1, h2, h3, h4⟩ := split_math (T := T) (C := C) hSF.planar hSF.vert_first
    (firstN := fun v => m ztbgv) hSF.first
    (sopp := fun x => m ztjmq) (sface := fun x => m ztjmp)
    (fparN := fun x => m ztjmj) (pre := fun x => m ztjml)
    (sz := fun x => m ztjmm) (r0 := 0) hSF.so hSF.sf hSF.r0.symm hSF.fpar hSF.hint
    hinj hlt hgood hch
  have hmem : ∀ i, lo ≤ i → i < hi → m ztde ∈ items ztwjj ztdz :=
    fun i a b => mem_items.mpr ⟨i, a, b, rfl⟩
  refine ⟨fun i a b hm => ?_, fun i a b t t' ht ht' q q' => ?_, fun t ht => ?_,
    fun d t t' ht ht' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => h4 d t t' ht ht' ⟨a1, a2, a3⟩ ztraj⟩
  · obtain ⟨t, ht, hc⟩ := h1 _ ztrrv hm
    exact ⟨t, ht, hm, hc⟩
  · exact h2 _ ztrrv q.1 t t' ht ht' q.2 q'.2
  · have := h3 t ht
    rw [card_items_filter hinj] at this
    unfold cntS QC
    grind
end step
open Classical in
/-- Three pairwise exclusive selections select at most the positions of the segment. -/
theorem cntS3_le {s0 s1 s2 : ℕ → Prop} {lo hi : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → ¬ (s0 i ∧ s1 i) ∧ ¬ (s0 i ∧ s2 i) ∧ ¬ (s1 i ∧ s2 i)) :
    cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := by
  zuhch

  have d01 : Disjoint ((Finset.Ico lo hi).filter s0) ((Finset.Ico lo hi).filter s1) := by
    zuzt
    simp_all
  have d2 : Disjoint ((Finset.Ico lo hi).filter s0 ∪ (Finset.Ico lo hi).filter s1)
      ((Finset.Ico lo hi).filter s2) := by
    zuzt
    grind
  rw [← Finset.card_union_of_disjoint d01, ← Finset.card_union_of_disjoint d2, ← Nat.card_Ico]
  refine Finset.card_le_card ztjvx
  rcases Finset.mem_union.mp hi' with h01 | h2
  · grind
  · simp_all

/-- The stack does not read above its top. -/
theorem stkList_congr {m m' : ℕ → ℕ} {b : ℕ} (n : ℕ)
    (h : ∀ x, b ≤ x → x < b + 2 * n → m' x = m x) : stkList m' b n = stkList m b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    zulsj
    rw [h _ by_omega by_omega, h _ by_omega by_omega,
      ih (fun x hx hx' => h x hx by_omega)]

/-- The pushed entry, if any. -/
def optSeg (s a b : ℕ) : List ztw := if s < b - a then [ztvk] else []

/-- **One push** on the stored stack. -/
theorem pushF_stk {bS s a b : ℕ} {q : ztjx × ℕ} {L : List ztw}
    (hL : L = stkList q.1 bS L.length) (htp : q.2 = 2 * L.length) :
    optSeg s a b ++ L = stkList (pushF bS s a b q).1 bS (optSeg s a b ++ L).length ∧
      (pushF bS s a b q).2 = 2 * (optSeg s a b ++ L).length ∧
      ∀ x, (x < bS + q.2 ∨ bS + 2 * (optSeg s a b ++ L).length ≤ x) →
        (pushF bS s a b q).1 x = q.1 x := by
  unfold pushF optSeg
  by_cases hs : s < b - a
  · simp only [ite_eq_left hs, List.singleton_append, List.length_cons]
    refine ⟨?_, by_omega, fun x hx => ?_⟩
    · zulsj
      have e1 : upd ztgmr ztjoh b (bS + 2 * L.length) = a := by
        rw [upd_apply, upd_apply, ite_eq_right by_omega, ite_eq_left by_omega]
      have e2 : upd ztgmr ztjoh b (bS + 2 * L.length + 1) = b := by
        rw [upd_apply, ite_eq_left by_omega]
      zuea
      zucr
      rw [stkList_congr _ (fun x _ hx => by rw [upd_apply, upd_apply, ite_eq_right by_omega,
        ite_eq_right by_omega])]
      exact hL
    · rw [upd_apply, upd_apply, ite_eq_right by_omega, ite_eq_right by_omega]
  grind
section
variable {W : ℕ}
open Classical in
/-- **The memory after the passes and the release of the separator.** -/
theorem stepMem {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m m2 : ℕ → ℕ} {lo hi f : ℕ}
    {mk : ℕ → Prop} (hlh : lo ≤ hi) (hhi : hi ≤ S.μ)
    (hact : ∀ i, lo ≤ i → i < hi → m ztde < S.μ)
    (hinj : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m ztde = m ztjme →
      i = i')
    (h2tmp : ∀ i, lo ≤ i → i < hi → m2 ztid = m ztde)
    (h2df : ∀ i, lo ≤ i → i < hi → (m2 ztxnb = 1 ↔ mk i))
    (hsum : cntS ztqco lo hi + cntS ztbapf lo hi +
      cntS ztzdc lo hi ≤ hi - lo)
    (huniq : ∀ i, lo ≤ i → i < hi → ¬ (SelI m2 S f f i ∧ SelI m2 S ztwmt f i) ∧
      ¬ (SelI m2 S f f i ∧ SelI m2 S ztbpq f i) ∧
      ¬ (SelI m2 S ztwmt f i ∧ SelI m2 S ztbpq f i))
    (hsmk : ∀ i, lo ≤ i → i < hi → (SelI m2 S f f i ∨ SelI m2 S ztwmt f i ∨
      SelI m2 S ztbpq f i) → ¬ mk i) :
    let s0 := SelI m2 S f f
    let s1 := SelI m2 S ztwmt f
    let s2 := SelI m2 S ztbpq f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    let mS := sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo ztcw
    (∀ x, ¬ ztjmf → ¬ ztclw →
      mS x = m2 x) ∧
    (∀ i, lo ≤ i → i < hi → s0 i → mS ztkql = m ztde) ∧
    (∀ i, lo ≤ i → i < hi → s1 i → mS ztkqj = m ztde) ∧
    (∀ i, lo ≤ i → i < hi → s2 i → mS ztkqk = m ztde) ∧
    (∀ i, lo ≤ i → i < hi → mk i → mS ztwxy = S.μ) ∧
    (∀ i, lo ≤ i → i < hi → s0 i → mS ztwxy = lo + cntS s0 lo i) ∧
    (∀ i, lo ≤ i → i < hi → s1 i → mS ztwxy = e1 + cntS s1 lo i) ∧
    (∀ i, lo ≤ i → i < hi → s2 i → mS ztwxy = e2 + cntS s2 lo i) ∧
    (∀ w, w < S.μ → (∀ i, lo ≤ i → i < hi → m ztde ≠ w) →
      mS zteob = m2 zteob) ∧
    (passC m2 S lo hi f).2 = e3 := by
  intro s0 s1 s2 e1 e2 e3 mS
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU
  have hit : ztxpy := fun i a b => by
    grind
  have hinj2 : ∀ i i', lo ≤ i → i < hi → lo ≤ i' → i' < hi → m2 ztid = m2 ztnpc →
      i = i' := fun i i' a b c d e => hinj i i' a b c d by_grind
  obtain ⟨A1, A2, A3, A4, A5, A6⟩ := passes_spec hL (f := f) hlh hhi hit hinj2 hsum
  have hu : ∀ i t t', lo ≤ i → i < hi → ztdxz →
      ztdya → t = t' := by
    intro i t t' a b h1 h2
    obtain ⟨u1, u2, u3⟩ := huniq i a b
    rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
      rcases h2 with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;> first | rfl | tauto
  obtain ⟨P0, P1, P2⟩ := A6 hu
  set mP := (passC m2 S lo hi f).1 with hmP
  -- `TMP` and the marks are untouched by the passes
  have hPt : ∀ i, lo ≤ i → i < hi → mP ztid = m ztde := by
    zujbd
    rw [A4 _ by_omega (fun i' c d _ => by have := hit i' c d; omega)]
    exact h2tmp i a b
  have hPd : ∀ i, lo ≤ i → i < hi → mP ztxnb = m2 ztxnb := by
    zujbd
    have := hact i a b
    exact A4 _ by_omega (fun i' c d _ => by have := hit i' c d; omega)
  -- the release condition
  have hrel : ∀ x, (∃ i, lo ≤ i ∧ i < lo + ztcw ∧ mP (S.bDF + mP ztid) = 1 ∧
      x = S.bPOS + mP ztid) ↔ ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m (S.bACT + i) := by
    zugop
    constructor
    · zufmg
      rw [hPt i a by_omega] at c d
      rw [hPd i a by_omega] at c
      exact ⟨i, a, by_omega, (h2df i a by_omega).mp c, d⟩
    · zufmg
      refine ⟨i, a, by_omega, ?_, by rw [hPt i a b]; exact d⟩
      rw [hPt i a b, hPd i a b]; exact (h2df i a b).mpr c
  have hmS : ∀ x, mS x = if ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m ztde
      then S.μ else mP x := by
    zugop
    show sepMem mP S.bTMP S.bPOS S.bDF S.μ lo ztcw x = _
    rw [sepMem_apply]
    by_cases h : ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m ztde
    · rw [ite_eq_left ((hrel x).mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((hrel x).mp h')), ite_eq_right h]
  have hnoPOS : ∀ x, ¬ ztclw →
      ¬ ∃ i, lo ≤ i ∧ i < hi ∧ mk i ∧ x = S.bPOS + m ztde := by
    rintro x hx ⟨i, a, b, -, rfl⟩
    have := hact i a b; omega
  have hnotmk : ∀ i, lo ≤ i → i < hi → ztmnk →
      ¬ ∃ i', lo ≤ i' ∧ i' < hi ∧ mk i' ∧ S.bPOS + m ztde = S.bPOS + m ztjme := by
    rintro i a b hs ⟨i', c, d, e, g⟩
    have := hinj i i' a b c d by_omega
    zumo
    exact hsmk i a b hs e
  refine ⟨fun x h1 h2 => ?_, fun i a b h => ?_, fun i a b h => ?_, fun i a b h => ?_,
    fun i a b h => ?_, fun i a b h => ?_, fun i a b h => ?_, fun i a b h => ?_,
    fun w hw hn => ?_, A5⟩
  · rw [hmS, ite_eq_right (hnoPOS x h2)]
    exact A4 x h1 (fun i c d _ => by have := hit i c d; omega)
  · have := cntS_lt a b h (i' := hi)
    zufwg
    zunjp; rw [A1 i a b h, h2tmp i a b]
  · have := cntS_lt a b h (i' := hi)
    zufwg
    zunjp; rw [A2 i a b h, h2tmp i a b]
  · have := cntS_lt a b h (i' := hi)
    zufwg
    zunjp; rw [A3 i a b h, h2tmp i a b]
  · rw [hmS, ite_eq_left ⟨i, a, b, h, rfl⟩]
  · rw [hmS, ite_eq_right (hnotmk i a b zteg), ← h2tmp i a b, P0 i a b h]
  · rw [hmS, ite_eq_right (hnotmk i a b ztwkb), ← h2tmp i a b, P1 i a b h]
  · rw [hmS, ite_eq_right (hnotmk i a b ztwxb), ← h2tmp i a b, P2 i a b h]
  · rw [hmS, ite_eq_right (by rintro ⟨i, a, b, -, e⟩; exact hn i a b by_omega)]
    refine A4 _ by_omega (fun i c d _ => ?_)
    rw [h2tmp i c d]
    zuchf
    exact hn i c d by_omega
end
section static
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}

/-- **The static facts only read the static slots.** -/
theorem SFacts.of_static {S : SS} {A0 U : ℕ} {m m' : ℕ → ℕ}
    (h : SFacts M T a ha C R first preE slot upT k c S A0 U W m) (he : StaticEq A0 U m m') :
    SFacts M T a ha C R first preE slot upT k c S A0 U W m' := by
  zuiwg
  have := hL.hFIRST; have := hL.hLEV; have := hL.hPV; have := hL.hFP; have := hL.hATT
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ; have := hL.hFPRE
  have := hL.hLBOT; have := hL.hLTOP; have := hL.hHALF; have := hL.hPOW; have := hL.hUPT
  have := hL.hUP; have := hL.hμU; have := hL.hNU; have := hL.hLU; have := hL.hVERT
  have := hL.hOPP; have hN := h.hN; have hμ := h.hμ
  have hlt : ∀ v : Fin μ, (v : ℕ) < μ := fun v => v.2
  have hltN : ∀ d : Fin N, (d : ℕ) < N := fun d => d.2
  refine ⟨hL, hN, hμ, h.planar, h.vert_first, fun d => ?_, fun d => ?_, fun v => ?_, fun v => ?_,
    h.lev_lt, fun d => ?_, fun d => ?_, fun x => ?_, fun x => ?_, fun g hg => ?_, fun g hg => ?_,
    h.r0, fun g hg => ?_, fun g hg => ?_, h.R_ok, h.R_n, h.R_up, h.R_root, h.R_pre,
    fun j hj g hg => ?_, h.upT_eq, h.upT_lt, fun x hx => ?_, fun j hj x hx => ?_,
    fun j hj => ?_, h.pow_big, h.pow_U, h.L_pos, fun w hw => ?_, fun v x hvx => ?_, fun v => ?_⟩
  · have := hltN d; zumxa; exact h.vert d
  · have := hltN d; zumxa; exact h.opp d
  · have := hlt v; zumxa; exact h.first v
  · have := hlt v; zumxa; exact h.lev v
  · have := hltN d; zumxa; exact h.att d
  · have := hltN d; zumxa; exact h.fp d
  · have := enc_lt x
    zumxa; exact h.so x
  · have := enc_lt x
    zumxa; exact h.sf x
  · have := hltN g; zumxa; exact h.fpar g hg
  · zumxa; exact h.fpar_lt g hg
  · zumxa; exact h.pre g hg
  · zumxa; exact h.sz g hg
  · zumxa; exact h.up_tab j hj g hg
  · zumxa; exact h.pv x hx
  · zumxa; exact h.upt_tab j hj x hx
  · zumxa; exact h.pow j hj
  · zumxa; exact h.half w hw
  · have := h.lev_lt v
    zunrp; exact h.win v x hvx
  · have := h.lev_lt v
    zunrp; exact h.win_k v
end static
section stack
variable {μ k s : ℕ} {H : Finset ℕ} {slab : ℕ → ℕ} {Adj : ℕ → ℕ → Prop}

/-- **The stack has at most `μ` entries** (each of them contributes at least `2` to the
potential `pot2`). -/
theorem SInv.length_le {act : ℕ → ℕ} {stk : List ztw} {fin : Finset ztw}
    {D : Finset ℕ} {nsp : ℕ} (hI : SInv μ k s H slab Adj act stk fin D nsp) :
    stk.length ≤ μ := by
  have h2 := hI.pot2
  have hge : ∑ p ∈ stk.toFinset, 2 ≤ ∑ p ∈ stk.toFinset, ztcyr :=
    Finset.sum_le_sum (fun p hp => by
      have := hI.big p (List.mem_toFinset.mp hp); omega)
  rw [Finset.sum_const, List.toFinset_card_of_nodup hI.nodup, smul_eq_mul] at hge
  omega
end stack
section m2
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {W : ℕ}
open Classical in
/-- **The memory after the marks and the copy.** -/
theorem m2_facts {S : SS} {A0 U : ℕ} {m : ℕ → ℕ} {lo hi : ℕ} {rest : List ztw}
    {fin : Finset ztw} {D : Finset ℕ} {nsp : ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W m)
    (hD : DInv M T k c S m (ztdz :: rest) fin D nsp) {lbot ltop : ℕ}
    (hwin : ∀ x : Fin μ, (x : ℕ) ∈ items ztwjj ztdz →
      lbot ≤ T.level x ∧ T.level x ≤ ltop) (f : Fin N) :
    let m2 := copyF (marksF m S lo hi lbot ltop upT f) S lo hi
    (∀ x, ¬ ztclv → ¬ ztcto →
      m2 x = m x) ∧
    (∀ i, lo ≤ i → i < hi → m2 (S.bTMP + i) = m (S.bACT + i)) ∧
    (∀ y, y < μ → m2 (S.bDF + y) =
      if y ∈ items ztwjj ztdz ∧ markN T a f y then 1 else m ztjmi) ∧
    m2 (S.bFP + f) = M.fperm f := by
  intro m2
  zuglp
  have := hL.hFP; have := hL.hACT
  have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU; have := hL.hNU
  have := hL.hLEV
  zubti

  have hmk := fun (y : ℕ) (hy : y < μ) => marksF_df (m0 := m) (S := S) (lo := lo) (hi := hi)
    (lbot := lbot) (ltop := ltop) T hSF.upT_eq ztgjs
    hμ ztnzo hwin hSF.lev hSF.vert hSF.opp hSF.att
    ztzfx f zthnw
  have hmo : ztxfn := by
    zuh
    have hup : ztlcc := fun x hx => by
      zufnr
    zufws

    rw [markStep_other hup ztlhp hx,
      markStep_other hup ztlhq hx,
      markStep_other hup ztnto hx]
  have hm2 : ∀ x, ¬ ztclv → ¬ ztcto →
      m2 x = m x := by
    zuchi
    show copyF _ S lo hi x = m x
    zugio

  refine ⟨hm2, fun i h1 h2 => ?_, fun y hy => ?_, ?_⟩
  · show copyF _ S lo hi _ = _
    zugio

  · show copyF _ S lo hi _ = _
    zugio

  · zufuq
    zuged
