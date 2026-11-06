module

public import Chazelle.Core.ClusterMarkRam
public import Chazelle.Core.ClusterSepRam
public import Chazelle.Core.ClusterArr

/-!
# WP-I, part 32: the split step on the RAM

The static layout `SS` of the split step (bases of the read-only arrays, the table length `L`,
`N`, `μ`, `s`), the registers holding it (`SS.Regs`), and the pieces of the split step of the
segment `[lo, hi)`:

* `medB`: `W := hi - lo`, the median face `y := FIRST[ACT[lo + HALF[W]]]` and the level window
  `lbot := LBOT[ℓ]`, `ltop := LTOP[ℓ]` of `ℓ = LEV[ACT[lo]]`;
* the climb (`climbStmt`), the three corners and their marks (`markStmt`), the copy of the
  segment to `TMP` (`shStmt`), the three class passes (`cpStmt`, `passStmt`), the release of the
  separator (`sepStmt`), the pushes (`pushOne`).

`splitStmt` is the whole step.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The static layout of the split step. -/
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
    r = 130340 ∨ (130341 ≤ r ∧ r ≤ 130344) ∨ r = 130600 ∨ (130609 ≤ r ∧ r ≤ 130619) ∨
    (130630 ≤ r ∧ r ≤ 130631) ∨ (130637 ≤ r ∧ r ≤ 130642) ∨ (130656 ≤ r ∧ r ≤ 130661) ∨
    (130550 ≤ r ∧ r ≤ 130556) ∨ (130676 ≤ r ∧ r ≤ 130679) ∨ (130670 ≤ r ∧ r ≤ 130673) ∨
    r = 130690 ∨ r = 130691 ∨ r = 130693 ∨ (130702 ≤ r ∧ r ≤ 130703)

theorem SS.Regs.of_frame {S : SS} {c c' : Config} (h : S.Regs c)
    (hr : ∀ r, ¬ SplitRG r → c'.nreg r = c.nreg r) : S.Regs c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by unfold SplitRG; omega)]; assumption)

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
  m (S.bDF + m (S.bTMP + i)) ≠ 1 ∧
    inClass (fun x => m (S.bSO + x)) (fun x => m (S.bSF + x)) (fun x => m (S.bFPAR + x))
      (fun x => m (S.bFPRE + x)) (fun x => m (S.bFSZ + x)) 0 X f
      (m (S.bFPRE + m (S.bFIRST + m (S.bTMP + i))))

section proofs

variable {P : Polygon} {W : ℕ}

/-- **The median face and the level window.** -/
theorem medB_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c) {lo hi : ℕ}
    (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hwH : S.bHALF + (hi - lo) ≤ W)
    (hwm : S.bACT + (c.nmem (S.bHALF + (hi - lo)) + lo) ≤ W)
    (hwf : S.bFIRST + c.nmem (S.bACT + (c.nmem (S.bHALF + (hi - lo)) + lo)) ≤ W)
    (hwa : S.bACT + lo ≤ W) (hwl : S.bLEV + c.nmem (S.bACT + lo) ≤ W)
    (hwb : S.bLBOT + c.nmem (S.bLEV + c.nmem (S.bACT + lo)) ≤ W)
    (hwt : S.bLTOP + c.nmem (S.bLEV + c.nmem (S.bACT + lo)) ≤ W) :
    ∃ c' k, Exec P W medB c c' k ∧ k = 16 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130302 = hi - lo ∧
      c'.nreg 130340 = c.nmem (S.bFIRST + c.nmem (S.bACT + (c.nmem (S.bHALF + (hi - lo)) + lo))) ∧
      c'.nreg 130609 = c.nmem (S.bLBOT + c.nmem (S.bLEV + c.nmem (S.bACT + lo))) ∧
      c'.nreg 130610 = c.nmem (S.bLTOP + c.nmem (S.bLEV + c.nmem (S.bACT + lo))) ∧
      c'.nreg 130300 = lo ∧ c'.nreg 130301 = hi ∧
      (∀ r, ¬ SplitRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold medB
  exec_block
  all_goals try (config_simp; simp only [hlo, hhi, hR.rHALF, hR.cACT, hR.cFIRST, hR.mLEV,
    hR.rLBOT, hR.rLTOP]; omega)
  refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [hlo, hhi, hR.rHALF, hR.cACT, hR.cFIRST, hR.mLEV,
    hR.rLBOT, hR.rLTOP]; done)
  simp only [Machine.upd_apply]; unfold SplitRG at hr; split_ifs <;> omega

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
  if lbot ≤ min (m (S.bLEV + u)) ltop then
    markMem m S.bPOS S.bDF lo hi up (up^[m (S.bLEV + u) - min (m (S.bLEV + u)) ltop] u)
      (min (m (S.bLEV + u)) ltop + 1 - lbot)
  else m

theorem markStep_other {m : ℕ → ℕ} {S : SS} {lo hi lbot ltop : ℕ} {up : ℕ → ℕ} {u : ℕ}
    (hup : ∀ x, x < S.μ → up x < S.μ) (hu : u < S.μ) {a : ℕ}
    (ha : ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ)) : markStep m S lo hi lbot ltop up u a = m a := by
  classical
  unfold markStep
  split_ifs
  · unfold markMem
    rw [ite_eq_right]
    rintro ⟨x, rfl, -, -, i', -, rfl⟩
    have := iterate_lt_of hup i' (iterate_lt_of hup (m (S.bLEV + u) - min (m (S.bLEV + u)) ltop) hu)
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
  · rw [hm _ (by omega)]; exact h.pv x hx
  · have : j * μ + μ ≤ L * μ := by
      have := Nat.mul_le_mul_right μ (show j + 1 ≤ L by omega); rwa [Nat.succ_mul] at this
    rw [hm _ (by omega)]; exact h.tab j hj x hx
  · rw [hm _ (by omega)]; exact h.pow j hj
  · rw [hm _ (by omega)]; exact h.lev_lt x hx
  · rw [hm _ (by omega)]; exact h.lev_mu x hx

section proofs

variable {P : Polygon} {W : ℕ}

/-- **The three corners and their marks.** -/
theorem marksS_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    {lo hi lbot ltop f : ℕ} {up : ℕ → ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hbot : c.nreg 130609 = lbot) (htop : c.nreg 130610 = ltop) (hf : c.nreg 130344 = f)
    (hM : MarkMem c.nmem W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ up)
    {u0 u1 u2 : ℕ} (hu0 : c.nmem (S.bVERT + f) = u0)
    (hu1 : c.nmem (S.bVERT + c.nmem (S.bOPP + f)) = u1)
    (hu2 : c.nmem (S.bVERT + c.nmem (S.bATT + f)) = u2)
    (h0 : u0 < S.μ) (h1 : u1 < S.μ) (h2 : u2 < S.μ)
    (hw0 : S.bVERT + f ≤ W) (hw1 : S.bOPP + f ≤ W) (hw2 : S.bATT + f ≤ W)
    (hw1' : S.bVERT + c.nmem (S.bOPP + f) ≤ W) (hw2' : S.bVERT + c.nmem (S.bATT + f) ≤ W)
    (hd : ∀ a, (a = S.bVERT + f ∨ a = S.bOPP + f ∨ a = S.bATT + f ∨
      a = S.bVERT + c.nmem (S.bOPP + f) ∨ a = S.bVERT + c.nmem (S.bATT + f)) →
      ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ)) :
    ∃ c' k, Exec P W marksS c c' k ∧ k ≤ 3 * (12 * S.L + 12 * (ltop + 1 - lbot) + 34) ∧
      WordsBounded W c' ∧
      c'.nmem = markStep (markStep (markStep c.nmem S lo hi lbot ltop up u0) S lo hi lbot ltop
        up u1) S lo hi lbot ltop up u2 ∧
      (∀ r, ¬ SplitRG r → c'.nreg r = c.nreg r) ∧ c'.nreg 130344 = f ∧ c'.nreg 130300 = lo ∧
      c'.nreg 130301 = hi ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the marking context in every configuration of the frame
  have ctx : ∀ c1 : Config, (∀ r, ¬ SplitRG r → c1.nreg r = c.nreg r) →
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
      (∀ r, ¬ SplitRG r → c1.nreg r = c.nreg r) → c1.nreg 130300 = lo →
      c1.nreg 130301 = hi → c1.nreg 130609 = lbot → c1.nreg 130610 = ltop →
      c1.nreg 130344 = f → u < S.μ →
      (∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) → c1.nmem a = c.nmem a) →
      (∃ c2 k2, Exec P W cb c1 c2 k2 ∧ k2 ≤ 4 ∧ WordsBounded W c2 ∧ c2.nreg 130600 = u ∧
        (∀ r, r ≠ 130600 → r ≠ 130693 → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧
        c2.rmem = c1.rmem ∧ c2.output = c1.output ∧ c2.nmem = c1.nmem) →
      ∃ c3 k3, Exec P W (.seq cb markStmt) c1 c3 k3 ∧
        k3 ≤ 12 * S.L + 12 * (ltop + 1 - lbot) + 34 ∧ WordsBounded W c3 ∧
        c3.nmem = markStep c1.nmem S lo hi lbot ltop up u ∧
        (∀ r, ¬ SplitRG r → c3.nreg r = c.nreg r) ∧ c3.nreg 130300 = lo ∧
        c3.nreg 130301 = hi ∧ c3.nreg 130609 = lbot ∧ c3.nreg 130610 = ltop ∧
        c3.nreg 130344 = f ∧ c3.rreg = c1.rreg ∧ c3.rmem = c1.rmem ∧ c3.output = c1.output := by
    intro cb c1 u hw1 hr1 h1 h2 h3 h4 h5 hu hm1 ⟨c2, k2, e2, hk2, hw2, h2u, h2r, hrr2, hrm2, ho2,
      hm2⟩
    have hr2 : ∀ r, ¬ SplitRG r → c2.nreg r = c.nreg r := fun r hr =>
      (h2r r (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega)).trans (hr1 r hr)
    have hC2 := ctx c2 hr2 (by rwa [h2r _ (by omega) (by omega)])
      (by rwa [h2r _ (by omega) (by omega)]) (by rwa [h2r _ (by omega) (by omega)])
      (by rwa [h2r _ (by omega) (by omega)])
    have hM2 : MarkMem c2.nmem W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ up :=
      hM.congr (fun a ha => by rw [hm2]; exact hm1 a ha)
    obtain ⟨c3, k3, e3, hk3, hw3, hm3, h3r, hrr3, hrm3, ho3⟩ := markStmt_exec (P := P) hw2 hC2 hM2
      h2u hu
    refine ⟨c3, k2 + k3, .seq e2 e3, by omega, hw3, by rw [hm3, hm2]; rfl, fun r hr => ?_, ?_, ?_,
      ?_, ?_, ?_, hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2⟩
    · rw [h3r r (by unfold MarkRG; unfold SplitRG at hr; omega)]; exact hr2 r hr
    all_goals rw [h3r _ (by unfold MarkRG; omega), h2r _ (by omega) (by omega)]; assumption
  have hmr : ∀ (m : ℕ → ℕ), (∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) → m a = c.nmem a) →
      ∀ u, u < S.μ → ∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) →
        markStep m S lo hi lbot ltop up u a = c.nmem a := fun m hm u hu a ha => by
    rw [markStep_other hup hu ha]; exact hm a ha
  -- corner 0
  obtain ⟨c3, k3, e3, hk3, hw3, hm3, hr3, h3lo, h3hi, h3b, h3t, h3f, hrr3, hrm3, ho3⟩ :=
    step c0B c u0 hw (fun _ _ => rfl) hlo hhi hbot htop hf h0 (fun _ _ => rfl) (by
      unfold c0B
      exec_block
      · rwa [hR.rVERT, hf]
      · refine ⟨by omega, ‹_›, by config_simp; rw [hR.rVERT, hf, hu0], fun r h1 h2 => ?_, rfl, rfl,
          rfl, rfl⟩
        simp only [Machine.upd_apply, h1, h2, ite_false])
  -- corner 1
  have hm3' : ∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) → c3.nmem a = c.nmem a := by
    rw [hm3]; exact hmr c.nmem (fun _ _ => rfl) u0 h0
  have hR3 := hR.of_frame hr3
  obtain ⟨c4, k4, e4, hk4, hw4, hm4, hr4, h4lo, h4hi, h4b, h4t, h4f, hrr4, hrm4, ho4⟩ :=
    step c1B c3 u1 hw3 hr3 h3lo h3hi h3b h3t h3f h1 hm3' (by
      have r1 := hm3' (S.bOPP + f) (hd _ (Or.inr (Or.inl rfl)))
      have r2 := hm3' (S.bVERT + c.nmem (S.bOPP + f)) (hd _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      unfold c1B
      exec_block
      all_goals try (config_simp; simp only [hR3.rOPP, hR3.rVERT, h3f, r1]; omega)
      refine ⟨by omega, ‹_›, by config_simp; simp only [hR3.rOPP, hR3.rVERT, h3f, r1, r2, hu1],
        fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, ite_false])
  -- corner 2
  have hm4' : ∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) → c4.nmem a = c.nmem a := by
    rw [hm4]; exact hmr c3.nmem hm3' u1 h1
  have hR4 := hR.of_frame hr4
  obtain ⟨c5, k5, e5, hk5, hw5, hm5, hr5, h5lo, h5hi, h5b, h5t, h5f, hrr5, hrm5, ho5⟩ :=
    step c2B c4 u2 hw4 hr4 h4lo h4hi h4b h4t h4f h2 hm4' (by
      have r1 := hm4' (S.bATT + f) (hd _ (Or.inr (Or.inr (Or.inl rfl))))
      have r2 := hm4' (S.bVERT + c.nmem (S.bATT + f)) (hd _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      unfold c2B
      exec_block
      all_goals try (config_simp; simp only [hR4.rATT, hR4.rVERT, h4f, r1]; omega)
      refine ⟨by omega, ‹_›, by config_simp; simp only [hR4.rATT, hR4.rVERT, h4f, r1, r2, hu2],
        fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, ite_false])
  refine ⟨c5, k3 + (k4 + k5), .seq e3 (.seq e4 e5), by omega, hw5, by rw [hm5, hm4, hm3], hr5,
    h5f, h5lo, h5hi, by rw [hrr5, hrr4, hrr3], by rw [hrm5, hrm4, hrm3], by rw [ho5, ho4, ho3]⟩


/-- A class pass: the class parameters of `X`, then the pass. -/
def classPass : Stmt := .seq cpStmt passStmt

/-- The pass memory facts from the slot layout. -/
theorem SS.Lay.passMem {S : SS} {A0 U W : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {lo hi : ℕ}
    (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m (S.bTMP + i) < S.μ)
    (hfirst : ∀ v, v < S.μ → m (S.bFIRST + v) < S.N) :
    PassMem m W lo hi S.bTMP S.bACT S.bPOS S.bDF S.bFIRST S.bFPRE S.μ S.N := by
  have := hL.hFIRST; have := hL.hFPRE; have := hL.hACT; have := hL.hPOS; have := hL.hTMP
  have := hL.hDF; have := hL.hμU; have := hL.hNU; have := hL.hW
  have : 0 ≤ S.L * U := Nat.zero_le _
  refine ⟨hlh, hit, hfirst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

/-- **A class pass.** -/
theorem classPass_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    (hL : S.Lay A0 U W) {lo hi X f e : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hX : c.nreg 130630 = X) (hf : c.nreg 130631 = f) (he : c.nreg 130656 = e)
    (hXN : X < 3 * S.N) (hfN : f < S.N)
    (hCp : CpMem c.nmem W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → c.nmem (S.bTMP + i) < S.μ)
    (hfirst : ∀ v, v < S.μ → c.nmem (S.bFIRST + v) < S.N) (hloe : lo ≤ e)
    (hfin : (passMem c.nmem (SelI c.nmem S X f) S.bACT S.bPOS S.bTMP lo e (hi - lo)).2 ≤ hi) :
    ∃ c' k, Exec P W classPass c c' k ∧ k ≤ 32 * (hi - lo) + 48 ∧ WordsBounded W c' ∧
      c'.nmem = (passMem c.nmem (SelI c.nmem S X f) S.bACT S.bPOS S.bTMP lo e (hi - lo)).1 ∧
      c'.nreg 130656 = (passMem c.nmem (SelI c.nmem S X f) S.bACT S.bPOS S.bTMP lo e
        (hi - lo)).2 ∧
      (∀ r, ¬ (CpRG r ∨ PassRG r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hr1, hrr1, hrm1, ho1, htest⟩ := cpStmt_exec (P := P) hw
    hR.zero hX hf hR.pSO hR.pSF hR.pFPAR hR.pPR hR.pSZ hCp hXN hfN
  have hsel : SelP c.nmem S.bTMP S.bDF S.bFIRST S.bFPRE (c1.nreg 130637) (c1.nreg 130638)
      (c1.nreg 130639) = SelI c.nmem S X f := by
    funext i
    unfold SelP SelI
    rw [htest]
  have r1 : ∀ r, ¬ CpRG r → c1.nreg r = c.nreg r := hr1
  have hC : PassCtx c1 lo hi (c1.nreg 130637) (c1.nreg 130638) (c1.nreg 130639) S.bTMP S.bACT
      S.bPOS S.bDF S.bFIRST S.bFPRE := by
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [r1 _ (by unfold CpRG; omega)]
    exacts [hR.one, hR.zero, hlo, hhi, hR.aTMP, hR.aACT, hR.aPOS, hR.aDF, hR.aFIRST, hR.aFPRE]
  have hPM := hL.passMem (m := c1.nmem) hlh hhiμ (by rwa [hm1])
    (by rwa [hm1])
  rw [← hm1] at hsel
  obtain ⟨c2, k2, e2, hk2, hw2, hm2, hp2, hr2, hrr2, hrm2, ho2⟩ := passStmt_exec (P := P) hw1 hC hPM
    hloe (by rwa [r1 _ (by unfold CpRG; omega)]) (by rwa [hsel, hm1])
  refine ⟨c2, k1 + k2, .seq e1 e2, by omega, hw2, by rw [hm2, hsel, hm1], by rw [hp2, hsel, hm1],
    fun r hr => ?_, hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
  rw [hr2 r (fun h => hr (Or.inr h)), r1 r (fun h => hr (Or.inl h))]

/-- **The selection only reads the static arrays, `TMP` and `DF`.** -/
theorem SelI_congr {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m m' : ℕ → ℕ}
    (hCp : CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N) {lo hi X f : ℕ}
    (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m (S.bTMP + i) < S.μ)
    (hfirst : ∀ v, v < S.μ → m (S.bFIRST + v) < S.N) (hXN : X < 3 * S.N) (hfN : f < S.N)
    (hm : ∀ a, ¬ (S.bACT ≤ a ∧ a < S.bACT + S.μ) → ¬ (S.bPOS ≤ a ∧ a < S.bPOS + S.μ) →
      m' a = m a) :
    ∀ i, lo ≤ i → i < hi → (SelI m' S X f i ↔ SelI m S X f i) := by
  intro i h1 h2
  have := hL.hFIRST; have := hL.hFPRE; have := hL.hACT; have := hL.hPOS; have := hL.hTMP
  have := hL.hDF; have := hL.hμU; have := hL.hNU; have := hL.hSO; have := hL.hSF
  have := hL.hFPAR; have := hL.hFSZ
  have hv := hit i h1 h2
  have e1 : m' (S.bTMP + i) = m (S.bTMP + i) := hm _ (by omega) (by omega)
  have e2 : m' (S.bDF + m (S.bTMP + i)) = m (S.bDF + m (S.bTMP + i)) := hm _ (by omega) (by omega)
  have hfv := hfirst _ hv
  have e3 : m' (S.bFIRST + m (S.bTMP + i)) = m (S.bFIRST + m (S.bTMP + i)) :=
    hm _ (by omega) (by omega)
  have e4 : m' (S.bFPRE + m (S.bFIRST + m (S.bTMP + i))) =
      m (S.bFPRE + m (S.bFIRST + m (S.bTMP + i))) := hm _ (by omega) (by omega)
  have hso := hCp.so_lt X hXN
  have e5 : m' (S.bSO + X) = m (S.bSO + X) := hm _ (by omega) (by omega)
  have hsf := hCp.sf_lt _ hso
  have e6 : m' (S.bSF + m (S.bSO + X)) = m (S.bSF + m (S.bSO + X)) := hm _ (by omega) (by omega)
  have e7 : ∀ g, g < S.N → m' (S.bFPAR + g) = m (S.bFPAR + g) ∧
      m' (S.bFPRE + g) = m (S.bFPRE + g) ∧ m' (S.bFSZ + g) = m (S.bFSZ + g) := fun g hg =>
    ⟨hm _ (by omega) (by omega), hm _ (by omega) (by omega), hm _ (by omega) (by omega)⟩
  obtain ⟨g1, g2, g3⟩ := e7 _ hsf
  obtain ⟨f1, f2, f3⟩ := e7 f hfN
  have hfp := hCp.fp_lt f hfN
  have e8 : m' (S.bSO + m (S.bFPAR + f)) = m (S.bSO + m (S.bFPAR + f)) :=
    hm _ (by omega) (by omega)
  unfold SelI inClass
  simp only [e1, e2, e3, e4, e5, e6, g1, g2, g3, f1, f2, f3, e8]

theorem CpMem.congr_lay {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m m' : ℕ → ℕ}
    (hCp : CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hm : ∀ a, ¬ (S.bACT ≤ a ∧ a < S.bACT + S.μ) → ¬ (S.bPOS ≤ a ∧ a < S.bPOS + S.μ) →
      m' a = m a) : CpMem m' W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N := by
  have := hL.hFPRE; have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hNU
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ
  refine ⟨hCp.wSO, hCp.wSF, hCp.wFP, hCp.wPR, hCp.wSZ, fun x hx => ?_, fun x hx => ?_,
    fun g hg => ?_, fun g hg => ?_⟩
  · rw [hm _ (by omega) (by omega)]; exact hCp.so_lt x hx
  · rw [hm _ (by omega) (by omega)]; exact hCp.sf_lt x hx
  · rw [hm _ (by omega) (by omega)]; exact hCp.fp_lt g hg
  · rw [hm _ (by omega) (by omega), hm _ (by omega) (by omega)]; exact hCp.prsz g hg

/-- A pass keeps everything outside `ACT` and `POS`. -/
theorem passMem_out {S : SS} {A0 U : ℕ} (_hL : S.Lay A0 U W) {m : ℕ → ℕ} {sel : ℕ → Prop}
    {lo hi e : ℕ} (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m (S.bTMP + i) < S.μ)
    (hle : e + cntS sel lo hi ≤ hi) (hlh : lo ≤ hi) :
    ∀ a, ¬ (S.bACT ≤ a ∧ a < S.bACT + S.μ) → ¬ (S.bPOS ≤ a ∧ a < S.bPOS + S.μ) →
      (passMem m sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).1 a = m a := by
  intro a h1 h2
  refine passMem_other m sel (hi - lo) (fun i a b => hit i a (by omega)) ⟨fun h => h1 ?_, h2⟩
  rw [passMem_ptr_eq, show lo + (hi - lo) = hi by omega] at h
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
noncomputable def passA (m : ℕ → ℕ) (S : SS) (lo hi f : ℕ) : (ℕ → ℕ) × ℕ :=
  passMem m (SelI m S f f) S.bACT S.bPOS S.bTMP lo lo (hi - lo)
/-- The second pass. -/
noncomputable def passB (m : ℕ → ℕ) (S : SS) (lo hi f : ℕ) : (ℕ → ℕ) × ℕ :=
  passMem (passA m S lo hi f).1 (SelI m S (2 * S.N + m (S.bFP + f)) f) S.bACT S.bPOS S.bTMP lo
    (passA m S lo hi f).2 (hi - lo)
/-- The third pass. -/
noncomputable def passC (m : ℕ → ℕ) (S : SS) (lo hi f : ℕ) : (ℕ → ℕ) × ℕ :=
  passMem (passB m S lo hi f).1 (SelI m S (S.N + f) f) S.bACT S.bPOS S.bTMP lo
    (passB m S lo hi f).2 (hi - lo)

/-- **The three class passes.** -/
theorem passesS_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    (hL : S.Lay A0 U W) {lo hi f : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hf : c.nreg 130344 = f) (hfN : f < S.N) (hfp : c.nmem (S.bFP + f) < S.N)
    (hCp : CpMem c.nmem W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → c.nmem (S.bTMP + i) < S.μ)
    (hfirst : ∀ v, v < S.μ → c.nmem (S.bFIRST + v) < S.N)
    (hsum : cntS (SelI c.nmem S f f) lo hi + cntS (SelI c.nmem S (2 * S.N + c.nmem (S.bFP + f)) f)
      lo hi + cntS (SelI c.nmem S (S.N + f) f) lo hi ≤ hi - lo) :
    ∃ c' k, Exec P W passesS c c' k ∧ k ≤ 3 * (32 * (hi - lo) + 48) + 20 ∧ WordsBounded W c' ∧
      c'.nmem = (passC c.nmem S lo hi f).1 ∧ c'.nreg 130670 = lo ∧
      c'.nreg 130671 = lo + cntS (SelI c.nmem S f f) lo hi ∧
      c'.nreg 130672 = lo + cntS (SelI c.nmem S f f) lo hi +
        cntS (SelI c.nmem S (2 * S.N + c.nmem (S.bFP + f)) f) lo hi ∧
      c'.nreg 130673 = lo + cntS (SelI c.nmem S f f) lo hi +
        cntS (SelI c.nmem S (2 * S.N + c.nmem (S.bFP + f)) f) lo hi +
        cntS (SelI c.nmem S (S.N + f) f) lo hi ∧
      (∀ r, ¬ SplitRG r → c'.nreg r = c.nreg r) ∧ c'.nreg 130344 = f ∧ c'.nreg 130300 = lo ∧
      c'.nreg 130301 = hi ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set m := c.nmem
  set X1 := 2 * S.N + m (S.bFP + f)
  set sl0 := SelI m S f f
  set sl1 := SelI m S X1 f
  set sl2 := SelI m S (S.N + f) f
  have := hL.hFP; have := hL.hACT; have := hL.hPOS; have := hL.hμU; have := hL.hNU
  have := hL.hTMP; have := hL.hFIRST; have := hL.hW
  have hfr : ∀ (c1 c2 : Config), (∀ r, ¬ (CpRG r ∨ PassRG r) → c2.nreg r = c1.nreg r) →
      ∀ r, ¬ SplitRG r → c2.nreg r = c1.nreg r := fun c1 c2 h r hr =>
    h r (by unfold CpRG PassRG; unfold SplitRG at hr; omega)
  -- the congruences for memories changed only in `ACT` and `POS`
  have transfer : ∀ m' : ℕ → ℕ, (∀ a, ¬ (S.bACT ≤ a ∧ a < S.bACT + S.μ) →
      ¬ (S.bPOS ≤ a ∧ a < S.bPOS + S.μ) → m' a = m a) →
      CpMem m' W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N ∧
      (∀ i, lo ≤ i → i < hi → m' (S.bTMP + i) < S.μ) ∧
      (∀ v, v < S.μ → m' (S.bFIRST + v) < S.N) ∧ m' (S.bFP + f) = m (S.bFP + f) ∧
      ∀ X, X < 3 * S.N → ∀ i, lo ≤ i → i < hi → (SelI m' S X f i ↔ SelI m S X f i) := by
    intro m' hm'
    refine ⟨CpMem.congr_lay hL hCp hm', fun i h1 h2 => ?_, fun v hv => ?_, hm' _ (by omega)
      (by omega), fun X hX => SelI_congr hL hCp hhiμ hit hfirst hX hfN hm'⟩
    · rw [hm' _ (by omega) (by omega)]; exact hit i h1 h2
    · rw [hm' _ (by omega) (by omega)]; exact hfirst v hv
  have hX1 : X1 < 3 * S.N := by simp only [X1]; omega
  have hs0 : lo + cntS sl0 lo hi ≤ hi := by omega
  have hs1 : lo + cntS sl0 lo hi + cntS sl1 lo hi ≤ hi := by omega
  have hs2 : lo + cntS sl0 lo hi + cntS sl1 lo hi + cntS sl2 lo hi ≤ hi := by omega
  have hX2 : S.N + f < 3 * S.N := by omega
  have hsp : ∀ (sel : ℕ → Prop) (m' : ℕ → ℕ) (e : ℕ),
      (passMem m' sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).2 = e + cntS sel lo hi := by
    intro sel m' e
    rw [passMem_ptr_eq, show lo + (hi - lo) = hi by omega]
  -- block 0
  obtain ⟨c1, k1, e1, hk1, hw1, h1a, h1b, h1c, h1d, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      pB0 c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 130656 = lo ∧ c1.nreg 130670 = lo ∧
      c1.nreg 130630 = f ∧ c1.nreg 130631 = f ∧
      (∀ r, r ≠ 130656 → r ≠ 130670 → r ≠ 130630 → r ≠ 130631 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    unfold pB0
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact hlo, by config_simp; exact hlo, by config_simp; exact hf,
      by config_simp; exact hf, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
  have hR1 := hR.of_frame (fun r hr => h1r r (by unfold SplitRG at hr; omega)
    (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega)
    (by unfold SplitRG at hr; omega))
  have g1 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 → c1.nreg r = c.nreg r := fun r hr =>
    h1r r (by omega) (by omega) (by omega) (by omega)
  -- pass 0
  obtain ⟨c2, k2, e2, hk2, hw2, hm2, hp2, hr2, hrr2, hrm2, ho2⟩ := classPass_exec (P := P) hw1 hR1
    hL (by rwa [g1 _ (by omega)]) (by rwa [g1 _ (by omega)]) h1c h1d h1a
    (by omega) hfN (by rwa [hm1]) hlh hhiμ (by rwa [hm1])
    (by rwa [hm1]) le_rfl (by rwa [hm1, hsp])
  rw [hm1] at hm2 hp2
  rw [hsp] at hp2
  have hA : (passA m S lo hi f).2 = lo + cntS sl0 lo hi := by unfold passA; rw [hsp]
  have hm2' : c2.nmem = (passA m S lo hi f).1 := hm2
  have hout1 : ∀ a, ¬ (S.bACT ≤ a ∧ a < S.bACT + S.μ) → ¬ (S.bPOS ≤ a ∧ a < S.bPOS + S.μ) →
      c2.nmem a = m a := by
    rw [hm2]; exact passMem_out hL hhiμ hit hs0 hlh
  obtain ⟨cp1, it1, fi1, fp1, se1⟩ := transfer _ hout1
  have hR2 := hR1.of_frame (hfr c1 c2 hr2)
  have g2 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 → c2.nreg r = c1.nreg r :=
    fun r hr => hr2 r (by unfold CpRG PassRG; omega)
  -- block 1
  obtain ⟨c3, k3, e3, hk3, hw3, h3a, h3b, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
      pB1 c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧ c3.nreg 130671 = lo + cntS sl0 lo hi ∧
      c3.nreg 130630 = X1 ∧
      (∀ r, r ≠ 130671 → r ≠ 130693 → r ≠ 130630 → c3.nreg r = c2.nreg r) ∧
      c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
    have hf2 : c2.nreg 130344 = f := by rwa [g2 _ (by omega), g1 _ (by omega)]
    unfold pB1
    exec_block
    all_goals try (config_simp; simp only [hR2.rFP, hR2.r2N, hf2, fp1]; omega)
    refine ⟨rfl, ‹_›, by config_simp; exact hp2, by
      config_simp; simp only [hR2.rFP, hR2.r2N, hf2, fp1]; rfl, fun r h1 h2 h3 => ?_, rfl, rfl,
      rfl, rfl⟩
    simp only [Machine.upd_apply, h1, h2, h3, ite_false]
  have hR3 := hR2.of_frame (fun r hr => h3r r (by unfold SplitRG at hr; omega)
    (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega))
  have g3 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 ∨ r = 130656 →
      c3.nreg r = c2.nreg r := fun r hr => h3r r (by omega) (by omega) (by omega)
  -- pass 1
  have hsel1 : ∀ i, lo ≤ i → i < lo + (hi - lo) → (SelI c2.nmem S X1 f i ↔ sl1 i) :=
    fun i h1 h2 => se1 X1 hX1 i h1 (by omega)
  have hpc1 := passMem_congr_sel (m0 := c2.nmem) (bACT := S.bACT) (bPOS := S.bPOS)
    (bTMP := S.bTMP) (lo := lo) (e := lo + cntS sl0 lo hi) (hi - lo) hsel1
  have hcnt1 : cntS (SelI c2.nmem S X1 f) lo hi = cntS sl1 lo hi :=
    cntS_congr (fun i h1 h2 => hsel1 i h1 (by omega))
  obtain ⟨c4, k4, e4, hk4, hw4, hm4, hp4, hr4, hrr4, hrm4, ho4⟩ := classPass_exec (P := P)
    (lo := lo) (hi := hi) (X := X1) (f := f) (e := lo + cntS sl0 lo hi) hw3 hR3 hL (by rwa [g3 _ (by omega), g2 _ (by omega), g1 _ (by omega)])
    (by rwa [g3 _ (by omega), g2 _ (by omega), g1 _ (by omega)]) h3b
    (by rwa [h3r _ (by omega) (by omega) (by omega), hr2 _ (by unfold CpRG PassRG; omega)])
    (by rwa [g3 _ (by omega)]) hX1 hfN (by rwa [hm3]) hlh hhiμ
    (by rwa [hm3]) (by rwa [hm3]) (by omega)
    (by rwa [hm3, hsp, hcnt1])
  rw [hm3, hpc1] at hm4 hp4
  rw [hsp] at hp4
  have hm4' : c4.nmem = (passB m S lo hi f).1 := by rw [hm4, hm2', ← hA]; rfl
  have hout2 : ∀ a, ¬ (S.bACT ≤ a ∧ a < S.bACT + S.μ) → ¬ (S.bPOS ≤ a ∧ a < S.bPOS + S.μ) →
      c4.nmem a = m a := by
    intro a h1 h2
    rw [hm4, passMem_out hL hhiμ it1 (by omega) hlh a h1 h2]
    exact hout1 a h1 h2
  obtain ⟨cp2, it2, fi2, fp2, se2⟩ := transfer _ hout2
  have hR4 := hR3.of_frame (hfr c3 c4 hr4)
  have g4 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 ∨ r = 130671 →
      c4.nreg r = c3.nreg r := fun r hr => hr4 r (by unfold CpRG PassRG; omega)
  -- block 2
  obtain ⟨c5, k5, e5, hk5, hw5, h5a, h5b, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
      pB2 c4 c5 k5 ∧ k5 = 2 ∧ WordsBounded W c5 ∧
      c5.nreg 130672 = lo + cntS sl0 lo hi + cntS sl1 lo hi ∧ c5.nreg 130630 = S.N + f ∧
      (∀ r, r ≠ 130672 → r ≠ 130630 → c5.nreg r = c4.nreg r) ∧
      c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output ∧ c5.nmem = c4.nmem := by
    have hf4 : c4.nreg 130344 = f := by
      rwa [g4 _ (by omega), g3 _ (by omega), g2 _ (by omega), g1 _ (by omega)]
    unfold pB2
    exec_block
    · config_simp; rw [hR4.rN, hf4]; omega
    · refine ⟨rfl, ‹_›, by config_simp; exact hp4, by config_simp; rw [hR4.rN, hf4],
        fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, ite_false]
  have hR5 := hR4.of_frame (fun r hr => h5r r (by unfold SplitRG at hr; omega)
    (by unfold SplitRG at hr; omega))
  have g5 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 ∨ r = 130671 ∨ r = 130656 →
      c5.nreg r = c4.nreg r := fun r hr => h5r r (by omega) (by omega)
  -- pass 2
  have hsel2 : ∀ i, lo ≤ i → i < lo + (hi - lo) → (SelI c4.nmem S (S.N + f) f i ↔ sl2 i) :=
    fun i h1 h2 => se2 (S.N + f) hX2 i h1 (by omega)
  have hpc2 := passMem_congr_sel (m0 := c4.nmem) (bACT := S.bACT) (bPOS := S.bPOS)
    (bTMP := S.bTMP) (lo := lo) (e := lo + cntS sl0 lo hi + cntS sl1 lo hi) (hi - lo) hsel2
  have hcnt2 : cntS (SelI c4.nmem S (S.N + f) f) lo hi = cntS sl2 lo hi :=
    cntS_congr (fun i h1 h2 => hsel2 i h1 (by omega))
  obtain ⟨c6, k6, e6, hk6, hw6, hm6, hp6, hr6, hrr6, hrm6, ho6⟩ := classPass_exec (P := P)
    (lo := lo) (hi := hi) (X := S.N + f) (f := f) (e := lo + cntS sl0 lo hi + cntS sl1 lo hi)
    hw5 hR5 hL (by rwa [g5 _ (by omega), g4 _ (by omega), g3 _ (by omega), g2 _ (by omega),
      g1 _ (by omega)])
    (by rwa [g5 _ (by omega), g4 _ (by omega), g3 _ (by omega), g2 _ (by omega), g1 _ (by omega)])
    h5b
    (by rwa [h5r _ (by omega) (by omega), hr4 _ (by unfold CpRG PassRG; omega),
      h3r _ (by omega) (by omega) (by omega), hr2 _ (by unfold CpRG PassRG; omega)])
    (by rwa [g5 _ (by omega)]) hX2 hfN (by rwa [hm5]) hlh hhiμ
    (by rwa [hm5]) (by rwa [hm5]) (by omega)
    (by rwa [hm5, hsp, hcnt2])
  rw [hm5, hpc2] at hm6 hp6
  rw [hsp] at hp6
  have hB : (passB m S lo hi f).2 = lo + cntS sl0 lo hi + cntS sl1 lo hi := by
    unfold passB; rw [hsp, hA]
  have hm6' : c6.nmem = (passC m S lo hi f).1 := by rw [hm6, hm4', ← hB]; rfl
  have g6 : ∀ r, r = 130300 ∨ r = 130301 ∨ r = 130344 ∨ r = 130670 ∨ r = 130671 ∨ r = 130672 →
      c6.nreg r = c5.nreg r := fun r hr => hr6 r (by unfold CpRG PassRG; omega)
  -- block 3
  have e7 := Exec.copyN (P := P) hw6 130673 130656
  have kk6 : ∀ r, r ≠ 130673 → upd c6.nreg 130673 (c6.nreg 130656) r = c6.nreg r :=
    fun r hr => Machine.upd_other _ _ _ hr
  have r344 : c6.nreg 130344 = f := by
    rwa [g6 _ (by omega), g5 _ (by omega), g4 _ (by omega), g3 _ (by omega), g2 _ (by omega),
      g1 _ (by omega)]
  have r300 : c6.nreg 130300 = lo := by
    rwa [g6 _ (by omega), g5 _ (by omega), g4 _ (by omega), g3 _ (by omega), g2 _ (by omega),
      g1 _ (by omega)]
  have r301 : c6.nreg 130301 = hi := by
    rwa [g6 _ (by omega), g5 _ (by omega), g4 _ (by omega), g3 _ (by omega), g2 _ (by omega),
      g1 _ (by omega)]
  have r670 : c6.nreg 130670 = lo := by
    rwa [g6 _ (by omega), g5 _ (by omega), g4 _ (by omega), g3 _ (by omega), g2 _ (by omega)]
  have r671 : c6.nreg 130671 = lo + cntS sl0 lo hi := by
    rwa [g6 _ (by omega), g5 _ (by omega), g4 _ (by omega)]
  have r672 : c6.nreg 130672 = lo + cntS sl0 lo hi + cntS sl1 lo hi := by
    rwa [g6 _ (by omega)]
  have hframe : ∀ r, ¬ SplitRG r → c6.nreg r = c.nreg r := fun r hr => by
    rw [hfr c5 c6 hr6 r hr, h5r r (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega),
      hfr c3 c4 hr4 r hr, h3r r (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega)
      (by unfold SplitRG at hr; omega), hfr c1 c2 hr2 r hr, h1r r (by unfold SplitRG at hr; omega)
      (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega)
      (by unfold SplitRG at hr; omega)]
  subst hk1 hk3 hk5
  refine ⟨_, 4 + (k2 + (4 + (k4 + (2 + (k6 + 1))))), .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
    (.seq e6 e7))))), by omega, e7.wb_right, hm6', by dsimp only; rwa [kk6 _ (by omega)],
    by dsimp only; rwa [kk6 _ (by omega)],
    by dsimp only; rwa [kk6 _ (by omega)],
    by dsimp only; simp only [Machine.upd_same]; rw [hp6], fun r hr => by
      dsimp only; rw [kk6 r (by unfold SplitRG at hr; omega)]; exact hframe r hr,
    by dsimp only; rwa [kk6 _ (by omega)], by dsimp only; rwa [kk6 _ (by omega)],
    by dsimp only; rwa [kk6 _ (by omega)], ?_, ?_, ?_⟩
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
    ∃ c' k, Exec P W copyS c c' k ∧ k ≤ 8 * (hi - lo) + 7 ∧ WordsBounded W c' ∧
      (∀ a, c'.nmem a = if S.bTMP + lo ≤ a ∧ a < S.bTMP + hi then
        c.nmem (S.bACT + (a - S.bTMP)) else c.nmem a) ∧
      (∀ r, ¬ SplitRG r → c'.nreg r = c.nreg r) ∧
      (∀ r, r = 130300 ∨ r = 130301 ∨ r = 130302 ∨ r = 130344 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hL.hACT; have := hL.hTMP; have := hL.hμU; have := hL.hW
  have : 0 ≤ S.L * U := Nat.zero_le _
  obtain ⟨c1, k1, e1, hk1, hw1, h1o, h1i, h1n, h1a, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130550 130650 130300, .addN 130551 130320 130300, .subN 130552 130301 130300,
        .copyN 130553 130009]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧
      c1.nreg 130550 = S.bTMP + lo ∧ c1.nreg 130551 = S.bACT + lo ∧ c1.nreg 130552 = hi - lo ∧
      c1.nreg 130553 = 0 ∧ (∀ r, r ≠ 130550 → r ≠ 130551 → r ≠ 130552 → r ≠ 130553 →
        c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧
      c1.nmem = c.nmem := by
    exec_block
    all_goals try (config_simp; simp only [hR.aTMP, hR.cACT, hlo]; omega)
    refine ⟨rfl, ‹_›, by config_simp; simp only [hR.aTMP, hlo], by
      config_simp; simp only [hR.cACT, hlo], by config_simp; rw [hhi, hlo], by
      config_simp; exact hR.zero, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
  have h11 : c1.nreg 130001 = 1 := (h1r _ (by omega) (by omega) (by omega) (by omega)).trans hR.one
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hm2⟩ := shStmt_exec (P := P) hw1 h11 h1o h1i h1n h1a
    (by omega) (by omega) (by omega) (fun i hi => by have := hw1.2 (S.bACT + lo + i); omega)
  refine ⟨c2, k1 + k2, .seq e1 e2, by omega, hw2, fun a => ?_, fun r hr => ?_, fun r hr => ?_,
    by rw [hf2.2.1, hrr1], by rw [hf2.2.2.1, hrm1], by rw [hf2.2.2.2.1, ho1]⟩
  · split_ifs with ha
    · have := hm2 (a - (S.bTMP + lo)) (by omega)
      rw [show S.bTMP + lo + (a - (S.bTMP + lo)) = a by omega, hm1,
        show S.bACT + lo + (a - (S.bTMP + lo)) = S.bACT + (a - S.bTMP) by omega] at this
      omega
    · rw [hf2.2.2.2.2 a (by omega), hm1]
  · rw [hf2.1 r (by unfold ArrRG; unfold SplitRG at hr; omega)]
    exact h1r r (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega)
      (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega)
  · rw [hf2.1 r (by unfold ArrRG; omega)]
    exact h1r r (by omega) (by omega) (by omega) (by omega)

/-- Push the large classes. -/
def pushS : Stmt := .seq (pushOne 0) (.seq (pushOne 1) (pushOne 2))

/-- One push, as a function of the memory and the stack top. -/
noncomputable def pushF (bS s a b : ℕ) (q : (ℕ → ℕ) × ℕ) : (ℕ → ℕ) × ℕ :=
  if s < b - a then (upd (upd q.1 (bS + q.2) a) (bS + q.2 + 1) b, q.2 + 2) else q

theorem pushF_snd_le (bS s a b : ℕ) (q : (ℕ → ℕ) × ℕ) : (pushF bS s a b q).2 ≤ q.2 + 2 := by
  unfold pushF; split_ifs <;> simp

/-- **Push the large classes.** -/
theorem pushS_exec {S : SS} {c : Config} (hw : WordsBounded W c) (hR : S.Regs c)
    {e0 e1 e2 e3 tp : ℕ} (h0 : c.nreg 130670 = e0) (h1 : c.nreg 130671 = e1)
    (h2 : c.nreg 130672 = e2) (h3 : c.nreg 130673 = e3) (htp : c.nreg 130701 = tp)
    (hwS : S.bSTK + tp + 6 ≤ W) :
    ∃ c' k, Exec P W pushS c c' k ∧ k ≤ 27 ∧ WordsBounded W c' ∧
      (c'.nmem, c'.nreg 130701) = pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2
        (pushF S.bSTK S.s e0 e1 (c.nmem, tp))) ∧
      (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130703 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have step : ∀ (t : ℕ) (c1 : Config) (a b : ℕ), t < 3 → WordsBounded W c1 →
      (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130703 → c1.nreg r = c.nreg r) →
      c1.nreg (130670 + t) = a → c1.nreg (130671 + t) = b → S.bSTK + c1.nreg 130701 + 2 ≤ W →
      ∃ c2 k2, Exec P W (pushOne t) c1 c2 k2 ∧ k2 ≤ 9 ∧ WordsBounded W c2 ∧
        (c2.nmem, c2.nreg 130701) = pushF S.bSTK S.s a b (c1.nmem, c1.nreg 130701) ∧
        (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130703 → c2.nreg r = c.nreg r) ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    intro t c1 a b ht hw1 hr1 ha hb hwS1
    obtain ⟨c2, k2, e2, hk2, hw2, hm2, htp2, hr2, hrr2, hrm2, ho2⟩ := pushOne_exec (P := P) hw1 t ht
      ((hr1 _ (by omega) (by omega) (by omega)).trans hR.one) ha hb
      ((hr1 _ (by omega) (by omega) (by omega)).trans hR.rs)
      ((hr1 _ (by omega) (by omega) (by omega)).trans hR.rSTK) rfl hwS1
    refine ⟨c2, k2, e2, hk2, hw2, ?_, fun r h1 h2 h3 => (hr2 r h1 h2 h3).trans (hr1 r h1 h2 h3),
      hrr2, hrm2, ho2⟩
    unfold pushF
    split_ifs with h
    · rw [ite_eq_left h] at hm2 htp2; simp only [hm2, htp2]
    · rw [ite_eq_right h] at hm2 htp2; simp only [hm2, htp2]
  obtain ⟨c1, k1, x1, hk1, hw1, hq1, hr1, hrr1, hrm1, ho1⟩ := step 0 c e0 e1 (by omega) hw
    (fun _ _ _ _ => rfl) h0 h1 (by omega)
  have hq1' := pushF_snd_le S.bSTK S.s e0 e1 (c.nmem, c.nreg 130701)
  rw [← hq1] at hq1'
  simp only at hq1'
  obtain ⟨c2, k2, x2, hk2, hw2, hq2, hr2, hrr2, hrm2, ho2⟩ := step 1 c1 e1 e2 (by omega) hw1 hr1
    (by rwa [hr1 _ (by omega) (by omega) (by omega)])
    (by rwa [hr1 _ (by omega) (by omega) (by omega)]) (by omega)
  have hq2' := pushF_snd_le S.bSTK S.s e1 e2 (c1.nmem, c1.nreg 130701)
  rw [← hq2] at hq2'
  simp only at hq2'
  obtain ⟨c3, k3, x3, hk3, hw3, hq3, hr3, hrr3, hrm3, ho3⟩ := step 2 c2 e2 e3 (by omega) hw2 hr2
    (by rwa [hr2 _ (by omega) (by omega) (by omega)])
    (by rwa [hr2 _ (by omega) (by omega) (by omega)]) (by omega)
  refine ⟨c3, k1 + (k2 + k3), .seq x1 (.seq x2 x3), by omega, hw3, ?_, hr3, by rw [hrr3, hrr2, hrr1],
    by rw [hrm3, hrm2, hrm1], by rw [ho3, ho2, ho1]⟩
  rw [hq3, hq2, hq1, htp]

end proofs

end

end Chazelle.Core.Cluster
