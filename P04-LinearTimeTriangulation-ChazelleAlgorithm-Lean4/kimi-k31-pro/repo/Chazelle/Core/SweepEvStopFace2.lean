module

public import Chazelle.Core.SweepEvStopFace
public import Chazelle.Core.SweepEvFace3
public import Chazelle.Core.SweepEvStopTasks
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stage 2: the regions faced at a position of the walk of `C₂` (task F, RAM 1)

`frLoc pe ph`: `faceLoc` (`SweepEvFace2`) at a general proper position `(pe, ph)` of the walk of
`C₂`: double identification (spine answer `j`), the regions of the arcs at `j - 1`, `j`, `j + 1`,
the ends of the arc at `j`.  Post `LocOutG`, run step `frLoc_irs`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

/-- The prefix at the position `(pe, ph)`. -/
def frLoc (pe ph : ℕ) : Stmt :=
  .seq (locJ (sw 31) (sw 4) pe ph lJ)
    (.seq (block [.copyN lNF (sw 4)])
      (.seq (block nbrHead) (.seq nbrJ (.seq (block nbrRegsL) (block faceRead)))))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The post of the prefix** at the position `(pe, ph)`. -/
def LocOutG (P : Polygon) (J : Merge.Junction) (N₂ : NF) (pe ph : ℕ) (c c' : Config) : Prop :=
  ∃ j, j < N₂.arcs.length ∧
    (¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P)) ((chainModel J.right).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩) →
      N₂.F (chainModel J.right) (Qof P) = ∅ ∨
        sideInArc (sk (chainModel J.right) (Qof P) N₂ j) (ek (chainModel J.right) (Qof P) N₂ j)
          ((chainModel J.right).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩)) ∧
    ((chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P)) ((chainModel J.right).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩) →
      sk (chainModel J.right) (Qof P) N₂ j = (chainModel J.right).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩ ∨
        ek (chainModel J.right) (Qof P) N₂ j = (chainModel J.right).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩) ∧
    c'.nreg lR0 = (N₂.arc (sj N₂ (predP N₂.arcs.length j))).reg ∧
    c'.nreg lR1 = (N₂.arc (sj N₂ j)).reg ∧
    c'.nreg lR2 = (N₂.arc (sj N₂ (succP N₂.arcs.length j))).reg ∧
    c'.nreg fSE = (N₂.arc (sj N₂ j)).s.edge ∧ c'.nreg fSH = (N₂.arc (sj N₂ j)).s.hgt ∧
    c'.nreg fEE = (N₂.arc (sj N₂ j)).e.edge ∧ c'.nreg fEH = (N₂.arc (sj N₂ j)).e.hgt ∧
    c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
    ∀ r, bandOf r ∉ oracleBands → (r < sw 1102 ∨ sw 1203 < r) → c'.nreg r = c.nreg r

/-- **The prefix at a general position** `(pe, ph)`. -/
theorem frLoc_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {pe ph : ℕ} (hpr : 240000 ≤ pe ∧ pe < 250000 ∧ 240000 ≤ ph ∧ ph < 250000)
    (hfe : c.nreg pe < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pe, c.nreg ph⟩)
    (hroom : c.nreg ALLOC + faceLocK (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ (frLoc pe ph) c (faceLocK (c₀.nreg TLR)) (LocOutG P J N₂ pe ph c) := by
  have hK := E.hK.fix hI
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  have hP₂  := E.hP
  have hNF := E.hNF₂
  obtain ⟨hmd, hmwf⟩ := E.md₂ hI
  have hNT := E.nt₂ hI
  have hNA  := hNT.nfAt
  obtain ⟨htab, hbig, hTB, eL⟩ := E.tab hI
  have hA0 := arcs_pos hP₂ hNF
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT hNF hA0
  obtain ⟨-, -, b3, -, -, -⟩ := Restore.nf_bounds hNT
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 _
  have hAc := hI.hA
  -- 1. locate
  unfold frLoc
  refine IRS.mono (K := (5500 * (c.nreg TLR + 1) + 9) + (1 + (6 + (7 + (21 + 14)))))
    (IRS.seq (locJ_irs (md := sw 31) (nf := sw 4) (pe := pe) (ph := ph) (o := lJ) hI E.hG E.hWh
      ⟨by ufn sw, by ufn sw, by ufn sw,
        by ufn sw, hpr.1, hpr.2.1, hpr.2.2.1, hpr.2.2.2⟩
      ⟨by ufn lJ sw, by ufn lJ sw⟩ hmd hmwf hP₂ hNA hNF
      hfe hpp htab hbig (by omega) (by omega) (by omega) (by omega)
      (by ruo [eL] faceLocK at hroom)) ?_)
    (by ruo [eL] faceLocK) (fun _ => id)
  rintro c₁ hI₁ - - ⟨hj1, hl1, hl2, k1', hA1, hm1⟩
  set j := c₁.nreg lJ with hjd
  have keep1 : ∀ r, bandOf r ∉ oracleBands → r ≠ lJ → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    by_cases hra : r = ALLOC
    · rwx [hra]
    · exact k1' r h1 h2 hra
  have e4 : c₁.nreg (sw 4) = c.nreg (sw 4) :=
    keep1 _ (not_oracle_sw (by ufn sw) (by ufn sw))
      (by ufn lJ sw)
  -- 2. copy the normal form register
  refine IRS.seq (IRS.block [.copyN lNF (sw 4)] hI₁
    ⟨iscr_sw (by ufn lNF sw) (by ufn lNF sw), trivial⟩) ?_
  rintro c₂ hI₂ - - hc2
  have hm2 : c₂.nmem = c.nmem := by rwx [hc2]
  have c2NF : c₂.nreg lNF = c.nreg (sw 4) := by
    rw [hc2]; show regB c₁.nmem [.copyN lNF (sw 4)] c₁.nreg lNF = _
    simp [regB, regI, upd, ite_true]; exact e4
  have c2r : ∀ r, r ≠ lNF → c₂.nreg r = c₁.nreg r := by
    intro r hr; rw [hc2]; show regB c₁.nmem [.copyN lNF (sw 4)] c₁.nreg r = _
    simp [regB, regI, upd, ite_eq_right hr]
  have hK₂ := E.hK.fix hI₂
  -- 3. the header
  refine IRS.seq (IRS.block nbrHead hI₂ (nbrHead_ok _ _ hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
    (by rwo [c2NF]))) ?_
  rintro c₃ hI₃ - - hc3
  obtain ⟨v3A, v3SB, v3AB⟩ := nbrHead_val c₂.nmem c₂.nreg hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
  have hm3 : c₃.nmem = c.nmem := by rwx [hc3]
  have c3A : c₃.nreg lA = N₂.arcs.length := by
    rw [hc3]; show regB c₂.nmem nbrHead c₂.nreg lA = _
    rw [v3A, c2NF, hm2]; exact hNA.2.1
  have c3SB : c₃.nreg lSB = c.nmem (c.nreg (sw 4) + 6) := by
    rw [hc3]; show regB c₂.nmem nbrHead c₂.nreg lSB = _; rw [v3SB, c2NF, hm2]
  have c3AB : c₃.nreg lAB = c.nmem (c.nreg (sw 4) + 4) := by
    rw [hc3]; show regB c₂.nmem nbrHead c₂.nreg lAB = _; rw [v3AB, c2NF, hm2]
  have c3r : ∀ r, r ≠ lX → r ≠ lA → r ≠ lSB → r ≠ lAB → c₃.nreg r = c₂.nreg r := by
    intro r h1 h2 h3 h4; rw [hc3]; exact nbrHead_other _ _ h1 h2 h3 h4
  have c3J : c₃.nreg lJ = j := by
    rw [c3r _ (by ufn lJ lX sw) (by ufn lJ lA sw)
      (by ufn lJ lSB sw) (by ufn lJ lAB sw),
      c2r _ (by ufn lJ lNF sw)]
  -- 4. the neighbouring positions
  refine IRS.seq (nbrJ_irs hI₃ (E.hK.fix hI₃) c3A c3J hj1) ?_
  rintro c₄ hI₄ - - ⟨v4P, v4N, k4', hm4'⟩
  have hjP := OracleQ.predP_lt hj1
  have hjN := OracleQ.succP_lt hj1
  have c4SB : c₄.nreg lSB = c.nmem (c.nreg (sw 4) + 6) := by
    rw [k4' _ (by ufn lSB lJP sw) (by ufn lSB lJN sw), c3SB]
  have c4AB : c₄.nreg lAB = c.nmem (c.nreg (sw 4) + 4) := by
    rw [k4' _ (by ufn lAB lJP sw) (by ufn lAB lJN sw), c3AB]
  have c4J : c₄.nreg lJ = j := by
    rw [k4' _ (by ufn lJ lJP sw) (by ufn lJ lJN sw), c3J]
  have hm4 : c₄.nmem = c.nmem := by rw [hm4', hm3]
  -- the table reads
  have hseqv : ∀ p, p < N₂.arcs.length → c.nmem (c.nmem (c.nreg (sw 4) + 6) + p) = sj N₂ p :=
    fun p hp => hNA.2.2.2.2.2.2.2.2.1 p (by rwx [NFLoc.seq_length hNF])
  have hsjl : ∀ p, p < N₂.arcs.length → sj N₂ p < N₂.arcs.length := fun p hp =>
    NFLoc.seq_lt hNF hp
  have harcv : ∀ a, a < N₂.arcs.length →
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a) = (N₂.arc a).reg ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 1) = (N₂.arc a).s.edge ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 2) = (N₂.arc a).s.hgt ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 3) = (N₂.arc a).e.edge ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 4) = (N₂.arc a).e.hgt :=
    hNA.2.2.2.2.2.2.1
  have hTBW : c.nreg TBR ≤ W := by omega
  have hb1 : ∀ v, v < N₂.arcs.length → c.nmem (c.nreg (sw 4) + 6) + v ≤ W ∧
      c.nmem (c.nreg (sw 4) + 4) + 5 * c.nmem (c.nmem (c.nreg (sw 4) + 6) + v) + 4 ≤ W := by
    intro v hv
    rw [hseqv v hv]
    have := b3 _ (hsjl v hv)
    constructor <;> omega
  have hbound : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      c₄.nreg lSB + c₄.nreg p ≤ W ∧ c₄.nreg lAB + 5 * c₄.nmem (c₄.nreg lSB + c₄.nreg p) ≤ W := by
    intro p hp
    rw [c4SB, c4AB, hm4]
    rcases hp with h | h | h <;> rw [h]
    · rw [v4P]; have := hb1 _ hjP; omega
    · rw [c4J]; have := hb1 _ hj1; omega
    · rw [v4N]; have := hb1 _ hjN; omega
  -- 5. the three regions
  refine IRS.seq (IRS.block nbrRegsL hI₄ (nbrRegsL_ok _ _ hbound)) ?_
  rintro c₅ hI₅ - - hc5
  obtain ⟨v50, v51, v52⟩ := nbrRegsL_val c₄.nmem c₄.nreg
  have c5R0 : c₅.nreg lR0 = (N₂.arc (sj N₂ (predP N₂.arcs.length j))).reg := by
    rw [hc5]; show regB c₄.nmem nbrRegsL c₄.nreg lR0 = _
    rw [v50, c4SB, c4AB, v4P, hm4, hseqv _ hjP]; exact (harcv _ (hsjl _ hjP)).1
  have c5R1 : c₅.nreg lR1 = (N₂.arc (sj N₂ j)).reg := by
    rw [hc5]; show regB c₄.nmem nbrRegsL c₄.nreg lR1 = _
    rw [v51, c4SB, c4AB, c4J, hm4, hseqv _ hj1]; exact (harcv _ (hsjl _ hj1)).1
  have c5R2 : c₅.nreg lR2 = (N₂.arc (sj N₂ (succP N₂.arcs.length j))).reg := by
    rw [hc5]; show regB c₄.nmem nbrRegsL c₄.nreg lR2 = _
    rw [v52, c4SB, c4AB, v4N, hm4, hseqv _ hjN]; exact (harcv _ (hsjl _ hjN)).1
  have c5r : ∀ r, r ≠ lX → r ≠ lY → r ≠ lR0 → r ≠ lR1 → r ≠ lR2 → c₅.nreg r = c₄.nreg r := by
    intro r h1 h2 h3 h4 h5; rw [hc5]; exact nbrRegsL_other _ _ h1 h2 h3 h4 h5
  have hm5 : c₅.nmem = c.nmem := by rwx [hc5]
  have c5SB : c₅.nreg lSB = c.nmem (c.nreg (sw 4) + 6) := by
    rw [c5r _ (by ufn lSB lX sw) (by ufn lSB lY sw)
      (by ufn lSB lR0 sw) (by ufn lSB lR1 sw)
      (by ufn lSB lR2 sw), c4SB]
  have c5AB : c₅.nreg lAB = c.nmem (c.nreg (sw 4) + 4) := by
    rw [c5r _ (by ufn lAB lX sw) (by ufn lAB lY sw)
      (by ufn lAB lR0 sw) (by ufn lAB lR1 sw)
      (by ufn lAB lR2 sw), c4AB]
  have c5J : c₅.nreg lJ = j := by
    rw [c5r _ (by ufn lJ lX sw) (by ufn lJ lY sw)
      (by ufn lJ lR0 sw) (by ufn lJ lR1 sw)
      (by ufn lJ lR2 sw), c4J]
  have hK₅ := E.hK.fix hI₅
  -- 6. the arc at `j`
  have hb6 := hb1 _ hj1
  refine (IRS.block faceRead hI₅ (faceRead_ok _ _ hK₅.2.1 (by rwo [c5SB, c5J])
    (by rwo [c5SB, c5J, c5AB, hm5]))).mono le_rfl ?_
  rintro c₆ hc6
  obtain ⟨v6SE, v6SH, v6EE, v6EH⟩ := faceRead_val c₅.nmem c₅.nreg hK₅.2.1
  have hsj := hseqv _ hj1
  have ha := harcv _ (hsjl _ hj1)
  have c6r : ∀ r, (r < sw 1102 ∨ sw 1203 < r) → c₆.nreg r = c₅.nreg r := by
    intro r hr; rw [hc6]; exact regB_out _ _ _ faceRead_dst hr
  have c6o : ∀ q, q ≠ lX → q ≠ lY → q ≠ fSE → q ≠ fSH → q ≠ fEE → q ≠ fEH →
      c₆.nreg q = c₅.nreg q := by
    intro q h1 h2 h3 h4 h5 h6; rw [hc6]; exact faceRead_other _ _ h1 h2 h3 h4 h5 h6
  have hothers : ∀ r, bandOf r ∉ oracleBands → (r < sw 1102 ∨ sw 1203 < r) →
      c₆.nreg r = c.nreg r := by
    intro r hr hrr
    have n1 := fun q (h1 : sw 1102 ≤ q) (h2 : q ≤ sw 1203) => out_ne hrr h1 h2
    rw [c6r r hrr,
      c5r r (n1 _ (by ufn lX sw) (by ufn lX sw))
        (n1 _ (by ufn lY sw) (by ufn lY sw))
        (n1 _ (by ufn lR0 sw) (by ufn lR0 sw))
        (n1 _ (by ufn lR1 sw) (by ufn lR1 sw))
        (n1 _ (by ufn lR2 sw) (by ufn lR2 sw)),
      k4' r (n1 _ (by ufn lJP sw) (by ufn lJP sw))
        (n1 _ (by ufn lJN sw) (by ufn lJN sw)),
      c3r r (n1 _ (by ufn lX sw) (by ufn lX sw))
        (n1 _ (by ufn lA sw) (by ufn lA sw))
        (n1 _ (by ufn lSB sw) (by ufn lSB sw))
        (n1 _ (by ufn lAB sw) (by ufn lAB sw)),
      c2r r (n1 _ (by ufn lNF sw) (by ufn lNF sw))]
    exact keep1 r hr (n1 _ (by ufn lJ sw) (by ufn lJ sw))
  have hR : ∀ q, (q = lR0 ∨ q = lR1 ∨ q = lR2) → c₆.nreg q = c₅.nreg q := by
    rintro q (rfl | rfl | rfl) <;> apply c6o <;>
      simp [lR0, lR1, lR2, lX, lY, fSE, fSH, fEE, fEH, sw]
  refine ⟨j, hj1, hl1, hl2, by rw [hR _ (Or.inl rfl), c5R0],
    by rw [hR _ (Or.inr (Or.inl rfl)), c5R1], by rw [hR _ (Or.inr (Or.inr rfl)), c5R2],
    ?_, ?_, ?_, ?_, by rwx [hc6],
    hothers _ (by decide) (Or.inl (by ufn ALLOC sw)), hothers⟩
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fSE = _
    rw [v6SE, c5AB, c5SB, c5J, hm5, hsj]; exact ha.2.1
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fSH = _
    rw [v6SH, c5AB, c5SB, c5J, hm5, hsj]; exact ha.2.2.1
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fEE = _
    rw [v6EE, c5AB, c5SB, c5J, hm5, hsj]; exact ha.2.2.2.1
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fEH = _
    rw [v6EH, c5AB, c5SB, c5J, hm5, hsj]; exact ha.2.2.2.2

end

end SweepEv

end Chazelle.Core
