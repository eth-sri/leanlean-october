module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopFace
public import Chazelle.Core.SweepEvFace3
public import Chazelle.Core.SweepEvStopTasks

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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The prefix at a general position** `(pe, ph)`. -/
theorem frLoc_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {pe ph : ℕ} (hpr : 240000 ≤ pe ∧ pe < 250000 ∧ 240000 ≤ ph ∧ ph < 250000)
    (hfe : c.nreg pe < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pe, c.nreg ph⟩)
    (hroom : c.nreg ALLOC + faceLocK (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ (frLoc pe ph) c (faceLocK (c₀.nreg TLR)) (LocOutG P J N₂ pe ph c) := by
  have hK := E.hK.fix hI
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  have hP₂ : J.right.P.Simple := E.hP
  have hNF := E.hNF₂
  obtain ⟨hmd, hmwf⟩ := E.md₂ hI
  have hNT := E.nt₂ hI
  have hNA : NFAt c.nmem (c.nreg (sw 4)) N₂ := hNT.nfAt
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
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, hpr.1, hpr.2.1, hpr.2.2.1, hpr.2.2.2⟩
      ⟨by omega_nf, by omega_nf⟩ hmd hmwf hP₂ hNA hNF
      hfe hpp htab hbig (by omega) (by omega) (by omega) (by omega)
      (by grind [faceLocK])) ?_)
    (by ram_grind) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨hj1, hl1, hl2, k1', hA1, hm1⟩
  set j := c₁.nreg lJ with hjd
  have keep1 : ∀ r, bandOf r ∉ oracleBands → r ≠ lJ → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    grind
  have e4 : c₁.nreg (sw 4) = c.nreg (sw 4) :=
    keep1 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (by omega_nf)
  -- 2. copy the normal form register
  refine IRS.seq (IRS.block [.copyN lNF (sw 4)] hI₁
    ⟨iscr_sw (by omega_nf) (by omega_nf), trivial⟩) ?_
  rintro c₂ hI₂ - - hc2
  have hm2 : c₂.nmem = c.nmem := by grind
  have c2NF : c₂.nreg lNF = c.nreg (sw 4) := by
    rw [hc2]; show regB c₁.nmem [.copyN lNF (sw 4)] c₁.nreg lNF = _
    simp only [regB, regI, upd, ite_true]; exact e4
  have c2r : ∀ r, r ≠ lNF → c₂.nreg r = c₁.nreg r := by
    intro r hr; rw [hc2]; show regB c₁.nmem [.copyN lNF (sw 4)] c₁.nreg r = _
    simp only [regB, regI, upd, ite_eq_right hr]
  have hK₂ := E.hK.fix hI₂
  -- 3. the header
  refine IRS.seq (IRS.block nbrHead hI₂ (nbrHead_ok _ _ hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
    (by omega))) ?_
  rintro c₃ hI₃ - - hc3
  obtain ⟨v3A, v3SB, v3AB⟩ := nbrHead_val c₂.nmem c₂.nreg hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
  have hm3 : c₃.nmem = c.nmem := by grind
  have c3A : c₃.nreg lA = N₂.arcs.length := by
    rw [hc3]; show regB c₂.nmem nbrHead c₂.nreg lA = _
    rw [v3A, c2NF, hm2]; exact hNA.2.1
  have c3SB : c₃.nreg lSB = c.nmem (c.nreg (sw 4) + 6) := by
    rw [hc3]; grind
  have c3AB : c₃.nreg lAB = c.nmem (c.nreg (sw 4) + 4) := by
    rw [hc3]; grind
  have c3r : ∀ r, r ≠ lX → r ≠ lA → r ≠ lSB → r ≠ lAB → c₃.nreg r = c₂.nreg r := by
    intro r h1 h2 h3 h4; rw [hc3]; exact nbrHead_other _ _ h1 h2 h3 h4
  have c3J : c₃.nreg lJ = j := by
    rw [c3r _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf),
      c2r _ (by omega_nf)]
  -- 4. the neighbouring positions
  refine IRS.seq (nbrJ_irs hI₃ (E.hK.fix hI₃) c3A c3J hj1) ?_
  rintro c₄ hI₄ - - ⟨v4P, v4N, k4', hm4'⟩
  have hjP := OracleQ.predP_lt hj1
  have hjN := OracleQ.succP_lt hj1
  have c4SB : c₄.nreg lSB = c.nmem (c.nreg (sw 4) + 6) := by
    rw [k4' _ (by omega_nf) (by omega_nf), c3SB]
  have c4AB : c₄.nreg lAB = c.nmem (c.nreg (sw 4) + 4) := by
    rw [k4' _ (by omega_nf) (by omega_nf), c3AB]
  have c4J : c₄.nreg lJ = j := by
    rw [k4' _ (by omega_nf) (by omega_nf), c3J]
  have hm4 : c₄.nmem = c.nmem := by grind
  -- the table reads
  have hseqv : ∀ p, p < N₂.arcs.length → c.nmem (c.nmem (c.nreg (sw 4) + 6) + p) = sj N₂ p :=
    fun p hp => hNA.2.2.2.2.2.2.2.2.1 p (by rw [NFLoc.seq_length hNF]; exact hp)
  have hsjl : ∀ p, p < N₂.arcs.length → sj N₂ p < N₂.arcs.length := fun p hp =>
    NFLoc.seq_lt hNF hp
  have harcv : ∀ a, a < N₂.arcs.length →
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a) = (N₂.arc a).reg ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 1) = (N₂.arc a).s.edge ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 2) = (N₂.arc a).s.hgt ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 3) = (N₂.arc a).e.edge ∧
      c.nmem (c.nmem (c.nreg (sw 4) + 4) + 5 * a + 4) = (N₂.arc a).e.hgt :=
    fun a ha => hNA.2.2.2.2.2.2.1 a ha
  
  have hb1 : ∀ v, v < N₂.arcs.length → c.nmem (c.nreg (sw 4) + 6) + v ≤ W ∧
      c.nmem (c.nreg (sw 4) + 4) + 5 * c.nmem (c.nmem (c.nreg (sw 4) + 6) + v) + 4 ≤ W := by
    intro v hv
    rw [hseqv v hv]
    have := b3 _ (hsjl v hv)
    omega
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
  have hm5 : c₅.nmem = c.nmem := by grind
  have c5SB : c₅.nreg lSB = c.nmem (c.nreg (sw 4) + 6) := by
    rw [c5r _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf)
      (by omega_nf), c4SB]
  have c5AB : c₅.nreg lAB = c.nmem (c.nreg (sw 4) + 4) := by
    rw [c5r _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf)
      (by omega_nf), c4AB]
  have c5J : c₅.nreg lJ = j := by
    rw [c5r _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf)
      (by omega_nf), c4J]
  have hK₅ := E.hK.fix hI₅
  -- 6. the arc at `j`
  have hb6 := hb1 _ hj1
  refine (IRS.block faceRead hI₅ (faceRead_ok _ _ hK₅.2.1 (by omega)
    (by rw [c5SB, c5J, c5AB, hm5]; omega))).mono le_rfl ?_
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
      c5r r (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf)),
      k4' r (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf)),
      c3r r (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf))
        (n1 _ (by omega_nf) (by omega_nf)),
      c2r r (n1 _ (by omega_nf) (by omega_nf))]
    exact keep1 r hr (n1 _ (by omega_nf) (by omega_nf))
  have hR : ∀ q, (q = lR0 ∨ q = lR1 ∨ q = lR2) → c₆.nreg q = c₅.nreg q := by
    rintro q (rfl | rfl | rfl) <;> apply c6o <;>
      omega_nf
  refine ⟨j, hj1, hl1, hl2, by rw [hR _ (Or.inl rfl), c5R0],
    by rw [hR _ (Or.inr (Or.inl rfl)), c5R1], by rw [hR _ (Or.inr (Or.inr rfl)), c5R2],
    ?_, ?_, ?_, ?_, by ram_simp,
    hothers _ (by decide) (Or.inl (by omega_nf)), hothers⟩
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fSE = _
    rw [v6SE, c5AB, c5SB, c5J, hm5, hsj]; exact ha.2.1
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fSH = _
    rw [v6SH, c5AB, c5SB, c5J, hm5, hsj]; omega
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fEE = _
    rw [v6EE, c5AB, c5SB, c5J, hm5, hsj]; omega
  · rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fEH = _
    rw [v6EH, c5AB, c5SB, c5J, hm5, hsj]; omega

end

end SweepEv

end Chazelle.Core
