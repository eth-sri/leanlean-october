module

public import Chazelle.Core.SweepIoMin
public import Chazelle.Core.SweepIoLocal
public import Chazelle.Core.SweepIoShot
public import Chazelle.Core.SweepIoHoles

/-!
# The sweep RAM (WP-D), answers: the local hit, part 1 (locate and the three regions)

The local hit in the model `M = chainModel C` (normal form `N`) at the walk position `x = (e, h)`
(registers `lE`, `lH`) for the direction code `lD`:

1. double identification (`locJ`): the spine position `j` (register `lJ`);
2. the regions of the arcs at the spine positions `j - 1`, `j`, `j + 1` (`nbrRegs N j`), in the
   registers `lR0, lR1, lR2` and stored as a list of three words at the allocator (`lL`);
3. (part 2) the gather of their arcs, the holes at `x`, the shot, the chord ends.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers -/

def lMD : ℕ := sw 1100
def lCD : ℕ := sw 1101
def lNF : ℕ := sw 1102
def lE : ℕ := sw 1103
def lH : ℕ := sw 1104
def lD : ℕ := sw 1105
def lN : ℕ := sw 1106
def lT : ℕ := sw 1107
def lJ : ℕ := sw 1108
def lR0 : ℕ := sw 1109
def lR1 : ℕ := sw 1110
def lR2 : ℕ := sw 1111
def lX : ℕ := sw 1112
def lY : ℕ := sw 1113
def lA : ℕ := sw 1114
def lSB : ℕ := sw 1115
def lAB : ℕ := sw 1116
def lJP : ℕ := sw 1117
def lJN : ℕ := sw 1118
def lL : ℕ := sw 1119

/-- The accumulator of the answers. -/
def accA : ℕ := sw 2000

/-! ## The three regions -/

/-- Header reads: the number of arcs, the sequence table, the arc records. -/
def nbrHead : List Instr :=
  [.addN lX lNF K1, .loadN lA lX, .addN lX lNF K6, .loadN lSB lX, .addN lX lNF K4,
    .loadN lAB lX]

/-- The neighbouring spine positions. -/
def nbrJ : Stmt :=
  .seq (.ifLtN lJ K1 (.instr (.subN lJP lA K1)) (.instr (.subN lJP lJ K1)))
    (.seq (.instr (.addN lJN lJ K1)) (.ifLtN lJN lA .skip (.instr (.constN lJN 0))))

/-- The region of the arc at the spine position in `p`, into `dst`. -/
def regOfL (p dst : ℕ) : List Instr :=
  [.addN lX lSB p, .loadN lX lX, .addN lY lX lX, .addN lY lY lY, .addN lY lY lX,
    .addN lY lAB lY, .loadN dst lY]

/-- The three regions. -/
def nbrRegsL : List Instr := regOfL lJP lR0 ++ regOfL lJ lR1 ++ regOfL lJN lR2

/-- Store the three regions at the allocator (list address in `lL`). -/
def put3 : Stmt :=
  block [.copyN lL ALLOC, .storeN ALLOC lR0, .addN ALLOC ALLOC K1, .storeN ALLOC lR1,
    .addN ALLOC ALLOC K1, .storeN ALLOC lR2, .addN ALLOC ALLOC K1]

theorem nbrRegsL_val (m f : ℕ → ℕ) :
    regB m nbrRegsL f lR0 = m (f lAB + 5 * m (f lSB + f lJP)) ∧
    regB m nbrRegsL f lR1 = m (f lAB + 5 * m (f lSB + f lJ)) ∧
    regB m nbrRegsL f lR2 = m (f lAB + 5 * m (f lSB + f lJN)) := by
  simp only [nbrRegsL, regOfL, List.cons_append, List.nil_append, regB, regI, upd, lX, lY, lSB,
    lAB, lJP, lJ, lJN, lR0, lR1, lR2, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  exact ⟨congrArg m (by ring), congrArg m (by ring), congrArg m (by ring)⟩

theorem nbrRegsL_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ lX) (h2 : q ≠ lY) (h3 : q ≠ lR0)
    (h4 : q ≠ lR1) (h5 : q ≠ lR2) : regB m nbrRegsL f q = f q :=
  regB_other m nbrRegsL f (fun i hi => by
    simp only [nbrRegsL, regOfL, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> intro h <;> subst h <;>
      simp_all)

theorem nbrHead_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk4 : f K4 = 4) (hk6 : f K6 = 6) :
    regB m nbrHead f lA = m (f lNF + 1) ∧ regB m nbrHead f lSB = m (f lNF + 6) ∧
    regB m nbrHead f lAB = m (f lNF + 4) := by
  have e1 : f 240611 = 1 := hk1
  have e4 : f 240613 = 4 := hk4
  have e6 : f 240612 = 6 := hk6
  simp only [nbrHead, regB, regI, upd, lX, lA, lSB, lAB, lNF, K1, K4, K6, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e4, e6]
  exact ⟨trivial, trivial, trivial⟩

theorem nbrHead_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ lX) (h2 : q ≠ lA) (h3 : q ≠ lSB)
    (h4 : q ≠ lAB) : regB m nbrHead f q = f q :=
  regB_other m nbrHead f (fun i hi => by
    simp only [nbrHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> intro h <;>
      subst h <;> simp_all)

theorem nbrHead_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk4 : f K4 = 4) (hk6 : f K6 = 6)
    (hb : f lNF + 6 ≤ W) : okB W m nbrHead f := by
  have e1 : f 240611 = 1 := hk1
  have e4 : f 240613 = 4 := hk4
  have e6 : f 240612 = 6 := hk6
  have hb' : f 241102 + 6 ≤ W := hb
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [nbrHead, okB, okI, regI, upd, lX, lA, lSB, lAB, lNF, K1, K4, K6, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e4, e6]
  exact ⟨⟨s 1112 (by norm_num) (by norm_num), by omega⟩, s 1114 (by norm_num) (by norm_num),
    ⟨s 1112 (by norm_num) (by norm_num), by omega⟩, s 1115 (by norm_num) (by norm_num),
    ⟨s 1112 (by norm_num) (by norm_num), by omega⟩, s 1116 (by norm_num) (by norm_num), trivial⟩

theorem nbrRegsL_ok (m f : ℕ → ℕ) (hb : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      f lSB + f p ≤ W ∧ f lAB + 5 * m (f lSB + f p) ≤ W) : okB W m nbrRegsL f := by
  obtain ⟨a1, a2⟩ := hb lJP (Or.inl rfl)
  obtain ⟨b1, b2⟩ := hb lJ (Or.inr (Or.inl rfl))
  obtain ⟨d1, d2⟩ := hb lJN (Or.inr (Or.inr rfl))
  have a1' : f 241115 + f 241117 ≤ W := a1
  have a2' : f 241116 + 5 * m (f 241115 + f 241117) ≤ W := a2
  have b1' : f 241115 + f 241108 ≤ W := b1
  have b2' : f 241116 + 5 * m (f 241115 + f 241108) ≤ W := b2
  have d1' : f 241115 + f 241118 ≤ W := d1
  have d2' : f 241116 + 5 * m (f 241115 + f 241118) ≤ W := d2
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [nbrRegsL, regOfL, List.cons_append, List.nil_append, okB, okI, regI, upd, lX, lY,
    lSB, lAB, lJP, lJ, lJN, lR0, lR1, lR2, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  refine ⟨⟨s 1112 (by norm_num) (by norm_num), a1'⟩, s 1112 (by norm_num) (by norm_num),
    ⟨s 1113 (by norm_num) (by norm_num), by omega⟩, ⟨s 1113 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 1113 (by norm_num) (by norm_num), by omega⟩, ⟨s 1113 (by norm_num) (by norm_num), by omega⟩,
    s 1109 (by norm_num) (by norm_num),
    ⟨s 1112 (by norm_num) (by norm_num), b1'⟩, s 1112 (by norm_num) (by norm_num),
    ⟨s 1113 (by norm_num) (by norm_num), by omega⟩, ⟨s 1113 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 1113 (by norm_num) (by norm_num), by omega⟩, ⟨s 1113 (by norm_num) (by norm_num), by omega⟩,
    s 1110 (by norm_num) (by norm_num),
    ⟨s 1112 (by norm_num) (by norm_num), d1'⟩, s 1112 (by norm_num) (by norm_num),
    ⟨s 1113 (by norm_num) (by norm_num), by omega⟩, ⟨s 1113 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 1113 (by norm_num) (by norm_num), by omega⟩, ⟨s 1113 (by norm_num) (by norm_num), by omega⟩,
    s 1111 (by norm_num) (by norm_num), trivial⟩

/-- The memory after `put3`. -/
def mem3 (m : ℕ → ℕ) (A v0 v1 v2 : ℕ) : ℕ → ℕ := upd (upd (upd m A v0) (A + 1) v1) (A + 2) v2

theorem put3_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 3 ≤ W) :
    IRS P W c₀ put3 c 7 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 3 ∧ c'.nreg lL = c.nreg ALLOC ∧
      (∀ r, r ≠ ALLOC → r ≠ lL → c'.nreg r = c.nreg r) ∧
      c'.nmem = mem3 c.nmem (c.nreg ALLOC) (c.nreg lR0) (c.nreg lR1) (c.nreg lR2)) := by
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have hw := hI.hw
  have hroom' : c.nreg 9999 + 3 ≤ W := hroom
  have ex : ∃ c' k, Exec P W (block [.copyN 241119 9999, .storeN 9999 241109,
      .addN 9999 9999 240611, .storeN 9999 241110, .addN 9999 9999 240611, .storeN 9999 241111,
      .addN 9999 9999 240611]) c c' k ∧ k = 7 ∧
      c'.nreg 9999 = c.nreg 9999 + 3 ∧ c'.nreg 241119 = c.nreg 9999 ∧
      (∀ r, r ≠ 9999 → r ≠ 241119 → c'.nreg r = c.nreg r) ∧
      c'.nmem = mem3 c.nmem (c.nreg 9999) (c.nreg 241109) (c.nreg 241110) (c.nreg 241111) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp
    · config_simp
      simp only [upd, ite_eq_right h1, ite_eq_right h2]
    · config_simp
      simp only [k1, mem3]
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6, h7⟩ := ex
  refine IRS.ofExec hI ex (by omega) (fun r hr hra => h3 r hra (fun h => hr (by
    subst h; exact iscr_sw (by norm_num) (by norm_num)))) h5 (fun a ha => ?_) h6 h7
    (by show c.nreg 9999 ≤ c'.nreg 9999; omega) (by show c'.nreg 9999 ≤ c.nreg 9999 + k; omega)
    ⟨h1, h2, fun r a b => h3 r a b, h4⟩
  rw [h4]
  have h0 : c₀.nreg 9999 ≤ c.nreg 9999 := hI.hA
  have ha' : a < c₀.nreg 9999 := ha
  unfold mem3
  simp only [upd]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The neighbouring spine positions. -/
theorem nbrJ_irs (hI : IInv W c₀ c) (hK : Consts c) {A j : ℕ} (hA : c.nreg lA = A)
    (hj : c.nreg lJ = j) (hjA : j < A) :
    IRS P W c₀ nbrJ c 7 (fun c' => c'.nreg lJP = predP A j ∧ c'.nreg lJN = succP A j ∧
      (∀ r, r ≠ lJP → r ≠ lJN → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have k1 : c.nreg K1 = 1 := hK.2.1
  have hAW : A ≤ W := by rw [← hA]; exact hI.hw.1 _
  unfold nbrJ
  -- the previous position
  have step1 : IRS P W c₀ (.ifLtN lJ K1 (.instr (.subN lJP lA K1)) (.instr (.subN lJP lJ K1))) c 3
      (fun c' => c' = { c with nreg := upd c.nreg lJP (predP A j) }) := by
    by_cases h0 : c.nreg lJ < c.nreg K1
    · refine (IRS.ifT h0 (IRS.reg hI (iscr_sw (by unfold lJP sw; norm_num) (by unfold lJP sw; norm_num))
        (Exec.subN hI.hw lJP lA K1))).mono (by omega) ?_
      rintro c' rfl
      rw [hA, k1, show predP A j = A - 1 by unfold predP; rw [ite_eq_left (by omega)]]
    · refine (IRS.ifF h0 (IRS.reg hI (iscr_sw (by unfold lJP sw; norm_num) (by unfold lJP sw; norm_num))
        (Exec.subN hI.hw lJP lJ K1))).mono le_rfl ?_
      rintro c' rfl
      rw [hj, k1, show predP A j = j - 1 by unfold predP; rw [ite_eq_right (by omega)]]
  refine IRS.seq step1 ?_ |>.mono (K := 3 + (1 + 3)) (by omega) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have c1J : c₁.nreg lJ = j := by
    rw [hc1]; show upd c.nreg lJP (predP A j) lJ = j
    rw [upd_other _ _ _ (by unfold lJ lJP sw; norm_num), hj]
  have c1K : c₁.nreg K1 = 1 := by
    rw [hc1]; show upd c.nreg lJP (predP A j) K1 = 1
    rw [upd_other _ _ _ (by unfold K1 lJP sw; norm_num), k1]
  have c1A : c₁.nreg lA = A := by
    rw [hc1]; show upd c.nreg lJP (predP A j) lA = A
    rw [upd_other _ _ _ (by unfold lA lJP sw; norm_num), hA]
  have c1P : c₁.nreg lJP = predP A j := by
    rw [hc1]; show upd c.nreg lJP (predP A j) lJP = _
    rw [upd_same]
  have c1r : ∀ r, r ≠ lJP → c₁.nreg r = c.nreg r := by
    intro r hr; rw [hc1]; show upd c.nreg lJP (predP A j) r = _
    rw [upd_other _ _ _ hr]
  have hjW : c₁.nreg lJ + c₁.nreg K1 ≤ W := by rw [c1J, c1K]; omega
  refine IRS.seq (IRS.reg hI₁ (iscr_sw (by unfold lJN sw; norm_num) (by unfold lJN sw; norm_num))
    (Exec.addN hI₁.hw lJN lJ K1 hjW)) ?_
  rintro c₂ hI₂ - - hc2
  have v2N : c₂.nreg lJN = j + 1 := by
    rw [hc2]; show upd c₁.nreg lJN (c₁.nreg lJ + c₁.nreg K1) lJN = _
    rw [upd_same, c1J, c1K]
  have v2A : c₂.nreg lA = A := by
    rw [hc2]; show upd c₁.nreg lJN (c₁.nreg lJ + c₁.nreg K1) lA = _
    rw [upd_other _ _ _ (by unfold lA lJN sw; norm_num), c1A]
  have v2P : c₂.nreg lJP = predP A j := by
    rw [hc2]; show upd c₁.nreg lJN (c₁.nreg lJ + c₁.nreg K1) lJP = _
    rw [upd_other _ _ _ (by unfold lJP lJN sw; norm_num), c1P]
  have v2r : ∀ r, r ≠ lJP → r ≠ lJN → c₂.nreg r = c.nreg r := by
    intro r h1 h2
    rw [hc2]; show upd c₁.nreg lJN (c₁.nreg lJ + c₁.nreg K1) r = _
    rw [upd_other _ _ _ h2, c1r r h1]
  by_cases hn : j + 1 < A
  · have hc : c₂.nreg lJN < c₂.nreg lA := by rwa [v2N, v2A]
    refine (IRS.ifT hc (IRS.skip (K := 1) hI₂ ?_)).mono (by omega) (fun _ h => h)
    refine ⟨v2P, by rw [v2N]; unfold succP; rw [ite_eq_left hn], v2r, by rw [hc2, hc1]⟩
  · have hc : ¬ c₂.nreg lJN < c₂.nreg lA := by rwa [v2N, v2A]
    refine (IRS.ifF hc (IRS.reg hI₂ (iscr_sw (by unfold lJN sw; norm_num) (by unfold lJN sw; norm_num))
        (Exec.constN hI₂.hw lJN 0 (Nat.zero_le _)))).mono le_rfl ?_
    rintro c' rfl
    have w1 : upd c₂.nreg lJN 0 lJP = predP A j := by
      rwa [upd_other _ _ _ (by unfold lJP lJN sw; norm_num)]
    have w2 : upd c₂.nreg lJN 0 lJN = succP A j := by
      rw [upd_same]; unfold succP; rw [ite_eq_right hn]
    have w3 : ∀ r, r ≠ lJP → r ≠ lJN → upd c₂.nreg lJN 0 r = c.nreg r := by
      intro r h1 h2; rw [upd_other _ _ _ h2]; exact v2r r h1 h2
    exact ⟨w1, w2, w3, by show c₂.nmem = c.nmem; rw [hc2, hc1]⟩

/-! ## The context -/

/-- A valid normal form of a chain model has an arc. -/
theorem arcs_pos {C : Chain} (hP : C.P.Simple) {N : NF} (hNF : IsNF (chainModel C) (Qof P) N) :
    0 < N.arcs.length := by
  obtain ⟨hcov1, -⟩ := arcCover (chainModel C) (Qof P) (N.F (chainModel C) (Qof P))
    (Or.inl ⟨C, hP, rfl⟩) hNF.1
  obtain ⟨U, hU, a, b, hab⟩ := hcov1
  obtain ⟨j, hj, -⟩ := NFLoc.listed_of_isArc hNF hU hab
  omega

/-- **The context of a local hit** in the chain model of `C` with the normal form `N` (bound
`E`), at a run configuration `c`: the descriptors in `lMD`, `lCD`, the normal form in `lNF`, the
table of powers above the normal form. -/
structure LCtx (P : Polygon) (W : ℕ) (C : Chain) (N : NF) (E : ℕ) (c : Config) : Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hctx : ChainCtx P W c lCD C
  hcd : c.nreg lCD = c.nreg lMD + 1
  hmd : ModelDescAt c.nmem (c.nreg lMD) (Qof P) (chainModel C)
  hmwf : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg lMD)
  hm0 : c.nmem (c.nreg lMD) = 0
  hP : C.P.Simple
  hNW : NFWithin c.nmem (c.nreg lNF) E N
  hE : E ≤ c.nreg ALLOC
  hNF : IsNF (chainModel C) (Qof P) N
  htab : ∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j
  hbig : N.arcs.length < 2 ^ c.nreg TLR
  hTB : E ≤ c.nreg TBR
  hTW : c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC

/-- The registers of part 1 (`lJ … lL`). -/
def LSet (r : ℕ) : Prop := sw 1108 ≤ r ∧ r ≤ sw 1119

/-- **Part 1** of the local hit. -/
def lh1 : Stmt :=
  .seq (locJ lMD lNF lE lH lJ) (.seq (block nbrHead) (.seq nbrJ (.seq (block nbrRegsL) put3)))

/-- The cost of part 1. -/
def lh1K (L : ℕ) : ℕ := 5500 * (L + 1) + 9 + 60

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Part 1 of the local hit**: the spine position of `x` and the list of its three regions. -/
theorem lh1_irs {C : Chain} {N : NF} {E : ℕ} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hL : LCtx P W C N E c) (he : c.nreg lE < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg lE, c.nreg lH⟩)
    (hroom : c.nreg ALLOC + lh1K (c.nreg TLR) ≤ W) :
    IRS P W c₀ lh1 c (lh1K (c.nreg TLR)) (fun c' =>
      c'.nreg lJ < N.arcs.length ∧
      (¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P))
          ((chainModel C).key (Qof P) ⟨c.nreg lE, c.nreg lH⟩) →
        N.F (chainModel C) (Qof P) = ∅ ∨
          sideInArc (sk (chainModel C) (Qof P) N (c'.nreg lJ))
            (ek (chainModel C) (Qof P) N (c'.nreg lJ))
            ((chainModel C).key (Qof P) ⟨c.nreg lE, c.nreg lH⟩)) ∧
      ((chainModel C).IsCut (N.F (chainModel C) (Qof P))
          ((chainModel C).key (Qof P) ⟨c.nreg lE, c.nreg lH⟩) →
        sk (chainModel C) (Qof P) N (c'.nreg lJ) =
            (chainModel C).key (Qof P) ⟨c.nreg lE, c.nreg lH⟩ ∨
          ek (chainModel C) (Qof P) N (c'.nreg lJ) =
            (chainModel C).key (Qof P) ⟨c.nreg lE, c.nreg lH⟩) ∧
      c'.nreg lL = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 3 ∧
      (∀ i, i < 3 → c'.nmem (c.nreg ALLOC + i) = (Sweep.nbrRegs N (c'.nreg lJ)).getD i 0) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg lR0 = (N.arc (sj N (predP N.arcs.length (c'.nreg lJ)))).reg ∧
      c'.nreg lR1 = (N.arc (sj N (c'.nreg lJ))).reg ∧
      c'.nreg lR2 = (N.arc (sj N (succP N.arcs.length (c'.nreg lJ)))).reg) := by
  have hNA : NFAt c.nmem (c.nreg lNF) N := hL.hNW.holds
  have hA0 := arcs_pos hL.hP hL.hNF
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hL.hNW hL.hNF hA0
  obtain ⟨-, -, b3, -, -, -⟩ := Restore.nf_bounds hL.hNW
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 _
  have hTB := hL.hTB
  have hTW := hL.hTW
  have hE := hL.hE
  -- 1. locate
  refine IRS.mono (K := (5500 * (c.nreg TLR + 1) + 9) + (6 + (7 + (21 + 7))))
    (IRS.seq (locJ_irs (md := lMD) (nf := lNF) (pe := lE) (ph := lH) (o := lJ) hI hL.hG hL.hWh
      ⟨by unfold lMD sw; norm_num, by unfold lMD sw; norm_num, by unfold lNF sw; norm_num,
        by unfold lNF sw; norm_num, by unfold lE sw; norm_num, by unfold lE sw; norm_num,
        by unfold lH sw; norm_num, by unfold lH sw; norm_num⟩
      ⟨by unfold lJ sw; norm_num, by unfold lJ sw; norm_num⟩ hL.hmd hL.hmwf hL.hP hNA hL.hNF
      he hpp hL.htab hL.hbig (by omega) (by omega) (by omega) (by omega)
      (by unfold lh1K at hroom; omega)) ?_) (by unfold lh1K; omega) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨hj1, hl1, hl2, k1, hA1, hm1⟩
  set j := c₁.nreg lJ
  have keep1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ lJ → c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1 r (not_oracle_sw h1 h2) h3 (by unfold ALLOC; omega)
  have hNF1 : c₁.nreg lNF = c.nreg lNF := keep1 _ (by unfold lNF sw; norm_num) (by unfold lNF sw; norm_num)
    (by unfold lNF lJ sw; norm_num)
  -- 2. the header
  have hK₁ := hK.fix hI₁
  have hok2 : okB W c₁.nmem nbrHead c₁.nreg := nbrHead_ok _ _ hK₁.2.1 hK₁.2.2.2.1 hK₁.2.2.1
    (by rw [hNF1]; omega)
  refine IRS.seq (IRS.block nbrHead hI₁ hok2) ?_
  rintro c₂ hI₂ - - hc2
  obtain ⟨v2A, v2SB, v2AB⟩ := nbrHead_val c₁.nmem c₁.nreg hK₁.2.1 hK₁.2.2.2.1 hK₁.2.2.1
  have hm2 : c₂.nmem = c.nmem := by rwa [hc2]
  have c2A : c₂.nreg lA = N.arcs.length := by
    rw [hc2]; show regB c₁.nmem nbrHead c₁.nreg lA = _
    rw [v2A, hNF1, hm1]; exact hNA.2.1
  have c2SB : c₂.nreg lSB = c.nmem (c.nreg lNF + 6) := by
    rw [hc2]; show regB c₁.nmem nbrHead c₁.nreg lSB = _; rw [v2SB, hNF1, hm1]
  have c2AB : c₂.nreg lAB = c.nmem (c.nreg lNF + 4) := by
    rw [hc2]; show regB c₁.nmem nbrHead c₁.nreg lAB = _; rw [v2AB, hNF1, hm1]
  have c2r : ∀ r, r ≠ lX → r ≠ lA → r ≠ lSB → r ≠ lAB → c₂.nreg r = c₁.nreg r := by
    intro r h1 h2 h3 h4; rw [hc2]; exact nbrHead_other _ _ h1 h2 h3 h4
  have c2J : c₂.nreg lJ = j := c2r _ (by unfold lJ lX sw; norm_num) (by unfold lJ lA sw; norm_num)
    (by unfold lJ lSB sw; norm_num) (by unfold lJ lAB sw; norm_num)
  -- 3. the neighbouring positions
  refine IRS.seq (nbrJ_irs hI₂ (hK.fix hI₂) c2A c2J hj1) ?_
  rintro c₃ hI₃ - - ⟨v3P, v3N, k3, hm3'⟩
  have hjP := OracleQ.predP_lt hj1
  have hjN := OracleQ.succP_lt hj1
  have c3SB : c₃.nreg lSB = c.nmem (c.nreg lNF + 6) := by
    rw [k3 _ (by unfold lSB lJP sw; norm_num) (by unfold lSB lJN sw; norm_num), c2SB]
  have c3AB : c₃.nreg lAB = c.nmem (c.nreg lNF + 4) := by
    rw [k3 _ (by unfold lAB lJP sw; norm_num) (by unfold lAB lJN sw; norm_num), c2AB]
  have c3J : c₃.nreg lJ = j := by
    rw [k3 _ (by unfold lJ lJP sw; norm_num) (by unfold lJ lJN sw; norm_num), c2J]
  have hm3 : c₃.nmem = c.nmem := by rw [hm3', hm2]
  -- the regions
  have hseqv : ∀ p, p < N.arcs.length → c.nmem (c.nmem (c.nreg lNF + 6) + p) = sj N p := fun p hp =>
    hNA.2.2.2.2.2.2.2.2.1 p (by rwa [NFLoc.seq_length hL.hNF])
  have hsjl : ∀ p, p < N.arcs.length → sj N p < N.arcs.length := fun p hp => NFLoc.seq_lt hL.hNF hp
  have hregv : ∀ p, p < N.arcs.length →
      c.nmem (c.nmem (c.nreg lNF + 4) + 5 * c.nmem (c.nmem (c.nreg lNF + 6) + p)) = (N.arc (sj N p)).reg := by
    intro p hp
    rw [hseqv p hp]; exact (hNA.2.2.2.2.2.2.1 _ (hsjl p hp)).1
  have hb1 : ∀ v, v < N.arcs.length → c.nmem (c.nreg lNF + 6) + v ≤ W ∧
      c.nmem (c.nreg lNF + 4) + 5 * c.nmem (c.nmem (c.nreg lNF + 6) + v) ≤ W := by
    intro v hv
    rw [hseqv v hv]
    have := b3 _ (hsjl v hv)
    constructor <;> omega
  have hbound : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      c₃.nreg lSB + c₃.nreg p ≤ W ∧ c₃.nreg lAB + 5 * c₃.nmem (c₃.nreg lSB + c₃.nreg p) ≤ W := by
    intro p hp
    rw [c3SB, c3AB, hm3]
    rcases hp with h | h | h <;> rw [h]
    · rw [v3P]; exact hb1 _ hjP
    · rw [c3J]; exact hb1 _ hj1
    · rw [v3N]; exact hb1 _ hjN
  refine IRS.seq (IRS.block nbrRegsL hI₃ (nbrRegsL_ok _ _ hbound)) ?_
  rintro c₄ hI₄ - - hc4
  obtain ⟨v40, v41, v42⟩ := nbrRegsL_val c₃.nmem c₃.nreg
  have c4R0 : c₄.nreg lR0 = (N.arc (sj N (predP N.arcs.length j))).reg := by
    rw [hc4]; show regB c₃.nmem nbrRegsL c₃.nreg lR0 = _
    rw [v40, c3SB, c3AB, v3P, hm3, hregv _ hjP]
  have c4R1 : c₄.nreg lR1 = (N.arc (sj N j)).reg := by
    rw [hc4]; show regB c₃.nmem nbrRegsL c₃.nreg lR1 = _
    rw [v41, c3SB, c3AB, c3J, hm3, hregv _ hj1]
  have c4R2 : c₄.nreg lR2 = (N.arc (sj N (succP N.arcs.length j))).reg := by
    rw [hc4]; show regB c₃.nmem nbrRegsL c₃.nreg lR2 = _
    rw [v42, c3SB, c3AB, v3N, hm3, hregv _ hjN]
  have c4r : ∀ r, r ≠ lX → r ≠ lY → r ≠ lR0 → r ≠ lR1 → r ≠ lR2 → c₄.nreg r = c₃.nreg r := by
    intro r h1 h2 h3 h4 h5; rw [hc4]; exact nbrRegsL_other _ _ h1 h2 h3 h4 h5
  have hm4 : c₄.nmem = c.nmem := by rwa [hc4]
  have hA4 : c₄.nreg ALLOC = c.nreg ALLOC := by
    rw [c4r _ (by unfold ALLOC lX sw; omega) (by unfold ALLOC lY sw; omega)
      (by unfold ALLOC lR0 sw; omega) (by unfold ALLOC lR1 sw; omega) (by unfold ALLOC lR2 sw; omega),
      k3 _ (by unfold ALLOC lJP sw; omega) (by unfold ALLOC lJN sw; omega),
      c2r _ (by unfold ALLOC lX sw; omega) (by unfold ALLOC lA sw; omega)
        (by unfold ALLOC lSB sw; omega) (by unfold ALLOC lAB sw; omega), hA1]
  have c4J : c₄.nreg lJ = j := by
    rw [c4r _ (by unfold lJ lX sw; norm_num) (by unfold lJ lY sw; norm_num)
      (by unfold lJ lR0 sw; norm_num) (by unfold lJ lR1 sw; norm_num) (by unfold lJ lR2 sw; norm_num),
      c3J]
  -- 4. store the list
  refine (put3_irs hI₄ (hK.fix hI₄) (by rw [hA4]; unfold lh1K at hroom; omega)).mono le_rfl ?_
  rintro c₅ ⟨hA5, hL5, k5, hm5⟩
  have ls : ∀ q, LSet q → q ≠ ALLOC := fun q hq => by unfold LSet sw at hq; unfold ALLOC; omega
  have nl : ∀ q g, LSet g → ¬ LSet q → q ≠ g := fun q g hg hq h => hq (h ▸ hg)
  have c5J : c₅.nreg lJ = j := by
    rw [k5 _ (by unfold lJ ALLOC sw; omega) (by unfold lJ lL sw; norm_num), c4J]
  have hlist : c₅.nmem = mem3 c.nmem (c.nreg ALLOC) (N.arc (sj N (predP N.arcs.length j))).reg
      (N.arc (sj N j)).reg (N.arc (sj N (succP N.arcs.length j))).reg := by
    rw [hm5, hm4, hA4, c4R0, c4R1, c4R2]
  refine ⟨by rwa [c5J], fun h => by rw [c5J]; exact hl1 h, fun h => by rw [c5J]; exact hl2 h,
    by rw [hL5, hA4], by rw [hA5, hA4], fun i hi => ?_, fun a ha => ?_, fun r hr hrl hra => ?_,
    by rw [c5J, k5 _ (by unfold lR0 ALLOC sw; omega) (by unfold lR0 lL sw; omega), c4R0],
    by rw [c5J, k5 _ (by unfold lR1 ALLOC sw; omega) (by unfold lR1 lL sw; omega), c4R1],
    by rw [c5J, k5 _ (by unfold lR2 ALLOC sw; omega) (by unfold lR2 lL sw; omega), c4R2]⟩
  · rw [hlist, c5J]
    unfold mem3 Sweep.nbrRegs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · simp (disch := omega) only [upd, Nat.add_zero, ite_eq_right, ite_true]; rfl
    · simp (disch := omega) only [upd, ite_eq_right, ite_true]; rfl
    · simp (disch := omega) only [upd, ite_eq_right, ite_true]; rfl
  · rw [hlist]; unfold mem3; simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · have h1 : r ≠ lL := nl r lL (by unfold LSet lL sw; omega) hrl
    rw [k5 r hra h1,
      c4r r (nl r lX (by unfold LSet lX sw; omega) hrl) (nl r lY (by unfold LSet lY sw; omega) hrl)
        (nl r lR0 (by unfold LSet lR0 sw; omega) hrl) (nl r lR1 (by unfold LSet lR1 sw; omega) hrl)
        (nl r lR2 (by unfold LSet lR2 sw; omega) hrl),
      k3 r (nl r lJP (by unfold LSet lJP sw; omega) hrl) (nl r lJN (by unfold LSet lJN sw; omega) hrl),
      c2r r (nl r lX (by unfold LSet lX sw; omega) hrl) (fun h => by subst h; unfold lA LSet sw at hrl; omega)
        (fun h => by subst h; unfold lSB LSet sw at hrl; omega)
        (fun h => by subst h; unfold lAB LSet sw at hrl; omega)]
    exact k1 r hr (nl r lJ (by unfold LSet lJ sw; omega) hrl) hra

end

end SweepIo

end Chazelle.Core
