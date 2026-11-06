module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.SweepEvTasks
public import Chazelle.Core.SweepIoLHit
public import Chazelle.Core.SweepIoGather

/-!
# The sweep (WP-D), stages 2–3: the region faced at a walk vertex of `C₂` (task D1, RAM part 1)

`faceLoc`: double identification of the walk vertex `(fE, 0)` of the model of `C₂` in `N₂`
(`locJ` with the model descriptor at `sw 31`, the normal form at `sw 4`), the spine positions
`j - 1`, `j`, `j + 1` and the regions of their arcs (the answer stage's (`SweepIo`) blocks `nbrHead`, `nbrJ`,
`nbrRegsL`, registers `sw 1102 … 1118`), and the two ends of the arc at `j` (registers
`fSE, fSH, fEE, fEH = sw 1200 … 1203`).  Post `LocOut`, run step `faceLoc_irs`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

/-! ## Registers and program -/

def fSE : ℕ := sw 1200
def fSH : ℕ := sw 1201
def fEE : ℕ := sw 1202
def fEH : ℕ := sw 1203
def fO : ℕ := sw 1204

/-- Read the ends of the arc at the spine position `lJ`. -/
def faceRead : List Instr :=
  [.addN lX lSB lJ, .loadN lX lX, .addN lY lX lX, .addN lY lY lY, .addN lY lY lX,
    .addN lY lAB lY, .addN lY lY K1, .loadN fSE lY, .addN lY lY K1, .loadN fSH lY,
    .addN lY lY K1, .loadN fEE lY, .addN lY lY K1, .loadN fEH lY]

/-- **The prefix of `face`**: locate, header, neighbours, regions, the arc at `j`. -/
def faceLoc : Stmt :=
  .seq (locJ (sw 31) (sw 4) fE K0 lJ)
    (.seq (block [.copyN lNF (sw 4)])
      (.seq (block nbrHead) (.seq nbrJ (.seq (block nbrRegsL) (block faceRead)))))

/-- The cost of the prefix. -/
def faceLocK (L : ℕ) : ℕ := 5500 * (L + 1) + 9 + 60

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The arc read -/

section
variable (m f : ℕ → ℕ)
section
variable (hk1 : f K1 = 1)
include hk1
theorem faceRead_val :
    regB m faceRead f fSE = m (f lAB + 5 * m (f lSB + f lJ) + 1) ∧
    regB m faceRead f fSH = m (f lAB + 5 * m (f lSB + f lJ) + 2) ∧
    regB m faceRead f fEE = m (f lAB + 5 * m (f lSB + f lJ) + 3) ∧
    regB m faceRead f fEH = m (f lAB + 5 * m (f lSB + f lJ) + 4) := by
  have e1 : f 240611 = 1 := hk1
  simp only [faceRead, regB, regI, upd, lX, lY, lSB, lAB, lJ, fSE, fSH, fEE, fEH, K1, sw]
  simp_all +arith

theorem faceRead_ok (hb1 : f lSB + f lJ ≤ W)
    (hb2 : f lAB + 5 * m (f lSB + f lJ) + 4 ≤ W) : okB W m faceRead f := by
  have e1 : f 240611 = 1 := hk1
  have hb1' : f 241115 + f 241108 ≤ W := hb1
  have hb2' : f 241116 + 5 * m (f 241115 + f 241108) + 4 ≤ W := hb2
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [faceRead, okB, okI, regI, upd, lX, lY, lSB, lAB, lJ, fSE, fSH, fEE, fEH, K1, sw]
  grind


end

theorem faceRead_other {q : ℕ} (h1 : q ≠ lX) (h2 : q ≠ lY) (h3 : q ≠ fSE)
    (h4 : q ≠ fSH) (h5 : q ≠ fEE) (h6 : q ≠ fEH) : regB m faceRead f q = f q :=
  regB_other m faceRead f (fun i hi => by
    simp only [faceRead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> core_grind <;> intro h <;> subst h <;> simp_all)

/-- A block writing only registers of `sw 1102 … 1203` keeps the others. -/
theorem regB_out (l : List Instr)
    (hl : ∀ i ∈ l, sw 1102 ≤ dstI i ∧ dstI i ≤ sw 1203) {q : ℕ} (hq : q < sw 1102 ∨ sw 1203 < q) :
    regB m l f q = f q :=
  regB_other m l f (fun i hi h => by grind)


end

theorem faceRead_dst : ∀ i ∈ faceRead, sw 1102 ≤ dstI i ∧ dstI i ≤ sw 1203 := by
  intro i hi
  simp only [faceRead, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [dstI, lX, lY, fSE, fSH, fEE, fEH, sw]

/-! ## The environment at a run configuration -/

/-- A model descriptor survives a change of the memory above its bound. -/
theorem modelDesc_transport {m m' : ℕ → ℕ} {D E E' : ℕ} {M : Model}
    (hd : ModelDescAt m D (Qof P) M) (hwf : ModelDescWF P E m D)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescAt m' D (Qof P) M ∧ ModelDescWF P E' m' D := by
  rcases hd with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hL, hM⟩
  · obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hwf h0 hC he hE
    exact ⟨Or.inl ⟨w2, H, C, w3, rfl⟩, w1⟩
  · have hD6 := hwf.1
    have e0 : m' D = m D := he _ (by omega)
    have e1 : m' (D + 1) = m (D + 1) := he _ (by omega)
    refine ⟨Or.inr ⟨by rw [e0, h1], by simp_all, hM⟩, by omega, fun h => ?_⟩
    omega

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

section
variable (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
include E hI
/-- The model descriptor of `C₂` (`sw 31`, stage 0) at a run configuration. -/
theorem EvEnv.md₂ :
    ModelDescAt c.nmem (c.nreg (sw 31)) (Qof P) (chainModel J.right) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 31)) := by
  obtain ⟨H, -, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d31, w31⟩ := hst
  have e : c.nreg (sw 31) = c₀.nreg (sw 31) := hI.hin _ (by omega_nf)
  rw [e]
  exact modelDesc_transport d31 w31 (fun a ha => hI.hm a ha) hI.hA

/-- The normal form `N₂` is protected below the power table. -/
theorem EvEnv.nt₂ :
    NFWithin c.nmem (c.nreg (sw 4)) (c.nreg TBR) N₂ := by
  rw [hI.hin _ (show IFix (sw 4) by omega_nf),
    hI.hin _ (show IFix TBR by omega_nf)]
  have h := E.hTBR
  exact Robust.transport E.hNT₂ (fun a ha => hI.hm a (by omega))

/-- The power table at a run configuration. -/
theorem EvEnv.tab :
    (∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j) ∧ N₂.arcs.length < 2 ^ c.nreg TLR ∧
      c.nreg TBR + c.nreg TLR ≤ c₀.nreg ALLOC ∧ c.nreg TLR = c₀.nreg TLR := by
  have eB : c.nreg TBR = c₀.nreg TBR := hI.hin _ (by omega_nf)
  have eL : c.nreg TLR = c₀.nreg TLR := hI.hin _ (by omega_nf)
  have h := E.hTBR
  refine ⟨fun j hj => ?_, by rw [eL]; exact E.hbig₂, by omega, eL⟩
  rw [eL] at hj
  rw [eB, hI.hm _ (by omega)]
  exact E.htab j hj

/-! ## The prefix -/


end

/-- **The post of the prefix**: the spine answer `j` of double identification for the vertex
`(fE, 0)`, the regions of the arcs at `j - 1`, `j`, `j + 1`, the ends of the arc at `j`. -/
def LocOut (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c c' : Config) : Prop :=
  ∃ j, j < N₂.arcs.length ∧
    (¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P)) (c.nreg fE) →
      N₂.F (chainModel J.right) (Qof P) = ∅ ∨
        sideInArc (sk (chainModel J.right) (Qof P) N₂ j) (ek (chainModel J.right) (Qof P) N₂ j)
          (c.nreg fE)) ∧
    ((chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P)) (c.nreg fE) →
      sk (chainModel J.right) (Qof P) N₂ j = c.nreg fE ∨
        ek (chainModel J.right) (Qof P) N₂ j = c.nreg fE) ∧
    c'.nreg lR0 = (N₂.arc (sj N₂ (predP N₂.arcs.length j))).reg ∧
    c'.nreg lR1 = (N₂.arc (sj N₂ j)).reg ∧
    c'.nreg lR2 = (N₂.arc (sj N₂ (succP N₂.arcs.length j))).reg ∧
    c'.nreg fSE = (N₂.arc (sj N₂ j)).s.edge ∧ c'.nreg fSH = (N₂.arc (sj N₂ j)).s.hgt ∧
    c'.nreg fEE = (N₂.arc (sj N₂ j)).e.edge ∧ c'.nreg fEH = (N₂.arc (sj N₂ j)).e.hgt ∧
    c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
    ∀ r, bandOf r ∉ oracleBands → (r < sw 1102 ∨ sw 1203 < r) → c'.nreg r = c.nreg r

theorem out_ne {r q : ℕ} (hr : r < sw 1102 ∨ sw 1203 < r) (h1 : sw 1102 ≤ q) (h2 : q ≤ sw 1203) :
    r ≠ q := by
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The prefix of `face`.** -/
theorem faceLoc_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fE < (chainModel J.right).W.n)
    (hroom : c.nreg ALLOC + faceLocK (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ faceLoc c (faceLocK (c₀.nreg TLR)) (LocOut P J N₂ c) := by
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
  have hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg fE, c.nreg K0⟩ := by
    grind [Chazelle.Core.ProperPos, Model.param]
  -- 1. locate
  unfold faceLoc
  refine IRS.mono (K := (5500 * (c.nreg TLR + 1) + 9) + (1 + (6 + (7 + (21 + 14)))))
    (IRS.seq (locJ_irs (md := sw 31) (nf := sw 4) (pe := fE) (ph := K0) (o := lJ) hI E.hG E.hWh
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf⟩
      ⟨by omega_nf, by omega_nf⟩ hmd hmwf hP₂ hNA hNF
      hfe hpp htab hbig (by omega) (by omega) (by omega) (by omega)
      (by grind [faceLocK])) ?_)
    (by simp_all [faceLocK] ) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨hj1, hl1, hl2, k1', hA1, hm1⟩
  set j := c₁.nreg lJ with hjd
  rw [k0, key_vertex] at hl1 hl2
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
    grind [lJ, lX, sw, lA, lSB, lAB, lNF]
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
  have hm5 : c₅.nmem = c.nmem := by rw [hc5]; exact hm4
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
    ?_, ?_, ?_, ?_, by rw [hc6]; exact hm5,
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
