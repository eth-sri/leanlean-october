module

public import Chazelle.Core.RestoreFHv
public import Chazelle.Core.RestoreSearchGood
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# WP-E, the search on the RAM (`FindOK`), part 6: testing a walk vertex

`FWin E c`: the flag `81007` is a bit, and when it is set the triple `81008 … 81010` is a
splitting chord of the region (the soundness half of `FindOK`).  `tVert a`: test the walk vertex
in register `a` in both directions (candidate `81060 … 81063`, its height vertex by `fHv`).  When
the flag is clear and the vertex is a good candidate (`GoodCand`) in one of the directions, the
flag is set afterwards.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt)

/-- **The result registers are sound.** -/
def FWin (E : FEnv) (c : Config) : Prop :=
  c.nreg 81007 ≤ 1 ∧ (c.nreg 81007 = 1 → ∀ reg, NFRegs E.M (Qof E.P) E.N reg →
    (recOf (c.nreg 81008, c.nreg 81009, c.nreg 81010)).Attached E.M (Qof E.P) ∧
    c.nreg 81008 < (Qof E.P).n ∧
    (recOf (c.nreg 81008, c.nreg 81009, c.nreg 81010)).toSet E.M (Qof E.P) ∈ E.M.Adm ∧
    SplitsWell E.M (E.N.F E.M (Qof E.P)) (reg E.r)
      ((recOf (c.nreg 81008, c.nreg 81009, c.nreg 81010)).toSet E.M (Qof E.P)))

/-- A good candidate at the walk vertex `v` in the direction of the bit `σb`. -/
def GoodAt (E : FEnv) (reg : ℕ → Set Point) (v σb : ℕ) : Prop :=
  ∃ T, GoodCand E.M (Qof E.P) (E.N.F E.M (Qof E.P)) (reg E.r) ⟨v, 0⟩ (dirOf σb) T

variable {E : FEnv} {c₀ c : Config}

/-- **A test at a good candidate sets the flag.** -/
theorem TOut.good (hE : FGood E c₀) {c' : Config} (h : TOut E c c') {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) (hch : (E.N.region E.r).chords ≠ [])
    (hx1 : c.nreg 81061 = 0) (hg : GoodAt E reg (c.nreg 81060) (c.nreg 81063)) :
    c'.nreg 81007 = 1 := by
  obtain ⟨T, hx0, hxe, hσ, hT, hsec, hdom, hout, hadm, hsw⟩ := hg
  obtain ⟨-, -, hcl⟩ := h
  obtain ⟨-, hex, hcomp⟩ := hcl reg hregs
  have hxeq : (⟨c.nreg 81060, c.nreg 81061⟩ : WPos) = ⟨c.nreg 81060, 0⟩ := by rw [hx1]
  rw [hxeq] at hex hcomp
  have hp0 : E.M.param (Qof E.P) ⟨c.nreg 81060, 0⟩ = 0 := rfl
  obtain ⟨h10, h11⟩ := hcomp (by rwx [hp0]) hch T hT hdom hout hadm hsw.1 hsw.2.1
  obtain ⟨T', hT', hstr, hposf, hfe, hfp, hadm', hA, hB, hiff⟩ := hex h10 h11
  have hM := walkAx_of_goodModel hE.hGM
  have hout' : rayPt (E.M.pos (Qof E.P) ⟨c.nreg 81060, 0⟩) (dirOf (c.nreg 81063)) T' ∉ E.M.D := by
    rw [← hposf]
    exact hM.trace _ hfe _ hfp.1 hfp.2.1.le
  have hdom' : ∀ t, 0 < t → t < T' →
      rayPt (E.M.pos (Qof E.P) ⟨c.nreg 81060, 0⟩) (dirOf (c.nreg 81063)) t ∈ E.M.D :=
    fun t h0 h1 => (Chazelle.Chain.regionsIn_subset (hregs.1.1 _ hE.hr) (hstr t h0 h1)).1
  obtain rfl : T = T' := exit_unique hT hT' hdom hout hdom' hout'
  refine hiff.2 ?_
  have hAB : sidePt E.M.W (c.nreg 81060) (E.M.param (Qof E.P) ⟨c.nreg 81060, 0⟩) ≠
      sidePt E.M.W (c'.nreg 83012) (E.M.param (Qof E.P) ⟨c'.nreg 83012, c'.nreg 83013⟩) := by
    show E.M.pos (Qof E.P) ⟨c.nreg 81060, 0⟩ ≠ E.M.pos (Qof E.P) ⟨c'.nreg 83012, c'.nreg 83013⟩
    rw [hposf]; exact ray_ne hT
  exact counts_of_splitsWell hM hE.hNF.1.2.1 hE.hNF.1.1 (hregs.1.1 _ hE.hr) hadm hA hB hAB hsw

/-- **The test call**, with the soundness of the result registers. -/
theorem tcall_win (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hcand : c.nreg 81007 = 0 →
      CandOK E ⟨c.nreg 81060, c.nreg 81061⟩ (c.nreg 81062) (c.nreg 81063))
    (hroom : c.nreg ALLOC + tK E ≤ E.W) :
    FRS B E.P E.W c₀ (tcall E.sT) c (tK E) (fun c' => TKeep c c' ∧ FWin E c' ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg 81061 = 0 → GoodAt E reg (c.nreg 81060) (c.nreg 81063) → c'.nreg 81007 = 1)) := by
  refine (tcall_fs hE hB hBT hI hw.1 hcand hroom).mono le_rfl (fun c' ⟨hk, hfl, h1, h0⟩ => ?_)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hw.1 with hz | ho
  · have hout := h0 hz
    refine ⟨hk, ⟨hfl, fun hf reg hregs => (hout.2.2 reg hregs).1 hf⟩, fun h => by omega,
      fun reg hregs hch hx1 hg => hout.good hE hregs hch hx1 hg⟩
  · obtain ⟨f1, t8, t9, t10⟩ := h1 ho
    refine ⟨hk, ⟨hfl, fun _ reg hregs => ?_⟩, fun _ => f1, fun _ _ _ _ _ => f1⟩
    rw [t8, t9, t10]; exact hw.2 ho reg hregs

/-! ## Testing a walk vertex in both directions -/

/-- **Test the walk vertex in register `a`** in both directions. -/
def tVert (a : ℕ) (sT : Stmt) : Stmt :=
  .seq (Stmt.block [.copyN 81060 a, .constN 81061 0]) (.seq (fHv 81060)
    (.seq (.seq (Stmt.block [.constN 81063 0]) (tcall sT))
      (.seq (Stmt.block [.constN 81063 1]) (tcall sT))))

/-- The cost bound of `tVert`. -/
def tvK (E : FEnv) : ℕ := 2 * tK E + hvK + 4

/-- The registers `tVert` writes below the test's registers. -/
def VertW (q : ℕ) : Prop := 81060 ≤ q ∧ q ≤ 81064

/-- **Testing a walk vertex** as a run step of the search. -/
theorem tVert_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {a : ℕ}
    (hv : c.nreg a < E.M.W.n)
    (hset : ∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) ⟨c.nreg a, 0⟩ ∈ C.set)
    (hroom : c.nreg ALLOC + tvK E ≤ E.W) :
    FRS B E.P E.W c₀ (tVert a E.sT) c (tvK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        ∀ σb, σb ≤ 1 → GoodAt E reg (c.nreg a) σb → c'.nreg 81007 = 1)) := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; ufo hostWords at this
  have hAW  := hI.hw.1 ALLOC
  -- the candidate vertex
  have ok1 : okB E.W c.nmem [.copyN 81060 a, .constN 81061 0] c.nreg := by
    simp only [okB, okI]
    exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
      ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by omega⟩, trivial⟩
  refine (FRS.seq (K₂ := 2 * tK E + hvK + 2) (FRS.block hB _ hI ok1)
    (fun c₁ hI₁ hA₁ h₁ => ?_)).mono
    (by sio only [List.length_cons, List.length_nil, tvK]) (fun _ => id)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81060 a, .constN 81061 0] c.nreg q :=
    fun q => by rw [h₁]
  have v60 : c₁.nreg 81060 = c.nreg a := by rw [e₁]; simp [regB, regI, upd]
  have v61 : c₁.nreg 81061 = 0 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81060 → q ≠ 81061 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₁]; simp [regB, regI, upd, h1, h2]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by ufo ALLOC)
    (by ufo ALLOC)
  -- the height vertex
  refine (FRS.seq (K₂ := 2 * tK E + 2) (fHv_fs hE hB hI₁ (a := 81060) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rwx [v60]) (by rwx [v60])
    (by ruo [hA₁'] tvK at hroom)) (fun c₂ hI₂ hA₂ ⟨hv2, hy2, fr2⟩ => ?_)).mono
    (by omega) (fun _ => id)
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
      c₂.nreg q = c.nreg q := fun q h1 h2 h3 h4 h5 h6 => by
    rw [fr2 q h1 h2 h5 h6, f₁ q h3 h4]
  have w60 : c₂.nreg 81060 = c.nreg a := by
    rw [fr2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), v60]
  have w61 : c₂.nreg 81061 = 0 := by
    rw [fr2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), v61]
  have hw₂ : FWin E c₂ := by
    unfold FWin
    rw [g₂ 81007 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), g₂ 81008 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), g₂ 81009 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), g₂ 81010 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hw
  have hA₂' : c₂.nreg ALLOC ≤ c.nreg ALLOC + hvK := by rwx [← hA₁']
  rw [v60] at hy2
  -- a direction bit and a test
  have dir : ∀ (b : ℕ) (cx : Config), b ≤ 1 → FInv E.W c₀ cx → FWin E cx →
      cx.nreg 81060 = c.nreg a → cx.nreg 81061 = 0 → cx.nreg 81062 = c₂.nreg 81062 →
      cx.nreg ALLOC + tK E + 1 ≤ E.W →
      FRS B E.P E.W c₀ (.seq (Stmt.block [.constN 81063 b]) (tcall E.sT)) cx (tK E + 1)
        (fun c' => FWin E c' ∧ (∀ q, 81011 ≤ q → q < 83000 → q ≠ 81063 → c'.nreg q = cx.nreg q) ∧
          (cx.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
          (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
            GoodAt E reg (c.nreg a) b → c'.nreg 81007 = 1)) := by
    intro b cx hb hIx hwx x60 x61 x62 hrx
    have okb : okB E.W cx.nmem [.constN 81063 b] cx.nreg := by
      simp only [okB, okI]; exact ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by omega⟩, trivial⟩
    refine (FRS.seq (K₂ := tK E) (FRS.block hB _ hIx okb) (fun cy hIy hAy hy => ?_)).mono
      (by sio only [List.length_cons, List.length_nil]) (fun _ => id)
    have ey : ∀ q, cy.nreg q = regB cx.nmem [.constN 81063 b] cx.nreg q := fun q => by rw [hy]
    have y63 : cy.nreg 81063 = b := by rw [ey]; simp [regB, regI, upd]
    have fy : ∀ q, q ≠ 81063 → cy.nreg q = cx.nreg q := fun q hq => by
      rw [ey]; simp [regB, regI, upd, hq]
    have hwy : FWin E cy := by
      unfold FWin
      rw [fy 81007 (by norm_num), fy 81008 (by norm_num), fy 81009 (by norm_num),
        fy 81010 (by norm_num)]
      exact hwx
    have hcand : CandOK E ⟨cy.nreg 81060, cy.nreg 81061⟩ (cy.nreg 81062) (cy.nreg 81063) := by
      rw [fy _ (by norm_num), fy _ (by norm_num), fy _ (by norm_num), y63, x60, x61, x62]
      exact ⟨hv, ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩, Or.inl rfl,
        hset, hv2, hy2, hb⟩
    refine (tcall_win hE hB hBT hIy hwy (fun _ => hcand) (by
      rwo [fy _ (by ufo ALLOC)])).mono le_rfl
      (fun c' ⟨hk, hw', hm, hg⟩ => ⟨hw', fun q h1 h2 h3 => by rw [hk q h1 h2, fy q h3], fun h => hm
        (by rwx [fy _ (by norm_num)]), fun reg hregs hch hgd => hg reg hregs hch
          (by rw [fy _ (by norm_num), x61]) (by rwx [fy _ (by norm_num), y63, x60])⟩)
  refine (FRS.seq (K₂ := tK E + 1)
    (dir 0 c₂ (by norm_num) hI₂ hw₂ w60 w61 rfl (by ufo tvK at hroom))
    (fun c₄ hI₄ hA₄ ⟨hw₄, fr₄, hm₄, hg₄⟩ => ?_)).mono (by omega) (fun _ => id)
  refine (dir 1 c₄ le_rfl hI₄ hw₄ (by rw [fr₄ _ (by norm_num) (by norm_num) (by norm_num), w60])
    (by rw [fr₄ _ (by norm_num) (by norm_num) (by norm_num), w61])
    (by rw [fr₄ _ (by norm_num) (by norm_num) (by norm_num)])
    (by ufo tvK at hroom)).mono le_rfl
    (fun c₆ ⟨hw₆, fr₆, hm₆, hg₆⟩ => ⟨hw₆, fun q h1 h2 hq => ?_, fun h => hm₆ (hm₄ ?_),
      fun reg hregs hch σb hσb hgd => ?_⟩)
  · unfold VertW at hq
    rw [fr₆ q h1 h2 (by omega), fr₄ q h1 h2 (by omega)]
    exact g₂ q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [g₂ 81007 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]; exact h
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hσb with rfl | rfl
    · exact hm₆ (hg₄ reg hregs hch hgd)
    · exact hg₆ reg hregs hch hgd

end

end Restore

end Chazelle.Core
