module

meta import Chazelle.Programs.RegisterGuard

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.SweepEvSym
public import Chazelle.Core.SweepEvOrgM
public import Chazelle.Core.SweepIoLH
public import Chazelle.Core.SweepIoHoleRam

/-!
# The sweep (WP-D), stages 2–3: the end of a chord of `N₂` on the RAM, part 1 (reading)

`orgHead k s`: read the record of chord `k` of `N₂` (normal form at `sw 4`) and select its end
`s` (`0`: the left end, shot east; `1`: the right end, shot west): the height index, the regions
`up`, `dn`, the end position `(oE, oC)` and the far end `(oFE, oFC)` (both with height code
`h + 1`), the direction code `oD` (`1` east, `0` west).  Then `normS` normalises `(oE, oC)`.

Registers: inputs `oK = sw 2200`, `oS = sw 2201`, outputs and scratch `sw 2202 … 2231`.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam
open Chazelle.Chain (sidePt)

@[expose] public section

/-! ## Registers -/

@[ram_layout] def oK : ℕ := sw 2200
@[ram_layout] def oS : ℕ := sw 2201
@[ram_layout] def oX : ℕ := sw 2202
@[ram_layout] def oH : ℕ := sw 2203
@[ram_layout] def oL : ℕ := sw 2204
@[ram_layout] def oR : ℕ := sw 2205
@[ram_layout] def oUp : ℕ := sw 2206
@[ram_layout] def oDn : ℕ := sw 2207
@[ram_layout] def oE : ℕ := sw 2210
@[ram_layout] def oC : ℕ := sw 2211
@[ram_layout] def oFE : ℕ := sw 2212
@[ram_layout] def oFC : ℕ := sw 2213
@[ram_layout] def oD : ℕ := sw 2214
@[ram_layout] def oCl : ℕ := sw 2215
@[ram_layout] def oNo : ℕ := sw 2216
@[ram_layout] def oT : ℕ := sw 2218
@[ram_layout] def oJ : ℕ := sw 2219
@[ram_layout] def oSym : ℕ := sw 2220
@[ram_layout] def oAbsA : ℕ := sw 2224

/-! ## The program -/

/-- Read the record of chord `oK` of the normal form at `sw 4`. -/
def orgLoad : List Instr :=
  [.addN oX (sw 4) K3, .loadN oX oX, .addN oX oX oK, .addN oX oX oK, .addN oX oX oK,
    .addN oX oX oK, .addN oX oX oK, .loadN oH oX, .addN oX oX K1, .loadN oL oX,
    .addN oX oX K1, .loadN oR oX, .addN oX oX K1, .loadN oUp oX, .addN oX oX K1,
    .loadN oDn oX, .addN oC oH K1, .copyN oFC oC]

/-- Select the end. -/
def orgPick : Stmt :=
  .ifLtN oS K1 (block [.copyN oE oL, .copyN oFE oR, .constN oD 1])
    (block [.copyN oE oR, .copyN oFE oL, .constN oD 0])

/-- **Read and normalise the end `oS` of chord `oK`.** -/
def orgHead : Stmt := .seq (block orgLoad) (.seq orgPick (normS (sw 21) oE oC oNo))

/-! ## The register effect of the blocks -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem orgLoad_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) :
    regB m orgLoad f oH = m (m (f (sw 4) + 3) + 5 * f oK) ∧
    regB m orgLoad f oL = m (m (f (sw 4) + 3) + 5 * f oK + 1) ∧
    regB m orgLoad f oR = m (m (f (sw 4) + 3) + 5 * f oK + 2) ∧
    regB m orgLoad f oUp = m (m (f (sw 4) + 3) + 5 * f oK + 3) ∧
    regB m orgLoad f oDn = m (m (f (sw 4) + 3) + 5 * f oK + 4) ∧
    regB m orgLoad f oC = m (m (f (sw 4) + 3) + 5 * f oK) + 1 ∧
    regB m orgLoad f oFC = m (m (f (sw 4) + 3) + 5 * f oK) + 1 := by
  register_block normalized [orgLoad]

theorem orgLoad_other (m f : ℕ → ℕ) {q : ℕ} (h : q < sw 2202 ∨ sw 2213 < q) :
    regB m orgLoad f q = f q :=
  (by register_keep [orgLoad])

theorem orgLoad_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) (hb : f (sw 4) + 3 ≤ W)
    (hb2 : m (f (sw 4) + 3) + 5 * f oK + 4 ≤ W) (hh : m (m (f (sw 4) + 3) + 5 * f oK) + 1 ≤ W) :
    okB W m orgLoad f := by
  register_block normalized [orgLoad]

end

end SweepEv

end Chazelle.Core

namespace Chazelle.Core

namespace Sweep

open WalkEmbed

@[expose] public section

/-- The ends of a chord of a normal form of a chain model are strictly inside the box band. -/
theorem endPos_band {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF (chainModel C) Q N) {k : ℕ}
    (hk : k < N.nChords) (s : ℕ) :
    |((chainModel C).pos Q (endPos N k s)).2| < C.radius ∧
      |((chainModel C).pos Q (farEnd N k s)).2| < C.radius := by
  obtain ⟨y, a, b, hab, heq, hl, hr, -⟩ := rec_ends hN hk
  have hmem : (N.chord k).toSet (chainModel C) Q ∈ N.F (chainModel C) Q := by
    refine ⟨N.chord k, ?_, rfl⟩
    unfold NF.chord
    rw [NFLoc.getD_of_lt _ hk]
    exact List.getElem_mem _
  obtain ⟨y', a', b', hH, -, heq', -, -⟩ :=
    Merge.augChords_spec (show _ ∈ Merge.augChords C from hN.1.2.1 hmem)
  have hab' : a' < b' := hH.lt
  have hD := hH.open_mem ((a' + b') / 2) (by linarith) (by linarith)
  have hbox := C.dom_subset_box hD
  have hyy : y = y' := by
    have h1 : ((a + b) / 2, y) ∈ Visibility.hseg y a b := ⟨rfl, by linarith, by linarith⟩
    rw [← heq, heq'] at h1
    exact h1.1
  have hy : |y| < C.radius := by rw [hyy]; exact hbox.2
  unfold endPos farEnd
  split_ifs <;> simp only [hl, hr] <;> exact ⟨hy, hy⟩

end

end Sweep

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem band_sw_not {r : ℕ} (h : 240000 ≤ r ∧ r < 250000) : bandOf r ∉ oracleBands :=
  not_oracle_sw h.1 h.2

/-- **The selection of the end.** -/
theorem orgPick_irs (hI : IInv W c₀ c) (hk1 : c.nreg K1 = 1) (hs : c.nreg oS ≤ 1) :
    IRS P W c₀ orgPick c 5 (fun c' => c'.nmem = c.nmem ∧
      c'.nreg oE = (if c.nreg oS = 0 then c.nreg oL else c.nreg oR) ∧
      c'.nreg oFE = (if c.nreg oS = 0 then c.nreg oR else c.nreg oL) ∧
      c'.nreg oD = (if c.nreg oS = 0 then 1 else 0) ∧
      ∀ q, q ≠ oE → q ≠ oFE → q ≠ oD → c'.nreg q = c.nreg q) := by
  have hW := hI.hw
  unfold orgPick
  by_cases h0 : c.nreg oS < c.nreg K1
  · have hs0 : c.nreg oS = 0 := by omega
    refine (IRS.ifT h0 (IRS.block (P := P) [.copyN oE oL, .copyN oFE oR, .constN oD 1] hI ?_)).mono
      (by simp) ?_
    · simp only [reg_check, oE, oFE, oD, sw]
      simp only [Nat.reduceAdd]
      exact ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
        ⟨iscr_sw (by norm_num) (by norm_num), by have := hW.1 K1; rw [hk1] at this; exact this⟩, trivial⟩
    · rintro c' rfl
      refine ⟨rfl, ?_, ?_, ?_, fun q h1 h2 h3 => ?_⟩
      · simp [regB, regI, upd, oE, oFE, oD, oL, oR, sw, ite_eq_left hs0]
      · simp [regB, regI, upd, oE, oFE, oD, oL, oR, sw, ite_eq_left hs0]
      · simp [regB, regI, upd, oD, sw, ite_eq_left hs0]
      register_block
  · have hs1 : c.nreg oS ≠ 0 := by omega
    refine (IRS.ifF h0 (IRS.block (P := P) [.copyN oE oR, .copyN oFE oL, .constN oD 0] hI ?_)).mono
      (by simp) ?_
    · simp only [reg_check, oE, oFE, oD, sw]
      simp only [Nat.reduceAdd]
      exact ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
        ⟨iscr_sw (by norm_num) (by norm_num), Nat.zero_le _⟩, trivial⟩
    · rintro c' rfl
      refine ⟨rfl, ?_, ?_, ?_, fun q h1 h2 h3 => ?_⟩
      · simp [regB, regI, upd, oE, oFE, oD, oL, oR, sw, ite_eq_right hs1]
      · simp [regB, regI, upd, oE, oFE, oD, oL, oR, sw, ite_eq_right hs1]
      · simp [regB, regI, upd, oD, sw, ite_eq_right hs1]
      register_block

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Reading the end of a chord.** -/
theorem orgHead_irs {J : Merge.Junction} {N₂ : NF} {E : ℕ} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hctx : ChainCtx P W c (sw 21) J.right) (hNF : IsNF J.rightModel (Qof P) N₂)
    (hNW : NFWithin c.nmem (c.nreg (sw 4)) E N₂) (hE : E ≤ c.nreg ALLOC)
    (hk : c.nreg oK < N₂.nChords) (hs : c.nreg oS ≤ 1)
    (hroom : c.nreg ALLOC + 11100 ≤ W) :
    IRS P W c₀ orgHead c 11100 (fun c' =>
      c'.nreg oH = (N₂.chord (c.nreg oK)).h ∧ c'.nreg oUp = (N₂.chord (c.nreg oK)).up ∧
      c'.nreg oDn = (N₂.chord (c.nreg oK)).dn ∧
      c'.nreg oD = (if c.nreg oS = 0 then 1 else 0) ∧
      c'.nreg oE = (endPos N₂ (c.nreg oK) (c.nreg oS)).edge ∧
      c'.nreg oC = nhgt J.rightModel (Qof P) (endPos N₂ (c.nreg oK) (c.nreg oS)) ∧
      c'.nreg oFE = (farEnd N₂ (c.nreg oK) (c.nreg oS)).edge ∧
      c'.nreg oFC = (farEnd N₂ (c.nreg oK) (c.nreg oS)).hgt ∧
      (∀ r, bandOf r ∉ oracleBands → (r < sw 2202 ∨ sw 2217 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem)) := by
  have hK := hK₀.fix hI
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  set k := c.nreg oK with hkdef
  set s := c.nreg oS with hsdef
  have hNA : NFAt c.nmem (c.nreg (sw 4)) N₂ := hNW.holds
  obtain ⟨hch, -⟩ := hNA.2.2.2.2.2
  obtain ⟨b1, hb2, -⟩ := Restore.nf_bounds hNW
  have hW := hI.hw.1 ALLOC
  have hb : c.nreg (sw 4) + 3 ≤ W := by omega
  have hb2 : c.nmem (c.nreg (sw 4) + 3) + 5 * k + 4 ≤ W := by have := hb2 k hk; omega
  obtain ⟨r0, r1, r2, r3, r4⟩ := hch k hk
  have hhn := (regOf_spec hNF).2.2.2.2.2.1 k hk
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hPn : P.n ≤ W := by have := hctx.2.1; unfold hostWords at this; omega
  have hh : c.nmem (c.nmem (c.nreg (sw 4) + 3) + 5 * k) + 1 ≤ W := by
    unfold NF.nChords at hk; rw [r0]; omega
  -- the load block
  refine IRS.seq (K₁ := orgLoad.length) (K₂ := 11100 - orgLoad.length)
    (IRS.block orgLoad hI (orgLoad_ok c.nmem c.nreg k1 k3 hb hb2 hh)) ?_ |>.budget (by simp [orgLoad])
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨vH, vL, vR, vUp, vDn, vC, vFC⟩ := orgLoad_val c.nmem c.nreg k1 k3
  set c₁ : Config := { c with nreg := regB c.nmem orgLoad c.nreg } with hc₁
  have ko : ∀ q, (q < sw 2202 ∨ sw 2213 < q) → c₁.nreg q = c.nreg q :=
    fun q hq => orgLoad_other _ _ hq
  have c1S : c₁.nreg oS = s := ko oS (by register_guard)
  have c1K1 : c₁.nreg K1 = 1 := (ko K1 (by register_guard)).trans k1
  -- the end position
  have hA := hNF.2.2.1 k hk
  have hlp : (N₂.chord k).lp < J.rightModel.W.n := hA.1.1
  have hrp : (N₂.chord k).rp < J.rightModel.W.n := hA.2.1
  have hpl : ProperPos J.rightModel (Qof P) P.n (N₂.chord k).lpos :=
    ⟨hA.1.2.1, hA.1.2.2.1, by show (N₂.chord k).h + 1 ≤ P.n; rw [← hQn]; omega⟩
  have hpr : ProperPos J.rightModel (Qof P) P.n (N₂.chord k).rpos :=
    ⟨hA.2.2.1, hA.2.2.2.1, by show (N₂.chord k).h + 1 ≤ P.n; rw [← hQn]; omega⟩
  obtain ⟨hbandE, -⟩ := endPos_band hNF hk s
  -- the selection
  have hc1 := ko K1 (by register_guard)
  refine IRS.seq (K₁ := 5) (K₂ := 11100 - orgLoad.length - 5)
    (orgPick_irs hI₁ (by rw [hc1]; exact k1) (by rw [c1S]; exact hs)) ?_ |>.budget (by simp [orgLoad])
  rintro c₂ hI₂ hA₂ hA₂' ⟨hm₂, vE, vFE, vD, k₂⟩
  have hl : orgLoad.length = 18 := rfl
  rw [c1S] at vE vFE vD
  have q₂ : ∀ q, q ≠ oE → q ≠ oFE → q ≠ oD → (q < sw 2202 ∨ sw 2213 < q) → c₂.nreg q = c.nreg q :=
    fun q h1 h2 h3 h4 => (k₂ q h1 h2 h3).trans (ko q h4)
  have hE₂ : c₂.nreg oE = (endPos N₂ k s).edge := by
    rw [vE]; unfold endPos
    split_ifs
    · exact vL.trans r1
    · exact vR.trans r2
  have hFE₂ : c₂.nreg oFE = (farEnd N₂ k s).edge := by
    rw [vFE]; unfold farEnd
    split_ifs
    · exact vR.trans r2
    · exact vL.trans r1
  have hC₂ : c₂.nreg oC = (N₂.chord k).h + 1 := by
    ram_rw [k₂ oC]
    exact (congrArg (· + 1) r0).symm ▸ vC
  have hFC₂ : c₂.nreg oFC = (N₂.chord k).h + 1 := by
    ram_rw [k₂ oFC]
    exact (congrArg (· + 1) r0).symm ▸ vFC
  have hpos : (⟨c₂.nreg oE, c₂.nreg oC⟩ : WPos) = endPos N₂ k s := by
    rw [hE₂, hC₂]; unfold endPos; split_ifs <;> rfl
  have hctx₂ : ChainCtx P W c₂ (sw 21) J.right :=
    hctx.transport (by ram_post [q₂])
      (fun a ha => by rw [hm₂]) (by omega)
  have hpp : ProperPos J.rightModel (Qof P) P.n ⟨c₂.nreg oE, c₂.nreg oC⟩ := by
    rw [hpos]; unfold endPos; split_ifs
    · exact hpl
    · exact hpr
  have he : c₂.nreg oE < J.rightModel.W.n := by
    rw [hE₂]; unfold endPos; split_ifs
    · exact hlp
    · exact hrp
  refine (normS_irs (P := P) (C := J.right) hI₂ (hK₀.fix hI₂) hctx₂
    (by register_guard) (by register_guard) he hpp
    (fun _ _ _ _ => by rw [hpos]; exact hbandE) (by rw [hl] at hA₁'; omega)).mono
    (by rw [hl]; norm_num) ?_
  rintro c₃ ⟨vE₃, vC₃, k₃, hA₃, hm₃⟩
  refine ⟨?_, ?_, ?_, ?_, by rw [vE₃, hE₂], by rw [vC₃, hpos], ?_, ?_, ?_, by omega, ?_⟩
  · rw [k₃ oH (band_sw_not (by register_guard)) (by register_guard)
      (by register_guard) (by register_guard) (by register_guard)]
    ram_rw [k₂ oH]
    exact vH.trans r0
  · rw [k₃ oUp (band_sw_not (by register_guard)) (by register_guard)
      (by register_guard) (by register_guard) (by register_guard)]
    ram_rw [k₂ oUp]
    exact vUp.trans r3
  · rw [k₃ oDn (band_sw_not (by register_guard)) (by register_guard)
      (by register_guard) (by register_guard) (by register_guard)]
    ram_rw [k₂ oDn]
    exact vDn.trans r4
  · rw [k₃ oD (band_sw_not (by register_guard)) (by register_guard)
      (by register_guard) (by register_guard) (by register_guard), vD]
  · rw [k₃ oFE (band_sw_not (by register_guard)) (by register_guard)
      (by register_guard) (by register_guard) (by register_guard), hFE₂]
  · rw [k₃ oFC (band_sw_not (by register_guard)) (by register_guard)
      (by register_guard) (by register_guard) (by register_guard), hFC₂]
    unfold farEnd; split_ifs <;> rfl
  · intro r hr hr2 hra
    rw [k₃ r hr (by register_guard) (by register_guard)
      (by register_guard) hra]
    ram_rw [k₂ r]
    exact ko r (by register_guard)
  · intro a ha
    ram_rw [hm₃ a, hm₂]

end

end SweepEv

end Chazelle.Core
