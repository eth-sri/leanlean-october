module

public import Chazelle.Core.RestoreFKind1
public import Chazelle.Core.RestoreFRebase
public import Chazelle.Core.RestoreTNorm
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-E, the search on the RAM (`FindOK`), part 25: an ordered pair of arcs

* `aNorm s`: normalise the walk position in `s`, `s + 1` (height code `0` iff parameter `0`), as
  the cutter's precondition asks (`ShootCut.box_param_pos'` at the box edges of a chain model).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- **Normalising a walk position** in `s`, `s + 1`. -/
def aNorm (s : ℕ) : Stmt :=
  .ifLtN 81011 (s + 1) (.ifLtN s 81021 .skip
    (.seq (Stmt.block [.copyN 81044 s, .constN 81045 0]) (.seq (cmpM 81046 81044 81045 s (s + 1))
      (.ifLtN 81011 81046 .skip (Stmt.block [.constN (s + 1) 0]))))) .skip

/-- The cost bound of `aNorm`. -/
def anK : ℕ := 11040

variable {E : FEnv} {c₀ c : Config}

theorem aNorm_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (hs : 81030 ≤ s ∧ s + 1 ≤ 81043)
    (hp : ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg s, c.nreg (s + 1)⟩) (hen : c.nreg s < E.M.W.n)
    (hy : ∀ C : Chain, E.M = chainModel C →
      |(E.M.pos (Qof E.P) ⟨c.nreg s, c.nreg (s + 1)⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + anK ≤ E.W) :
    FRS B E.P E.W c₀ (aNorm s) c anK (fun c' =>
      c'.nreg s = c.nreg s ∧
      c'.nreg (s + 1) = (normOf E.M (Qof E.P) ⟨c.nreg s, c.nreg (s + 1)⟩).hgt ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ s + 1 → ¬ (81044 ≤ q ∧ q ≤ 81047) →
        c'.nreg q = c.nreg q) := by
  have k0 := k0_of hE hI
  have hn : 0 < E.M.W.n := by omega
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  unfold normOf
  -- height code 0: nothing to do
  by_cases a1 : c.nreg 81011 < c.nreg (s + 1)
  swap
  · have h0 : c.nreg (s + 1) = 0 := by rwo [k0] at a1
    refine (FRS.ifF a1 (FRS.skip (K := 0) hI ⟨rfl, ?_, fun _ _ _ _ _ _ => rfl⟩)).mono
      (by ufo anK) (fun _ => id)
    split_ifs <;> simp [h0]
  refine (FRS.ifT a1 ?_).mono (K := anK - 2) (by ufo anK) (fun _ => id)
  have hh0 : 0 < c.nreg (s + 1) := by rw [k0] at a1; exact a1
  -- below the vertex range: a box edge of a chain model, positive parameter
  by_cases a2 : c.nreg s < c.nreg 81021
  · refine (FRS.ifT a2 (FRS.skip (K := 0) hI ⟨rfl, ?_, fun _ _ _ _ _ _ => rfl⟩)).mono
      (by omega) (fun _ => id)
    have hv : c.nreg 81021 = c₀.nreg 81021 := hI.hin _ (by ufo FFix)
    have hpos : 0 < E.M.param (Qof E.P) ⟨c.nreg s, c.nreg (s + 1)⟩ := by
      rw [hv] at a2
      by_cases hch : ∃ C : Chain, E.M = chainModel C
      · obtain ⟨C, hC⟩ := hch
        have hn7 : E.M.W.n = 2 * C.m + 7 := by rw [hC]; exact chainModel_n C
        have h6 := (hE.hvc 6 (by have := C.one_le; omega) (fun C' hC' => by
          rw [hC', pos_eq_sidePt]
          show Chazelle.Chain.sidePt (C'.sideWalk C'.sideBeta) 6 0 ∈ C'.set
          rw [Chazelle.Chain.sidePt_zero, C'.sideWalk_vtx_six]
          exact C'.top_mem_set)).1
        have he6 : c.nreg s < 6 := by omega
        have hp0 := hp.1
        have hy' := hy C hC
        rw [hC] at hp0 hy' ⊢
        exact ShootCut.box_param_pos' C (Qof E.P) he6 hp0 hy'
      · have := (hE.hvc (c.nreg s) hen (fun C hC => absurd ⟨C, hC⟩ hch)).1
        omega
    rw [ite_eq_right (ne_of_gt hpos)]
  refine (FRS.ifF a2 ?_).mono (K := anK - 4) (by ufo anK) (fun _ => id)
  have hv : c.nreg 81021 = c₀.nreg 81021 := hI.hin _ (by ufo FFix)
  have ok1 : okB E.W c.nmem [.copyN 81044 s, .constN 81045 0] c.nreg := by
    sin only [okB, okI, FScr, FOut]
  refine FRS.seq (K₂ := 11025) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
    (by simp) (fun _ => id)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81044 s, .constN 81045 0] c.nreg q :=
    fun q => by rw [h₁]
  have v44 : c₁.nreg 81044 = c.nreg s := by
    rw [e₁]; simp [regB, regI, upd]
  have v45 : c₁.nreg 81045 = 0 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81044 → q ≠ 81045 → c₁.nreg q = c.nreg q := fun q a b => by
    rw [e₁]; simp [regB, regI, upd, a, b]
  have w0 : c₁.nreg s = c.nreg s := f₁ _ (by omega) (by omega)
  have w1 : c₁.nreg (s + 1) = c.nreg (s + 1) := f₁ _ (by omega) (by omega)
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by ufo ALLOC) (by ufo ALLOC)
  have hpg0 : PosG E.M (Qof E.P) E.P.n ⟨c₁.nreg 81044, c₁.nreg 81045⟩ := by
    rw [v44, v45]
    refine ⟨hen, ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩, fun C hC _ => ?_⟩
    have := hE.vlo6 C hC; rw [hv] at a2; show 6 ≤ c.nreg s; omega
  have hpg1 : PosG E.M (Qof E.P) E.P.n ⟨c₁.nreg s, c₁.nreg (s + 1)⟩ := by
    rw [w0, w1]; exact ⟨hen, hp, fun _ _ h => absurd h (by show c.nreg (s + 1) ≠ 0; omega)⟩
  refine FRS.seq (K₁ := 11022) (K₂ := 3) (cmpM_fs hE hB hI₁ (r := 81046) (a := 81044)
    (b := 81045) (d := s) (e := s + 1) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by ufo KeyW)
    (by ufo KeyW) (by ufo KeyW) (by ufo KeyW) hpg0 hpg1
    (by rw [hA₁']; simp [List.length_cons, List.length_nil] at hA₁; ufo anK at hroom))
    (fun c₂ hI₂ hA₂ ⟨b46, _, f₂⟩ => ?_)
  rw [v44, v45, w0, w1, key_vtx_lt_iff] at b46
  have k0₂ := k0_of hE hI₂
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → ¬ (81044 ≤ q ∧ q ≤ 81047) →
      c₂.nreg q = c.nreg q := fun q a b h1 h2 => by
    rw [f₂ q a b h1 (by omega) (by omega), f₁ q (by omega) (by omega)]
  have y0 : c₂.nreg s = c.nreg s := g₂ s (by omega) (by omega) (by ufo KeyW) (by omega)
  have y1 : c₂.nreg (s + 1) = c.nreg (s + 1) :=
    g₂ _ (by omega) (by omega) (by ufo KeyW) (by omega)
  by_cases a3 : c₂.nreg 81011 < c₂.nreg 81046
  · have hpos : 0 < E.M.param (Qof E.P) ⟨c.nreg s, c.nreg (s + 1)⟩ := by
      rw [k0₂] at a3; exact b46.2.1 (by have := b46.1; omega)
    refine (FRS.ifT a3 (FRS.skip (K := 0) hI₂ ⟨y0, ?_, fun q a b h1 h2 h3 => g₂ q a b h1 h3⟩)).mono
      (by omega) (fun _ => id)
    rw [ite_eq_right (ne_of_gt hpos), y1]
  · have hz : E.M.param (Qof E.P) ⟨c.nreg s, c.nreg (s + 1)⟩ = 0 := by
      rw [k0₂] at a3
      have h46 : c₂.nreg 81046 ≠ 1 := by omega
      exact le_antisymm (not_lt.1 (fun h => h46 (b46.2.2 h))) hp.1
    have okz : okB E.W c₂.nmem [.constN (s + 1) 0] c₂.nreg := by
      sin only [okB, okI, FScr, FOut]; omega
    refine (FRS.ifF a3 (FRS.block hB _ hI₂ okz)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.constN (s + 1) 0] c₂.nreg q := fun q => by rw [h']
    refine ⟨by rw [e']; simp [regB, regI, upd]; exact y0, by rw [e', ite_eq_left hz]; simp [regB, regI, upd],
      fun q a b h1 h2 h3 => by rw [e']; simp [regB, regI, upd, h2]; exact g₂ q a b h1 h3⟩

/-! ## The piece loop -/

/-- The reads of piece `i` (`81079`) of the list at `L` (`81076`): its record address `81080`,
kind `81077`, start edge `81070`. -/
def pbL : List Instr :=
  [.addN 81080 81076 81012, .addN 81080 81080 81079, .addN 81080 81080 81079,
    .addN 81080 81080 81079, .addN 81080 81080 81079, .addN 81080 81080 81079,
    .addN 81080 81080 81079, .addN 81080 81080 81079, .addN 81073 81080 81014,
    .addN 81073 81073 81012, .loadN 81077 81073, .loadN 81070 81080]

/-- **One piece.** -/
def pieceBody (sT : Stmt) : Stmt :=
  .seq (Stmt.block pbL) (.seq (.ifLtN 81011 81077 (ifEq 81077 81012 (k1S sT)) (kind0 sT))
    (Stmt.block [.addN 81079 81079 81012]))

/-- The record address of piece `i` of the list at `L`. -/
def prOf (L i : ℕ) : ℕ := L + 1 + 7 * i

theorem pbL_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hPR : prOf (c.nreg 81076) (c.nreg 81079) + 6 < c₀.nreg ALLOC) :
    FRS B E.P E.W c₀ (Stmt.block pbL) c 12 (fun c' =>
      c'.nreg 81080 = prOf (c.nreg 81076) (c.nreg 81079) ∧
      c'.nreg 81077 = c₀.nmem (prOf (c.nreg 81076) (c.nreg 81079) + 4) ∧
      c'.nreg 81070 = c₀.nmem (prOf (c.nreg 81076) (c.nreg 81079)) ∧
      ∀ q, q ≠ 81070 → q ≠ 81073 → q ≠ 81077 → q ≠ 81080 → c'.nreg q = c.nreg q) := by
  have hA0  := hI.hA
  have hAW  := hI.hw.1 ALLOC
  have k1 : c.nreg 81012 = 1 := by rw [hI.hin _ (by ufo FFix), hE.k1]
  have k3 : c.nreg 81014 = 3 := by rw [hI.hin _ (by ufo FFix), hE.k3]
  unfold prOf at *
  have ok : okB E.W c.nmem pbL c.nreg := by
    sin only [pbL, okB, okI, regI, upd, FScr, FOut, k1, k3]; omega
  refine (FRS.block hB _ hI ok).mono (by simp [pbL]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem pbL c.nreg q := fun q => by rw [h']
  have ea : c.nreg 81076 + 1 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 +
      c.nreg 81079 + c.nreg 81079 + c.nreg 81079 = c.nreg 81076 + 1 + 7 * c.nreg 81079 := by ring
  refine ⟨?_, ?_, ?_, fun q a b d e => ?_⟩
  · rw [e']; simp [pbL, regB, regI, upd, k1]; rw [← ea]
  · rw [e']; simp [pbL, regB, regI, upd, k1, k3]
    rw [show c.nreg 81076 + 1 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 +
      c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + 3 + 1 =
      c.nreg 81076 + 1 + 7 * c.nreg 81079 + 4 by ring]
    exact hI.hm _ (by omega)
  · rw [e']; simp [pbL, regB, regI, upd, k1]
    rw [show c.nreg 81076 + 1 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 +
      c.nreg 81079 + c.nreg 81079 + c.nreg 81079 = c.nreg 81076 + 1 + 7 * c.nreg 81079 by ring]
    exact hI.hm _ (by omega)
  · rw [e', regB_other _ _ _ (fun i hi => ?_)]
    simp [pbL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [dstI] <;> omega

/-- The facts a kind-1 piece at the record `PR` needs (from the cutter's contract, below the base
of the search). -/
structure K1Hyp (E : FEnv) (c₀ : Config) (PR : ℕ) (Hs : Host) (Cα : Chain) (N : NF) (γ' : ℕ) :
    Prop where
  hPR : PR + 6 < c₀.nreg ALLOC
  hCD : ChainDescAt c₀.nmem (c₀.nmem (PR + 5)) (Qof E.P) Hs Cα
  hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c₀.nmem (PR + 5))
  hNW : NFWithin c₀.nmem (c₀.nmem (PR + 6)) (c₀.nreg ALLOC) N
  hcan : IsCanonicalNF (chainModel Cα) (Qof E.P) N γ' 4
  hQ : Cα.P = Qof E.P
  hdir : (∀ d, d ≤ Cα.m → E.M.W.vtx ((c₀.nmem PR + d) % E.M.W.n) = Cα.vertex d) ∨
    (∀ d, d ≤ Cα.m → E.M.W.vtx ((c₀.nmem PR + d) % E.M.W.n) = Cα.vertex (Cα.m - d))
  hs : c₀.nmem PR < E.M.W.n
  hmn : Cα.m < E.M.W.n
  hVs : VSet E (c₀.nmem PR)
  h2α : 2 * (2 * Cα.m + 7) ≤ E.W
  hWa : ∀ r, r < N.nRegions → 2 * (2 * Cα.m + 7) + (N.region r).arcs.length ≤ E.W
  hdW : decDepth 4 N.nChords + 1 ≤ E.W

/-- The facts of piece `i` of the list at `L` the loop needs. -/
def PieceGood (E : FEnv) (c₀ : Config) (L Kp i : ℕ) : Prop :=
  prOf L i + 6 < c₀.nreg ALLOC ∧ c₀.nmem (prOf L i) < E.M.W.n ∧ k0K E ≤ Kp ∧
    (c₀.nmem (prOf L i + 4) = 1 → ∃ Hs Cα N γ', K1Hyp E c₀ (prOf L i) Hs Cα N γ' ∧
      k1K E Cα N ≤ Kp)

/-- **What the run of piece `i` tells**, with the success flag `f` (target in `cT`). -/
def PieceDone (E : FEnv) (c₀ cT : Config) (L i f : ℕ) : Prop :=
  (c₀.nmem (prOf L i + 4) = 0 → ∀ reg, NFRegs E.M (Qof E.P) E.N reg →
    (E.N.region E.r).chords ≠ [] → ∀ t, t < 10 →
      VSet E ((c₀.nmem (prOf L i) + t) % E.M.W.n) → ∀ σb, σb ≤ 1 →
        GoodAt E reg ((c₀.nmem (prOf L i) + t) % E.M.W.n) σb → f = 1) ∧
  (c₀.nmem (prOf L i + 4) = 1 → ∃ Hs Cα N γ', K1Hyp E c₀ (prOf L i) Hs Cα N γ' ∧
    ∃ J, (∀ d, d ≤ Cα.m → E.M.W.vtx ((c₀.nmem (prOf L i) + d) % E.M.W.n) =
        WalkEmbed.tourV Cα J d) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
        (v = c₀.nmem (prOf L i) ∨ v = (c₀.nmem (prOf L i) + Cα.m) % E.M.W.n ∨
          (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m ∧
            v = (c₀.nmem (prOf L i) + (2 * Cα.m - WalkEmbed.tpos Cα J)) % E.M.W.n)) →
        VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → f = 1) ∧
      (WalkEmbed.tpos Cα J + Cα.m ≤ 2 * Cα.m →
        SComp E c₀ cT Cα N (c₀.nmem (prOf L i)) (6 + WalkEmbed.tpos Cα J) Cα.m f) ∧
      (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m →
        SComp E c₀ cT Cα N (c₀.nmem (prOf L i)) (6 + WalkEmbed.tpos Cα J)
          (2 * Cα.m - WalkEmbed.tpos Cα J) f ∧
        SComp E c₀ cT Cα N ((c₀.nmem (prOf L i) + (2 * Cα.m - WalkEmbed.tpos Cα J)) %
          E.M.W.n) 6 (Cα.m - (2 * Cα.m - WalkEmbed.tpos Cα J)) f))

theorem SComp.mono {cT : Config} {Cα : Chain} {N : NF} {g g' L f f' : ℕ}
    (h : SComp E c₀ cT Cα N g g' L f) (hf : f = 1 → f' = 1) : SComp E c₀ cT Cα N g g' L f' :=
  fun reg ai bi aj bj dX regα T hD hJ hJr => hf (h reg ai bi aj bj dX regα T hD hJ hJr)

theorem PieceDone.mono {cT : Config} {L i f f' : ℕ} (h : PieceDone E c₀ cT L i f)
    (hf : f = 1 → f' = 1) : PieceDone E c₀ cT L i f' := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun hk reg hr hch t ht hv σb hσb hg => hf (h0 hk reg hr hch t ht hv σb hσb hg),
    fun hk => ?_⟩
  obtain ⟨Hs, Cα, N, γ', hK, J, hV, ht, hs1, hs2⟩ := h1 hk
  exact ⟨Hs, Cα, N, γ', hK, J, hV, fun reg hr hch v hv hvs σb hσb hg =>
    hf (ht reg hr hch v hv hvs σb hσb hg), fun h => (hs1 h).mono hf,
    fun h => ⟨(hs2 h).1.mono hf, (hs2 h).2.mono hf⟩⟩

theorem SComp.congr {cT cT' : Config} {Cα : Chain} {N : NF} {g g' L f : ℕ}
    (h : SComp E c₀ cT Cα N g g' L f) (h40 : cT'.nreg 81140 = cT.nreg 81140)
    (h41 : cT'.nreg 81141 = cT.nreg 81141) : SComp E c₀ cT' Cα N g g' L f := by
  intro reg ai bi aj bj dX regα T hD hJ hJr
  rw [h40, h41] at hJ hJr
  exact h reg ai bi aj bj dX regα T hD hJ hJr

/-- The registers the piece loop writes. -/
def PW (q : ℕ) : Prop := K1W q ∨ (81070 ≤ q ∧ q ≤ 81073) ∨ q = 81077 ∨ q = 81079 ∨ q = 81080

theorem pieceBody_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {L i Kp : ℕ}
    (hL : c.nreg 81076 = L) (hi : c.nreg 81079 = i) (hG : PieceGood E c₀ L Kp i)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + (Kp + 20) ≤ E.W) :
    FRS B E.P E.W c₀ (pieceBody E.sT) c (Kp + 20) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ PW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧ c'.nreg 81079 = i + 1 ∧
      PieceDone E c₀ c L i (c'.nreg 81007)) := by
  obtain ⟨hPR, hs0, hk0, hk1⟩ := hG
  refine FRS.seq (K₁ := 12) (K₂ := Kp + 8) (pbL_fs hE hB hI (by rwx [hL, hi]))
    (fun c₁ hI₁ hA₁ ⟨v80, v77, v70, f₁⟩ => ?_) |>.mono (by omega) (fun _ => id)
  rw [hL, hi] at v80 v77 v70
  have k0₁ := k0_of hE hI₁
  have k1₁ : c₁.nreg 81012 = 1 := by rw [hI₁.hin _ (by ufo FFix), hE.k1]
  have hw₁ : FWin E c₁ := hw.congr' (fun q a b => f₁ q (by omega) (by omega) (by omega) (by omega))
  have e40 : c₁.nreg 81140 = c.nreg 81140 := f₁ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e41 : c₁.nreg 81141 = c.nreg 81141 := f₁ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e79 : c₁.nreg 81079 = i := by
    rw [f₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), hi]
  -- the final counter step
  have fin : ∀ c₂ : Config, FInv E.W c₀ c₂ → FWin E c₂ →
      (∀ q, 81011 ≤ q → q < 83000 → ¬ PW q → q ≠ 81079 → c₂.nreg q = c.nreg q) →
      c₂.nreg 81079 = i → (c.nreg 81007 = 1 → c₂.nreg 81007 = 1) →
      PieceDone E c₀ c L i (c₂.nreg 81007) → c₂.nreg ALLOC + 1 ≤ E.W →
      FRS B E.P E.W c₀ (Stmt.block [.addN 81079 81079 81012]) c₂ 1 (fun c' => FWin E c' ∧
        (∀ q, 81011 ≤ q → q < 83000 → ¬ PW q → c'.nreg q = c.nreg q) ∧
        (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧ c'.nreg 81079 = i + 1 ∧
        PieceDone E c₀ c L i (c'.nreg 81007)) := by
    intro c₂ hI₂ hw₂ f₂ h79 m₂ d₂ _
    have k1₂ : c₂.nreg 81012 = 1 := by rw [hI₂.hin _ (by ufo FFix), hE.k1]
    have hiW : i + 1 ≤ E.W := by
      have := hPR; have := hI.hA; have := hI.hw.1 ALLOC; ufo prOf at *
    have ok : okB E.W c₂.nmem [.addN 81079 81079 81012] c₂.nreg := by
      sin only [okB, okI, FScr, FOut, k1₂, h79]; omega
    refine (FRS.block hB _ hI₂ ok).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.addN 81079 81079 81012] c₂.nreg q := fun q => by
      rw [h']
    have f' : ∀ q, q ≠ 81079 → c'.nreg q = c₂.nreg q := fun q h => by
      rw [e']; simp [regB, regI, upd, h]
    have g07 : c'.nreg 81007 = c₂.nreg 81007 := f' _ (by norm_num)
    exact ⟨hw₂.congr' (fun q a b => f' q (by omega)), fun q a b hq => by
      rw [f' q (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inl h))))),
        f₂ q a b hq (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inl h)))))],
      fun h => by rw [g07]; exact m₂ h, by rw [e']; simp [regB, regI, upd, k1₂, h79],
      by rwx [g07]⟩
  have nPW : ∀ q, ¬ PW q → q ≠ 81070 ∧ q ≠ 81073 ∧ q ≠ 81077 ∧ q ≠ 81080 := fun q hq =>
    ⟨fun h => hq (Or.inr (Or.inl ⟨by omega, by omega⟩)),
      fun h => hq (Or.inr (Or.inl ⟨by omega, by omega⟩)),
      fun h => hq (Or.inr (Or.inr (Or.inl h))), fun h => hq (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
  by_cases a1 : c₁.nreg 81011 < c₁.nreg 81077
  · refine FRS.seq (K₁ := Kp + 6) (K₂ := 1) (Q₁ := fun c₂ => FWin E c₂ ∧
        (∀ q, 81011 ≤ q → q < 83000 → ¬ PW q → q ≠ 81079 → c₂.nreg q = c.nreg q) ∧
        c₂.nreg 81079 = i ∧ (c.nreg 81007 = 1 → c₂.nreg 81007 = 1) ∧
        PieceDone E c₀ c L i (c₂.nreg 81007))
      (FRS.ifT a1 ?_ |>.mono (K := Kp + 6) (by omega)
      (fun _ => id)) (fun c₂ hI₂ hA₂ h₂ => ?_) |>.mono (by omega) (fun _ => id)
    rotate_left
    · exact fin c₂ hI₂ h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2.1 h₂.2.2.2.2 (by omega)
    by_cases a2 : c₁.nreg 81077 = c₁.nreg 81012
    · have hk : c₀.nmem (prOf L i + 4) = 1 := by rw [← v77, a2, k1₁]
      obtain ⟨Hs, Cα, N, γ', hK, hKp⟩ := hk1 hk
      refine (FRS.ifEq_eq a2 (kind1_fs hE hB hBT hI₁ hw₁ (by rw [v80]; exact hK.hPR)
        (by rw [v80]; exact hK.hCD) (by rw [v80]; exact hK.hwf) (by rw [v80]; exact hK.hNW)
        hK.hcan hK.hQ (by rw [v80]; exact hK.hdir) (by rw [v80]; exact hK.hs) hK.hmn
        (by rw [v80]; exact hK.hVs) (by rwx [e40, e41]) hnW hK.h2α hK.hWa hK.hdW
        (by omega))).mono (by omega) (fun c₂ ⟨w₂, f₂, m₂, J, hV, ht, hs1, hs2⟩ => ?_)
      rw [v80] at hV ht hs1 hs2
      refine ⟨w₂, fun q a b hq h79 => by
        rw [f₂ q a b (fun h => hq (Or.inl h)), f₁ q (nPW q hq).1 (nPW q hq).2.1 (nPW q hq).2.2.1
          (nPW q hq).2.2.2],
        by rw [f₂ _ (by norm_num) (by norm_num) (by ufo K1W DescW NodeW LeafW KeyW VertW),
          e79],
        fun h => m₂ (by rwx [f₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]),
        ⟨fun h0 => absurd h0 (by rwn [hk]), fun _ => ⟨Hs, Cα, N, γ', hK, J, hV, ht,
          fun h => (hs1 h).congr (by rw [f₁ _ (by norm_num) (by norm_num) (by norm_num)
            (by norm_num)]) (by rw [f₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]),
          fun h => ⟨(hs2 h).1.congr (by rw [f₁ _ (by norm_num) (by norm_num) (by norm_num)
            (by norm_num)]) (by rw [f₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]),
            (hs2 h).2.congr (by rw [f₁ _ (by norm_num) (by norm_num) (by norm_num)
            (by norm_num)]) (by rw [f₁ _ (by norm_num) (by norm_num) (by norm_num)
            (by norm_num)])⟩⟩⟩⟩
    · refine (FRS.ifEq_ne (K := Kp) hI₁ a2 ⟨hw₁, fun q a b hq _ => f₁ q (nPW q hq).1
        (nPW q hq).2.1 (nPW q hq).2.2.1 (nPW q hq).2.2.2, e79,
        fun h => by rwx [f₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)],
        fun h0 => absurd h0 (by rw [← v77]; rwo [k0₁] at a1), fun h1 => absurd h1 (by
          rw [← v77]; rw [k1₁] at a2; exact a2)⟩).mono (by omega) (fun _ => id)
  · have hk : c₀.nmem (prOf L i + 4) = 0 := by rw [← v77]; rwo [k0₁] at a1
    refine FRS.seq (K₁ := Kp + 2) (K₂ := 1) (FRS.ifF a1 ((kind0_fs hE hB hBT hI₁ hw₁ v70 hs0
      (by omega)).mono hk0 (fun c₂ h => h))) (fun c₂ hI₂ hA₂ ⟨w₂, f₂, m₂, t₂⟩ => ?_) |>.mono
      (by omega) (fun _ => id)
    refine fin c₂ hI₂ w₂ (fun q a b hq h79 => by
      rw [f₂ q a b (fun h => hq (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl h)))))))
        (fun h => hq (Or.inr (Or.inl ⟨by omega, by omega⟩)))
        (fun h => hq (Or.inr (Or.inl ⟨by omega, by omega⟩))),
        f₁ q (nPW q hq).1 (nPW q hq).2.1 (nPW q hq).2.2.1 (nPW q hq).2.2.2])
      (by rw [f₂ _ (by norm_num) (by norm_num) (by ufo VertW) (by norm_num)
        (by norm_num), e79])
      (fun h => m₂ (by rwx [f₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]))
      ⟨fun _ => t₂, fun h1 => absurd h1 (by rwn [hk])⟩ (by omega)


theorem PieceDone.congr {cT cT' : Config} {L i f : ℕ} (h : PieceDone E c₀ cT L i f)
    (h40 : cT'.nreg 81140 = cT.nreg 81140) (h41 : cT'.nreg 81141 = cT.nreg 81141) :
    PieceDone E c₀ cT' L i f := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨h0, fun hk => ?_⟩
  obtain ⟨Hs, Cα, N, γ', hK, J, hV, ht, hs1, hs2⟩ := h1 hk
  exact ⟨Hs, Cα, N, γ', hK, J, hV, ht, fun h => (hs1 h).congr h40 h41,
    fun h => ⟨(hs2 h).1.congr h40 h41, (hs2 h).2.congr h40 h41⟩⟩

/-- **The piece loop** over the pieces `81079 < 81078` of the list at `81076`. -/
def pieceLoop (sT : Stmt) : Stmt := .whileLtN 81079 81078 (pieceBody sT)

/-- The invariant of the piece loop (from its start `c`). -/
def PLI (E : FEnv) (c₀ c : Config) (L q : ℕ) (c' : Config) : Prop :=
  FWin E c' ∧ (∀ r, 81011 ≤ r → r < 83000 → ¬ PW r → c'.nreg r = c.nreg r) ∧
    (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧ c'.nreg 81079 ≤ q ∧
    ∀ i, i < c'.nreg 81079 → PieceDone E c₀ c L i (c'.nreg 81007)

theorem pieceLoop_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {L q Kp : ℕ}
    (hL : c.nreg 81076 = L) (hq : c.nreg 81078 = q) (h0 : c.nreg 81079 = 0)
    (hG : ∀ i, i < q → PieceGood E c₀ L Kp i)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + (Kp + 22) * q ≤ E.W) :
    FRS B E.P E.W c₀ (pieceLoop E.sT) c ((Kp + 22) * q + 2) (fun c' => FWin E c' ∧
      (∀ r, 81011 ≤ r → r < 83000 → ¬ PW r → c'.nreg r = c.nreg r) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∀ i, i < q → PieceDone E c₀ c L i (c'.nreg 81007)) := by
  have hq0 : c.nreg 81078 - c.nreg 81079 = q := by rwr [hq, h0]
  have n78 : ¬ PW 81078 := by ufo PW K1W DescW NodeW LeafW KeyW VertW
  have n76 : ¬ PW 81076 := by ufo PW K1W DescW NodeW LeafW KeyW VertW
  have n40 : ¬ PW 81140 := by ufo PW K1W DescW NodeW LeafW KeyW VertW
  have n41 : ¬ PW 81141 := by ufo PW K1W DescW NodeW LeafW KeyW VertW
  refine (FRS.while (a := 81079) (b := 81078) (body := pieceBody E.sT) (PLI E c₀ c L q)
    (fun d => d.nreg 81078 - d.nreg 81079) (Kp + 20) (fun d _ hlt => by omega)
    (fun d hId hd hlt hroomd => ?_) hI ⟨hw, fun _ _ _ _ => rfl, id, by rwo [h0],
      fun i hi => by rwo [h0] at hi⟩ (by rwo [hq0])).mono (by rw [hq0])
    (fun c' hP => ?_)
  · obtain ⟨dw, df, dm, dle, dd⟩ := hd
    have d78 : d.nreg 81078 = q := by rw [df _ (by norm_num) (by norm_num) n78, hq]
    have d40 := df _ (by norm_num) (by norm_num) n40
    have d41 := df _ (by norm_num) (by norm_num) n41
    rw [d78] at hlt
    refine (pieceBody_fs hE hB hBT hId dw (by rw [df _ (by norm_num) (by norm_num) n76, hL]) rfl
      (hG _ hlt) (by rwx [d40, d41]) hnW hroomd).mono le_rfl
      (fun c' ⟨w', f', m', h79, pd⟩ => ?_)
    have c78 : c'.nreg 81078 = q := by rw [f' _ (by norm_num) (by norm_num) n78, d78]
    refine ⟨⟨w', fun r a b hr => (f' r a b hr).trans (df r a b hr), fun h => m' (dm h),
      by omega, fun i hi => ?_⟩, by omega⟩
    rcases Nat.lt_or_ge i (d.nreg 81079) with h | h
    · exact (dd i h).mono m'
    · rw [show i = d.nreg 81079 by omega]
      exact pd.congr d40.symm d41.symm
  · obtain ⟨hP1, hex⟩ := hP
    obtain ⟨cw, cf, cm, cle, cd⟩ := hP1
    have c78 : c'.nreg 81078 = q := by rw [cf _ (by norm_num) (by norm_num) n78, hq]
    exact ⟨cw, cf, cm, fun i hi => cd i (by omega)⟩

end

end Restore

end Chazelle.Core
