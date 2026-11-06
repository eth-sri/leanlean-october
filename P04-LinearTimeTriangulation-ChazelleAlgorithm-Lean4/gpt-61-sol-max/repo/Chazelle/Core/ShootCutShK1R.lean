module

public import Chazelle.Core.ShootCutShK1

/-!
# WP-G, part 52: shooting at a kind-1 piece (`pieceK1`)

With a query origin (`140237 = 1`, origin in `140238 …`): the Lemma 3.6 query of the piece's
structure (the third word of its grade-table entry `140255`), then the candidate from its answer
(`k1OutR`, abscissa record `onEdge e' h`) merged into the best answer.  Without one
(`140237 = 0`), the piece has no hit and nothing is done.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

@[expose] public section

/-- The query inputs. -/
def qSet : Stmt :=
  block [.addN 140350 140255 K1, .addN 140350 140350 K1, .loadN 120000 140350,
    .copyN 120001 140238, .copyN 120002 140239, .copyN 120003 140240, .copyN 120004 140008]

/-- The candidate of a hit. -/
def qHit : Stmt :=
  .seq k1OutR (block [.constN 140220 1, .constN 140221 1, .constN 140222 1, .copyN 140223 120006,
    .copyN 140224 140236])

/-- **A kind-1 piece.** -/
def pieceK1 (query : Stmt) : Stmt :=
  .ifLtN 140237 K1 .skip
    (.seq qSet (.seq query (.seq (.ifLtN 120005 K1 cand0 (.ifLtN K1 120005 cand0 qHit)) mrg)))

theorem qOriginIn_of_eq {c c' : Config} {r : ℕ} {o : QOrigin} (h : QOriginIn c r o)
    (he : ∀ j, r ≤ j → j < r + 3 → c'.nreg j = c.nreg j) : QOriginIn c' r o := by
  cases o with
  | sym s => exact symPtIn_of_eq h he
  | box h' =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨by rw [he r le_rfl (by omega), h1], by rw [he (r + 1) (by omega) (by omega), h2]⟩

theorem qOriginIn_copy {c c' : Config} {r r' : ℕ} {o : QOrigin} (h : QOriginIn c r o)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) : QOriginIn c' r' o := by
  cases o with
  | sym s => exact NFLoc.symPtIn_copy h h0 h1 h2
  | box h' =>
    obtain ⟨a, b⟩ := h
    exact ⟨by rw [h0, a], by rw [h1, b]⟩

/-- The band-`14` registers written by `pieceK1`. -/
def Wk1 (r : ℕ) : Bool :=
  decide (140210 ≤ r ∧ r < 140227) || r == 140310 || decide (140350 ≤ r ∧ r < 140355)

theorem oracleBands_mem (r : ℕ) (h : bandOf r = 1 ∨ bandOf r = 3 ∨ bandOf r = 4 ∨ bandOf r = 5 ∨
    bandOf r = 6 ∨ bandOf r = 12 ∨ bandOf r = 13 ∨ bandOf r = 14 ∨ bandOf r = 15) :
    bandOf r ∈ oracleBands := by
  simp only [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot,
    bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

theorem wr_qSet : wr (fun r => r == 140350 || decide (120000 ≤ r ∧ r < 120005)) qSet = true := by
  decide

theorem qSet_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {en : ℕ}
    (h55 : c.nreg 140255 = en) (hW : en + 2 ≤ W) :
    ∃ c' k, Exec P W qSet c c' k ∧ k = 7 ∧ c'.nreg 120000 = c.nmem (en + 2) ∧
      c'.nreg 120001 = c.nreg 140238 ∧ c'.nreg 120002 = c.nreg 140239 ∧
      c'.nreg 120003 = c.nreg 140240 ∧ c'.nreg 120004 = c.nreg 140008 ∧
      FrameB (fun r => r == 140350 || decide (120000 ≤ r ∧ r < 120005)) c c' := by
  have h1' : c.nreg 140401 = 1 := h1
  obtain ⟨c', k, ex, hk, v0, v1, v2, v3, v4⟩ : ∃ c' k, Exec P W qSet c c' k ∧ k = 7 ∧
      c'.nreg 120000 = c.nmem (en + 2) ∧ c'.nreg 120001 = c.nreg 140238 ∧
      c'.nreg 120002 = c.nreg 140239 ∧ c'.nreg 120003 = c.nreg 140240 ∧
      c'.nreg 120004 = c.nreg 140008 := by
    unfold qSet
    simp only [K1]
    exec_block
    all_goals first | omega | (config_simp; rw [h55, h1']; omega) | skip
    refine ⟨rfl, ?_, by config_simp, by config_simp, by config_simp, by config_simp⟩
    config_simp; rw [h55, h1']
  exact ⟨c', k, ex, hk, v0, v1, v2, v3, v4, exec_frameB ex wr_qSet⟩

/-- The registers written by `qHit`. -/
def Bqh (r : ℕ) : Bool := Bko r || decide (140220 ≤ r ∧ r < 140225)

theorem wr_qHit : wr Bqh qHit = true := by decide

theorem qHit_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1)
    {p₀ x0 w dir e' h : ℕ} (h50 : c.nreg 140250 = p₀) (h56 : c.nreg 140256 = x0)
    (h57 : c.nreg 140257 = dir) (h58 : c.nreg 140258 = w) (h06 : c.nreg 120006 = e')
    (h36 : c.nreg 140236 = h) (hdir : dir = 1 ∨ dir = 0) (hW1 : p₀ + w + 1 ≤ W)
    (hW2 : x0 + w ≤ W) (hW3 : e' + 1 ≤ W) (hW4 : h + 1 ≤ W) {S : Set Point} {X : Point}
    (he' : e' < P.n) (hh : h < P.n) (hF : FirstHit S z σ (σ * (X.1 - z.1))) (hXz : X.2 = z.2)
    (hout : (k1Out p₀ x0 w dir e' h).edge < 2 * C.m + 7 ∧
      ProperPos (chainModel C) (Qof P) P.n (k1Out p₀ x0 w dir e' h) ∧
      (chainModel C).pos (Qof P) (k1Out p₀ x0 w dir e' h) = X ∧
      X.1 = ((SymPt.onEdge e' h).eval (Qof P)).1 ∧ |X.1| < C.radius) :
    ∃ c' k, Exec P W qHit c c' k ∧ k ≤ 40 ∧ CandAt P C c' 140220 S z σ ∧ FrameB Bqh c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, v25, v26, f₁⟩ := k1OutR_exec (P := P) c hw h1 h50 h56 h57 h58 h06 h36
    hdir hW1 hW2 hW3 hW4
  have k₁' : ∀ r, Bko r = false → c₁.nreg r = c.nreg r := f₁.1
  have q06 : c₁.nreg 120006 = e' := by rw [k₁' _ (by decide), h06]
  have q36 : c₁.nreg 140236 = h := by rw [k₁' _ (by decide), h36]
  obtain ⟨c₂, k₂, e₂, hk₂, v20, v21, v22, v23, v24, g₂⟩ : ∃ c₂ k₂, Exec P W (block
      [.constN 140220 1, .constN 140221 1, .constN 140222 1, .copyN 140223 120006,
        .copyN 140224 140236]) c₁ c₂ k₂ ∧ k₂ = 5 ∧ c₂.nreg 140220 = 1 ∧ c₂.nreg 140221 = 1 ∧
      c₂.nreg 140222 = 1 ∧ c₂.nreg 140223 = e' ∧ c₂.nreg 140224 = h ∧
      ∀ r, (r < 140220 ∨ 140225 ≤ r) → c₂.nreg r = c₁.nreg r := by
    have w₁ := e₁.wb_right
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp; exact q06,
      by config_simp; exact q36, fun r hr => ?_⟩
    simp only [upd]; split_ifs <;> first | rfl | omega
  have ex : Exec P W qHit c c₂ (k₁ + k₂) := .seq e₁ e₂
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := hout
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  refine ⟨c₂, _, ex, by omega, ⟨by rw [v20], fun h' => absurd v20 h', fun _ => ⟨X.1, ⟨C.radius_pos,
    Or.inr (Or.inr ⟨v21, ho5, .onEdge e' h, ⟨v22, v23, v24⟩, ⟨he', hh⟩, ho4.symm⟩)⟩, hF,
    by rw [g₂ _ (by omega), g₂ _ (by omega), v25, v26]; exact ho2,
    by rw [g₂ _ (by omega), v25, hnW]; exact ho1,
    by rw [g₂ _ (by omega), g₂ _ (by omega), v25, v26, ho3]; ext <;> simp [hXz]⟩⟩,
    exec_frameB ex wr_qHit⟩

/-- A frame of a statement writing only registers of `B` and bands of `oracleBands`. -/
theorem frame_ob {B : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → (bandOf r = 1 ∨ bandOf r = 5 ∨ bandOf r = 12 ∨ bandOf r = 14) ∧
      r ≠ ALLOC) (k : ℕ) : Frame oracleBands c c' k :=
  frame_of_frameB h (fun r hr => ⟨oracleBands_mem r (by have := (hB r hr).1; omega),
    (hB r hr).2⟩) k

theorem pieceK1_exec {O : OracleIface} (hV : O.Valid) (c : Config) (hw : WordsBounded W c)
    (E : ShEnv P W H C z σ c) (h08 : dirOf (c.nreg 140008) = σ) {S₀ : Set Point}
    (hB : CandAt P C c 140210 S₀ z σ) {p₀ en x0 w dir : ℕ} (h50 : c.nreg 140250 = p₀)
    (h55 : c.nreg 140255 = en) (h56 : c.nreg 140256 = x0) (h57 : c.nreg 140257 = dir)
    (h58 : c.nreg 140258 = w) (hblk : BlockWalk (chainModel C).W (Qof P) p₀ x0 w dir)
    (hw1 : 1 ≤ w) (hxw : x0 + w < P.n) (hp6 : 6 ≤ p₀) (hp : p₀ + w ≤ 2 * C.m + 6)
    (hdir : dir = 1 ∨ dir = 0)
    (hAt : O.At P c.nmem (c.nmem (en + 2)))
    (hCα : ∃ Hs Cα, ChainDescAt c.nmem (c.nmem (c.nmem (en + 2))) (Qof P) Hs Cα ∧
      Cα.set = (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ))
    (hqk : c.nreg 140237 ≤ 1)
    (hq0 : c.nreg 140237 = 0 → NoHit ((chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) z σ)
    (hq1 : c.nreg 140237 = 1 → c.nreg 140234 = 1 ∧
      ∃ o, QOriginIn c 140238 o ∧ o.Lt P.n ∧ QRel P C σ z o)
    (hQs : (Qof P).Simple) {Kq : ℕ}
    (hcost : ⌈(O.κ : ℝ) * ((c.nmem (c.nmem (en + 2) + 2) : ℝ) ^ ((1 : ℝ) / 3) *
      ((c.nmem (c.nmem (c.nmem (en + 2)) + 2) : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)⌉₊ ≤ Kq)
    (hroom : c.nreg ALLOC + Kq + 400 ≤ W) (hWen : en + 2 ≤ W) (hW1 : p₀ + w + 1 ≤ W)
    (hW2 : x0 + w ≤ W) :
    ∃ c' k, Exec P W (pieceK1 O.query) c c' k ∧ k ≤ Kq + 400 ∧
      CandAt P C c' 140210 (S₀ ∪ (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) z σ ∧
      Frame oracleBands c c' k ∧
      (∀ r, 140000 ≤ r → r < 160000 → Wk1 r = false → c'.nreg r = c.nreg r) ∧
      ShEnv P W H C z σ c' := by
  set S := (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ) with hSdef
  have hW' : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hD := distinct_Qof E.hG
  have k1 := E.k1
  unfold pieceK1
  by_cases t0 : c.nreg 140237 < c.nreg K1
  · -- no query: no hit
    have hN := hq0 (by rw [k1] at t0; omega)
    obtain ⟨x₁, c₁', r₁⟩ := hB.cand
    have hu := cand_union E.hσ c₁' (show Cand S z σ 0 0 from ⟨fun h => absurd h (by norm_num),
      fun _ => hN⟩)
    simp only [zero_ne_one, false_and, ↓reduceIte] at hu
    exact ⟨c, _, .ifLtN_true t0 (.skip hw), by omega, CandAt.of_cand hB.1 hu r₁,
      frame_of_frameB (FrameB.refl (fun _ => false) c) (fun r h => by simp at h) _,
      fun _ _ _ _ => rfl, E⟩
  have hq : c.nreg 140237 = 1 := by rw [k1] at t0; omega
  obtain ⟨hyk, o, hoIn, hoLt, hrel⟩ := hq1 hq
  -- the origin is at the height of a vertex of `Q`
  obtain ⟨-, hzR, -, hhi, hzh⟩ : c.nreg 140234 = 1 ∧ |z.2| < C.radius ∧
      c.nreg (140234 + 1) = 0 ∧ c.nreg (140234 + 2) < P.n ∧
      z.2 = ((Qof P).vtx (c.nreg (140234 + 2))).2 := by
    rcases E.oy with ⟨h', _⟩ | ⟨h', _⟩ | h' <;> [omega; omega; exact h']
  set h := c.nreg (140234 + 2) with hhdef
  -- the query inputs
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, v3, v4, f₁⟩ := qSet_exec (P := P) c hw k1 h55 hWen
  have kq₁ : ∀ r, r ≠ 140350 → ¬ (120000 ≤ r ∧ r < 120005) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 => f₁.1 r (by simp [h1]; omega)
  have hm₁ : c₁.nmem = c.nmem := f₁.2.2.1
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := kq₁ _ (by decide) (by simp [ALLOC])
  have hoIn₁ : QOriginIn c₁ (bandReg bOQuery 1) o := qOriginIn_copy hoIn v1 v2 v3
  have hq0' : rd c₁ bOQuery 0 = c.nmem (en + 2) := v0
  -- the query
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, F₂⟩ := hV.2.2 P W c₁ e₁.wb_right
    ⟨E.hG, E.hW, by rw [hm₁, hq0']; exact hAt, o, hoLt, hoIn₁⟩ (by
      dsimp only
      rw [hA₁]
      have : ⌈(O.κ : ℝ) * ((c₁.nmem (rd c₁ bOQuery 0 + 2) : ℝ) ^ ((1 : ℝ) / 3) *
          ((c₁.nmem (c₁.nmem (rd c₁ bOQuery 0) + 2) : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)⌉₊ ≤ Kq := by
        rw [hm₁, hq0']; exact hcost
      omega)
  replace hk₂ : k₂ ≤ Kq := by
    refine le_trans hk₂ ?_
    show ⌈(O.κ : ℝ) * ((c₁.nmem (rd c₁ bOQuery 0 + 2) : ℝ) ^ ((1 : ℝ) / 3) *
      ((c₁.nmem (c₁.nmem (rd c₁ bOQuery 0) + 2) : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)⌉₊ ≤ Kq
    rw [hm₁, hq0']; exact hcost
  obtain ⟨Hs, Cα, hCd, hCs⟩ := hCα
  have hpost := post₂ Hs Cα o (by rw [hm₁, hq0']; exact hCd) hoIn₁
  have hdir₁ : dirOf (rd c₁ bOQuery 4) = σ := by show dirOf (c₁.nreg 120004) = σ; rw [v4, h08]
  rw [hdir₁] at hpost
  -- the frame of the query
  obtain ⟨Fr, Frr, Fm, Frm, Fo, Fa1, Fa2⟩ := F₂
  have kq₂ : ∀ r, bandOf r ∉ kernelBands ∪ {bOQuery} → r ≠ ALLOC → c₂.nreg r = c₁.nreg r := Fr
  have band14 : ∀ r, 140000 ≤ r → r < 160000 → bandOf r ∉ kernelBands ∪ {bOQuery} := fun r h1 h2 => by
    simp only [kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bandOf,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have k₂' : ∀ r, 140000 ≤ r → r < 160000 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    kq₂ r (band14 r h1 h2) (by unfold ALLOC; omega)
  have hE₂ : ShEnv P W H C z σ c₂ := by
    refine ShEnv.of_agree E (fun r hr hra => ?_) (fun a ha => ?_) (by rw [← hA₁]; exact Fa1)
    · have h14 : 140000 ≤ r ∧ r < 160000 := by unfold envR K1 ALLOC at hr; unfold ALLOC at hra; omega
      rw [k₂' r h14.1 h14.2, kq₁ r (by unfold envR K1 ALLOC at hr; omega) (by omega)]
    · rw [Fm a (by rw [hA₁]; exact ha), hm₁]
  have hSC : ∀ x ∈ S, InC C x := fun x hx => block_inC hw1 hp6 hp hx
  have htr := query_transfer (S := S) (z := z) E.hσ hrel (by rw [hCs]) hSC
  rw [hCs] at hpost
  have w₂ := e₂.wb_right
  have k1₂ : c₂.nreg K1 = 1 := hE₂.k1
  -- the candidate
  have wr_c0 : wr (fun r => Bqh r || r == 140220) cand0 = true := by decide
  have r50 : c₂.nreg 140250 = p₀ := by
    rw [k₂' _ (by norm_num) (by norm_num), kq₁ _ (by decide) (by omega), h50]
  have r56 : c₂.nreg 140256 = x0 := by
    rw [k₂' _ (by norm_num) (by norm_num), kq₁ _ (by decide) (by omega), h56]
  have r57 : c₂.nreg 140257 = dir := by
    rw [k₂' _ (by norm_num) (by norm_num), kq₁ _ (by decide) (by omega), h57]
  have r58 : c₂.nreg 140258 = w := by
    rw [k₂' _ (by norm_num) (by norm_num), kq₁ _ (by decide) (by omega), h58]
  have r36 : c₂.nreg 140236 = h := by
    rw [k₂' _ (by norm_num) (by norm_num), kq₁ _ (by decide) (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, ca, fc⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 120005 K1 cand0
      (.ifLtN K1 120005 cand0 qHit)) c₂ c₃ k₃ ∧ k₃ ≤ 50 ∧ CandAt P C c₃ 140220 S z σ ∧
      FrameB (fun r => Bqh r || r == 140220) c₂ c₃ := by
    by_cases t1 : c₂.nreg 120005 < c₂.nreg K1
    · have hN := htr.2 (hpost.2 (by rw [k1₂] at t1; show c₂.nreg 120005 ≠ 1; omega))
      obtain ⟨c₃, k, ex, hk, ca, -⟩ := cand0_exec (P := P) (C := C) c₂ w₂ hN
      exact ⟨c₃, _, .ifLtN_true t1 ex, by omega, ca, exec_frameB ex wr_c0⟩
    by_cases t2 : c₂.nreg K1 < c₂.nreg 120005
    · have hN := htr.2 (hpost.2 (by rw [k1₂] at t2; show c₂.nreg 120005 ≠ 1; omega))
      obtain ⟨c₃, k, ex, hk, ca, -⟩ := cand0_exec (P := P) (C := C) c₂ w₂ hN
      exact ⟨c₃, _, .ifLtN_false t1 (.ifLtN_true t2 ex), by omega, ca, exec_frameB ex wr_c0⟩
    have hf : c₂.nreg 120005 = 1 := by rw [k1₂] at t1 t2; omega
    obtain ⟨t', hF', he'n, hXe⟩ := hpost.1 hf
    obtain ⟨hFz, hXz⟩ := htr.1 t' hF'
    set X := rayPt (o.eval (Qof P) Cα σ) σ t' with hX
    have hXS : X ∈ S := by rw [← hXz]; exact hFz.2.1
    have hXy : X.2 = z.2 := by rw [← hXz, rayPt_snd]
    set e' := rd c₂ bOQuery 6 with he'def
    have hout := k1_hit (C := C) hD hQs hblk hw1 (by rw [hQn]; exact hxw) hp6 hp hdir hXS hXe
      (by rw [hQn]; exact he'n) (by rw [hQn]; exact hhi) (by rw [hXy, hzh])
    rw [hQn] at hout
    obtain ⟨c₃, k, ex, hk, ca, f⟩ := qHit_exec (P := P) (C := C) (S := S) (X := X) c₂ w₂ k1₂ r50 r56
      r57 r58 rfl r36 hdir (by omega) hW2
      (by have : rd c₂ bOQuery 6 = c₂.nreg 120006 := rfl; omega) (by omega) he'n hhi hFz hXy hout
    exact ⟨c₃, _, .ifLtN_false t1 (.ifLtN_false t2 ex), by omega, ca,
      FrameB.wk f (fun r h => by simp [h])⟩
  have w₃ := e₃.wb_right
  have hE₃ : ShEnv P W H C z σ c₃ := hE₂.frame fc fun r hr => by
    unfold envR at hr
    simp only [Bqh, Bko, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr ⊢
    omega
  have hB₃ : CandAt P C c₃ 140210 S₀ z σ := hB.keep fun j hj => by
    rw [fc.1 _ (by simp [Bqh, Bko]; omega), k₂' _ (by omega) (by omega),
      kq₁ _ (by omega) (by omega)]
  obtain ⟨c₄, k₄, e₄, hk₄, cb, fm⟩ := mrg_exec c₃ w₃ hE₃ hB₃ ca
  have hE₄ := hE₃.frame fm Bmrg_env
  refine ⟨c₄, _, .ifLtN_false t0 (.seq e₁ (.seq e₂ (.seq e₃ e₄))), by omega, cb, ?_, ?_, hE₄⟩
  · -- the frame
    have F1 : Frame oracleBands c c₁ k₁ := frame_ob f₁ (fun r hr => by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      unfold bandOf ALLOC; omega) k₁
    have F2 : Frame oracleBands c₁ c₂ k₂ :=
      Frame.mono ⟨Fr, Frr, Fm, Frm, Fo, Fa1, Fa2⟩ (by
        intro b hb
        simp only [oracleBands, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hb ⊢
        rcases hb with hb | hb
        · exact Or.inl hb
        · exact Or.inr (Or.inl hb)) le_rfl
    have F3 : Frame oracleBands c₂ c₃ k₃ := frame_ob fc (fun r hr => by
      simp only [Bqh, Bko, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      unfold bandOf ALLOC; omega) k₃
    have F4 : Frame oracleBands c₃ c₄ k₄ := frame_ob fm (fun r hr => by
      simp only [Bmrg, Bk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      unfold bandOf ALLOC; omega) k₄
    have := ((F1.trans F2).trans F3).trans F4
    simp only [Finset.union_self] at this
    exact this.mono le_rfl (by omega)
  · intro r h1 h2 hr
    simp only [Wk1, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hr
    rw [fm.1 r (by simp [Bmrg, Bk]; omega), fc.1 r (by simp [Bqh, Bko]; omega),
      k₂' r h1 h2, kq₁ r (by omega) (by omega)]

end

end ShootCut

end Chazelle.Core
