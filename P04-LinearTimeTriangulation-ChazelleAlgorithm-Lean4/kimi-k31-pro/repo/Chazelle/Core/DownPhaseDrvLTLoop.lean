module

public import Chazelle.Core.DownPhaseDrvLTGat
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# Down-phase level tail (D12), part 4: the gather loop

`GEnv`: the fixed data of the gather (the start allocator `A₀`, memory `m₀` and registers `r₀`,
the table `T`, the lower bound `B` of the kept lists, the number `R` of regions, the bound `Mx` of
the kept lengths, the kept lists `Lx`); `GGood` its facts (the table entries `RegMem`);
`LInv G j e`: the state after `j` regions (`L₂`'s first `j` lists at `A₀`, their buckets at
`A₀ + 3 K₂`).  `body_step`, **`loop_exec`**.
-/

namespace Chazelle.Core

namespace DrvLT

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

/-- **The fixed data of the gather.** -/
structure GEnv where
  P : Polygon
  W : ℕ
  A₀ : ℕ
  m₀ : ℕ → ℕ
  r₀ : ℕ → ℕ
  T : ℕ
  B : ℕ
  R : ℕ
  Mx : ℕ
  Q : Polygon
  N : NF
  Lx : ℕ → List (ℕ × ℕ × ℕ)

namespace GEnv

variable (G : GEnv)

/-- The first `j` kept lists. -/
def flat (j : ℕ) : List (ℕ × ℕ × ℕ) := (List.range j).flatMap G.Lx

/-- The total kept length. -/
def K₂ : ℕ := (G.flat G.R).length

end GEnv

/-- **The facts of the gather's data.** -/
structure GGood (G : GEnv) : Prop where
  hTB : G.T + 3 * G.R ≤ G.B
  hBA : G.B ≤ G.A₀
  hmem : ∀ r, r < G.R → DrvR.RegMem G.m₀ G.A₀ G.T G.B G.Q G.N r (G.Lx r)
  hMx : ∀ r, r < G.R → (G.Lx r).length ≤ G.Mx
  room : G.A₀ + 5 * G.K₂ + 1 ≤ G.W

/-- **The state after `j` regions.** -/
structure LInv (G : GEnv) (j : ℕ) (e : Config) : Prop where
  wb : WordsBounded G.W e
  r30 : e.nreg 211130 = j
  r11 : e.nreg 211011 = G.R
  r31 : e.nreg 211131 = G.T + 3 * j
  r00 : e.nreg 211100 = 1
  r01 : e.nreg 211101 = 3
  r34 : e.nreg 210034 = 1
  r10 : e.nreg 211110 = G.A₀
  r12 : e.nreg 211112 = G.A₀ + 3 * G.K₂
  r13 : e.nreg 211113 = G.A₀ + 3 * (G.flat j).length
  r14 : e.nreg 211114 = G.A₀ + 3 * G.K₂ + 2 * (G.flat j).length
  alloc : e.nreg ALLOC = G.A₀ + 5 * G.K₂
  keep : ∀ r, BL r = false → r ≠ ALLOC → e.nreg r = G.r₀ r
  low : ∀ a, a < G.A₀ → e.nmem a = G.m₀ a
  list : ChordListAt e.nmem G.A₀ (G.flat j)
  bkt : ∀ q, q < 2 * (G.flat j).length →
    e.nmem (G.A₀ + 3 * G.K₂ + q) = DrvR.keyBkt G.Q G.N (DrvR.endPos (G.flat j) q)
  jle : j ≤ G.R

theorem seg_pt {m m' : ℕ → ℕ} {a b n q : ℕ} (h : seg m' a n = seg m b n) (hq : q < n) :
    m' (a + q) = m (b + q) := by
  have := congrArg (fun l => l.getD q 0) h
  simp only [SortL.seg_getD _ hq] at this
  exact this

theorem B1_BL : ∀ r, B1 r = true → BL r = true := by
  intro r h; sio only [B1, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢

theorem B2_BL : ∀ r, B2 r = true → BL r = true := by
  intro r h; sio only [B2, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢

theorem B3_BL : ∀ r, B3 r = true → BL r = true := by
  intro r h; sio only [B3, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢

theorem Bcp_BL : ∀ r, DrvR.Bcp r = true → BL r = true := by
  intro r h; sio only [DrvR.Bcp, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢

/-- **One region of the gather.** -/
theorem body_step {G : GEnv} (hG : GGood G) {j : ℕ} {e : Config} (hI : LInv G j e)
    (hj : j < G.R) :
    ∃ e' k, Exec G.P G.W ltBody e e' k ∧ LInv G (j + 1) e' ∧
      Restore.RF DrvR.drvBands G.A₀ e e' k ∧ k ≤ 35 * G.Mx + 30 := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG.hmem j hj
  have hTB := hG.hTB
  have hBA := hG.hBA
  have hroom := hG.room
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (G.Lx j).length = ℓ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, (G.flat j).length = F := ⟨_, rfl⟩
  rw [hℓ] at g1 g3 g6
  have hF1 : (G.flat (j + 1)).length = F + ℓ := by
    show ((List.range (j + 1)).flatMap G.Lx).length = _
    rwr [flat_succ, List.length_append, ← hℓ, ← hF]
  have hFK : F + ℓ ≤ G.K₂ := by
    rw [← hF1]; exact flat_length_mono G.Lx (by omega)
  have hℓM : ℓ ≤ G.Mx := hℓ ▸ hG.hMx j hj
  have r13 := hI.r13
  have r14 := hI.r14
  rw [hF] at r13 r14
  -- the table entry
  have t0 : e.nmem (G.T + 3 * j) = G.m₀ (G.T + 3 * j) := hI.low _ (by omega)
  have t1 : e.nmem (G.T + 3 * j + 1) = ℓ := by rwx [hI.low _ (by omega)]
  have t2 : e.nmem (G.T + 3 * j + 1 + 1) = G.m₀ (G.T + 3 * j + 2) := hI.low _ (by omega)
  -- 1. the entry
  obtain ⟨e₁, k₁, x₁, hk₁, a40, a43, a44, a45, a61, a62, a63, m₁, f₁⟩ :=
    ltB1_exec (P := G.P) e hI.wb hI.r31 hI.r00 r13 (by omega) (by rwo [t1])
  rw [t0] at a40 a62
  rw [t1] at a44 a45 a61
  rw [t2] at a43
  have w₁ := x₁.wb_right
  have k₁r : ∀ r, B1 r = false → e₁.nreg r = e.nreg r := f₁.1
  -- 2. the triples
  obtain ⟨e₂, k₂, x₂, hk₂, w₂, sg₂, mo₂, f₂⟩ := DrvR.cpS_exec (P := G.P) (W := G.W) w₁
    (S := G.m₀ (G.T + 3 * j)) (D := G.A₀ + 3 * F) a61 a62 a63
    (by rw [k₁r _ (by decide)]; exact hI.r34) (Or.inl (by omega)) (by omega) (by omega)
  have k₂r : ∀ r, DrvR.Bcp r = false → e₂.nreg r = e₁.nreg r := f₂.1
  -- 3. the bucket arguments
  obtain ⟨e₃, k₃, x₃, hk₃, a13, b61, b62, b63, m₃, f₃⟩ := ltB2_exec (P := G.P) e₂ w₂
    (a := G.A₀ + 3 * F) (ℓ := ℓ) (b := G.m₀ (G.T + 3 * j + 2))
    (D₂ := G.A₀ + 3 * G.K₂ + 2 * F)
    (by rw [k₂r _ (by decide), k₁r _ (by decide), r13])
    (by rw [k₂r _ (by decide), a44]) (by rw [k₂r _ (by decide), a45])
    (by rw [k₂r _ (by decide), a43])
    (by rw [k₂r _ (by decide), k₁r _ (by decide), r14]) (by omega)
  have w₃ := x₃.wb_right
  have k₃r : ∀ r, B2 r = false → e₃.nreg r = e₂.nreg r := f₃.1
  -- 4. the buckets
  obtain ⟨e₄, k₄, x₄, hk₄, w₄, sg₄, mo₄, f₄⟩ := DrvR.cpS_exec (P := G.P) (W := G.W) w₃
    (S := G.m₀ (G.T + 3 * j + 2)) (D := G.A₀ + 3 * G.K₂ + 2 * F) b61 b62 b63
    (by rw [k₃r _ (by decide), k₂r _ (by decide), k₁r _ (by decide)]; exact hI.r34)
    (Or.inl (by omega)) (by omega) (by omega)
  have k₄r : ∀ r, DrvR.Bcp r = false → e₄.nreg r = e₃.nreg r := f₄.1
  -- 5. the pointers
  have r4 : ∀ r, B1 r = false → DrvR.Bcp r = false → B2 r = false →
      e₄.nreg r = e.nreg r := fun r h1 h2 h3 => by
    rw [k₄r r h2, k₃r r h3, k₂r r h2, k₁r r h1]
  obtain ⟨e₅, k₅, x₅, hk₅, c14, c31, c30, m₅, f₅⟩ := ltB3_exec (P := G.P) e₄ w₄
    (D₂ := G.A₀ + 3 * G.K₂ + 2 * F) (ℓ := ℓ) (p := G.T + 3 * j) (j := j)
    (by rw [r4 _ (by decide) (by decide) (by decide), r14])
    (by rw [k₄r _ (by decide), k₃r _ (by decide), k₂r _ (by decide), a45])
    (by rw [r4 _ (by decide) (by decide) (by decide), hI.r31])
    (by rw [r4 _ (by decide) (by decide) (by decide), hI.r01])
    (by rw [r4 _ (by decide) (by decide) (by decide), hI.r30])
    (by rw [r4 _ (by decide) (by decide) (by decide), hI.r00]) (by omega) (by omega)
    (by omega)
  have k₅r : ∀ r, B3 r = false → e₅.nreg r = e₄.nreg r := f₅.1
  -- the memory
  have mem5 : ∀ a, e₅.nmem a = if G.A₀ + 3 * G.K₂ + 2 * F ≤ a ∧
      a < G.A₀ + 3 * G.K₂ + 2 * F + 2 * ℓ then e₄.nmem a
      else if G.A₀ + 3 * F ≤ a ∧ a < G.A₀ + 3 * F + 3 * ℓ then e₂.nmem a else e.nmem a := by
    intro a
    rw [m₅]
    split_ifs with h1 h2
    · rfl
    · rw [mo₄ a (by omega), m₃]
    · rw [mo₄ a (by omega), m₃, mo₂ a (by omega), m₁]
  have low5 : ∀ a, a < G.A₀ → e₅.nmem a = e.nmem a := fun a ha => by
    rw [mem5 a, ite_eq_right (by omega), ite_eq_right (by omega)]
  -- the frame
  have fr : FrameM BL e e₅ :=
    ((((BL_mono B1_BL (BuildRam.FrameB.toM f₁)).trans (BL_mono Bcp_BL f₂)).trans
      (BL_mono B2_BL (BuildRam.FrameB.toM f₃))).trans
      (BL_mono Bcp_BL f₄)).trans (BL_mono B3_BL (BuildRam.FrameB.toM f₅))
  have r5 : ∀ r, BL r = false → e₅.nreg r = e.nreg r := fr.1
  have r5' : ∀ r, B1 r = false → DrvR.Bcp r = false → B2 r = false → B3 r = false →
      e₅.nreg r = e.nreg r := fun r h1 h2 h3 h4 => by rw [k₅r r h4, r4 r h1 h2 h3]
  refine ⟨e₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), Exec.seq x₁ (Exec.seq x₂ (Exec.seq x₃
    (Exec.seq x₄ x₅))), ?_, DrvD.rf_of_frameM inDrv_BL fr low5, by omega⟩
  refine ⟨x₅.wb_right, by rw [c30], by rw [r5 _ (by decide), hI.r11], by rwo [c31],
    by rw [r5' _ (by decide) (by decide) (by decide) (by decide), hI.r00],
    by rw [r5' _ (by decide) (by decide) (by decide) (by decide), hI.r01],
    by rw [r5' _ (by decide) (by decide) (by decide) (by decide), hI.r34],
    by rw [r5' _ (by decide) (by decide) (by decide) (by decide), hI.r10],
    by rw [r5' _ (by decide) (by decide) (by decide) (by decide), hI.r12], ?_, by rwo [c14, hF1],
    by rw [r5 _ (by decide), hI.alloc],
    fun r hr hra => by rw [r5 r hr, hI.keep r hr hra], fun a ha => by rw [low5 a ha, hI.low a ha],
    ?_, ?_, by omega⟩
  · -- the triple pointer
    have : e₅.nreg 211113 = e₄.nreg 211113 := k₅r _ (by decide)
    rwring [this, k₄r _ (by decide), a13, hF1]
  · -- the triples
    show ChordListAt e₅.nmem G.A₀ ((List.range (j + 1)).flatMap G.Lx)
    rw [flat_succ]
    refine DrvR.chordListAt_append ?_ ?_
    · refine DrvR.clAt_congr hI.list fun x hx1 hx2 => ?_
      have hF' : ((List.range j).flatMap G.Lx).length = F := hF
      rw [mem5 x, ite_eq_right (by omega), ite_eq_right (by omega)]
    · have e3 : (List.range j).flatMap G.Lx = G.flat j := rfl
      rw [e3, hF]
      refine DrvR.chordListAt_of_seg (m := G.m₀) (B := G.m₀ (G.T + 3 * j)) g4 ?_
      rw [hℓ]
      unfold seg
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [mem5, ite_eq_right (by omega), ite_eq_left (by omega), seg_pt sg₂ hi, m₁, hI.low _ (by omega)]
  · -- the buckets
    intro q hq
    rw [hF1] at hq
    have e1 : G.flat (j + 1) = G.flat j ++ G.Lx j := flat_succ G.Lx j
    rw [e1]
    rcases Nat.lt_or_ge q (2 * F) with hq1 | hq1
    · rw [mem5, ite_eq_right (by omega), ite_eq_right (by omega), hI.bkt q (by omega),
        DrvLM.endPos_append_left (by omega)]
    · obtain ⟨q', rfl⟩ : ∃ q', q = 2 * F + q' := ⟨q - 2 * F, by omega⟩
      have ea := DrvLM.endPos_append_right (G.flat j) (G.Lx j) q'
      rw [hF] at ea
      rw [ea, mem5, ite_eq_left (by omega),
        show G.A₀ + 3 * G.K₂ + (2 * F + q') = G.A₀ + 3 * G.K₂ + 2 * F + q' by ring,
        seg_pt sg₄ (by omega), m₃, mo₂ _ (by omega), m₁, hI.low _ (by omega)]
      exact g7 q' (by omega)

/-- **The gather loop.** -/
theorem loop_exec {G : GEnv} (hG : GGood G) {e : Config} (hI : LInv G 0 e) :
    ∃ e' k, Exec G.P G.W ltLoop e e' k ∧ LInv G G.R e' ∧
      Restore.RF DrvR.drvBands G.A₀ e e' k ∧ k ≤ (35 * G.Mx + 32) * G.R + 2 := by
  obtain ⟨e', k, ex, ⟨j, hJ⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := G.P) (W := G.W)
    (a := 211130) (b := 211011) (body := ltBody) (B := DrvR.drvBands) (A₀ := G.A₀)
    (fun e => ∃ j, LInv G j e) (fun e => G.R - e.nreg 211130) (35 * G.Mx + 30)
    (fun e ⟨_, h⟩ => h.wb)
    (fun e ⟨j, hJ⟩ ht => by
      rw [hJ.r30, hJ.r11] at ht
      obtain ⟨e', k, ex, hJ', RF', hk⟩ := body_step hG hJ ht
      exact ⟨e', k, ex, ⟨j + 1, hJ'⟩, RF', hk, by rwo [hJ.r30, hJ'.r30]⟩) ⟨0, hI⟩
  have hjR : j = G.R := by rw [hJ.r30, hJ.r11] at hx; have := hJ.jle; omega
  subst hjR
  refine ⟨e', k, ex, hJ, RFl, ?_⟩
  rw [hI.r30] at hk
  simpa using hk

end

end DrvLT

end Chazelle.Core
