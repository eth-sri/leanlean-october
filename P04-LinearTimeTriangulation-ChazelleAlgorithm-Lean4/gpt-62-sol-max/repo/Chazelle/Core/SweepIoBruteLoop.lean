module

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.SweepIoBruteMath

/-!
# The sweep RAM (WP-D), answers: the arcs of the brute-force shot

`bLoop` copies the arcs of the normal form `N₁` (handle `sw 3`) to fresh memory at the allocator,
each end normalised (`normS` with the chain descriptor of `C₁` at `sw 20`): record `k` holds
`nArc (chainModel C₁) Q N₁ k`.  The base is left in `bBase`, the number of arcs in `bN`.

Registers: `bX … bT` (`sw 4001 … 4005`), the gather registers `gS … gE1`, `gO`, `gO + 1`
(`sw 1016 … 1021`, `put4`), the oracle bands (`normS`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers and code -/

@[ram_layout] def bX : ℕ := sw 4001
@[ram_layout] def bN : ℕ := sw 4002
@[ram_layout] def bA4 : ℕ := sw 4003
@[ram_layout] def bBase : ℕ := sw 4004
@[ram_layout] def bT : ℕ := sw 4005

/-- The registers the loop writes outside the oracle bands (besides the allocator). -/
@[local ram_layout] def BSet (r : ℕ) : Prop := (sw 4001 ≤ r ∧ r ≤ sw 4005) ∨ (sw 1016 ≤ r ∧ r ≤ sw 1021)

/-- The head: the number of arcs, the base of the arc records, the output base, the counter. -/
def bHead : List Instr :=
  [.addN bX (sw 3) K1, .loadN bN bX, .addN bX (sw 3) K4, .loadN bA4 bX, .copyN bBase ALLOC,
    .constN bT 0]

/-- Read the ends of arc `bT`. -/
def bRead : List Instr :=
  [.addN bX bT bT, .addN bX bX bX, .addN bX bX bT, .addN bX bA4 bX, .addN bX bX K1, .loadN gS bX,
    .addN bX bX K1, .loadN gS1 bX, .addN bX bX K1, .loadN gE bX, .addN bX bX K1, .loadN gE1 bX]

/-- One arc: read, normalise both ends, store, advance. -/
def bArc : Stmt :=
  .seq (block bRead) (.seq (normS (sw 20) gS gS1 gO) (.seq (normS (sw 20) gE gE1 gO)
    (.seq put4 (block [.addN bT bT K1]))))

/-- **The loop** over the arcs. -/
def bLoop : Stmt := .seq (block bHead) (.whileLtN bT bN bArc)

/-- The cost of one arc. -/
@[ram_layout] def bArcK : ℕ := 22051

/-- The cost of the loop over `A` arcs. -/
def bLoopK (A : ℕ) : ℕ := 6 + ((bArcK + 2) * A + 2)

/-! ## The blocks -/

section

variable (m f : ℕ → ℕ) (hk1 : f K1 = 1)

include m hk1 in
theorem bRead_val :
    regB m bRead f gS = m (f bA4 + 5 * f bT + 1) ∧
    regB m bRead f gS1 = m (f bA4 + 5 * f bT + 2) ∧
    regB m bRead f gE = m (f bA4 + 5 * f bT + 3) ∧
    regB m bRead f gE1 = m (f bA4 + 5 * f bT + 4) := by
  register_block normalized [bRead]

theorem bRead_other (m f : ℕ → ℕ) {q : ℕ} (h : ¬ BSet q) : regB m bRead f q = f q :=
  (by register_keep [bRead, BSet])

theorem bRead_other' (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ bX) (h2 : q ≠ gS) (h3 : q ≠ gS1)
    (h4 : q ≠ gE) (h5 : q ≠ gE1) : regB m bRead f q = f q :=
  (by register_keep [bRead])

include m hk1 in
theorem bRead_ok (hb : f bA4 + 5 * f bT + 4 ≤ W) :
    okB W m bRead f := by
  register_block normalized [bRead]

include m hk1 in
theorem bHead_val (hk4 : f K4 = 4) :
    regB m bHead f bN = m (f (sw 3) + 1) ∧ regB m bHead f bA4 = m (f (sw 3) + 4) ∧
    regB m bHead f bBase = f ALLOC ∧ regB m bHead f bT = 0 := by
  have e1 : f 240611 = 1 := hk1
  have e4 : f 240613 = 4 := hk4
  simp only [bHead, regB, regI, upd, bX, bN, bA4, bBase, bT, K1, K4, ALLOC, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e4]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem bHead_other (m f : ℕ → ℕ) {q : ℕ} (h : ¬ BSet q) : regB m bHead f q = f q :=
  (by register_keep [bHead, BSet])

include m hk1 in
theorem bHead_ok (hk4 : f K4 = 4) (hb : f (sw 3) + 4 ≤ W) :
    okB W m bHead f := by
  register_block normalized [bHead]

end

/-! ## The invariant -/

/-- **The state of the loop** after `i` arcs (relative to the entry `cS`). -/
def BW (M : Model) (Q : Polygon) (N : NF) (cS c : Config) (i : ℕ) : Prop :=
  c.nreg bBase = cS.nreg ALLOC ∧ c.nreg bT = i ∧ i ≤ N.arcs.length ∧
    c.nreg bN = N.arcs.length ∧ c.nreg bA4 = cS.nmem (cS.nreg (sw 3) + 4) ∧
    c.nreg ALLOC = cS.nreg ALLOC + 4 * i ∧
    (∀ k, k < i → ShotList.arcAt c.nmem (cS.nreg ALLOC) k = nArc M Q N k) ∧
    (MemEqBelow (cS.nreg ALLOC) c.nmem cS.nmem) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ BSet r → r ≠ ALLOC → c.nreg r = cS.nreg r)

theorem bset_sw20 : ¬ BSet (sw 20) := by reg_omega

theorem nob_sw {j : ℕ} (h : j < 10000) : bandOf (sw j) ∉ oracleBands :=
  not_oracle_sw (by reg_omega) (by reg_omega)

/-- The chain context survives the loop. -/
theorem BW.ctx {M : Model} {Q : Polygon} {N : NF} {cS : Config} {i : ℕ} {C : Chain}
    (h : BW M Q N cS c i) (hctx : ChainCtx P W cS (sw 20) C) : ChainCtx P W c (sw 20) C :=
  hctx.transport (h.2.2.2.2.2.2.2.2 _ (nob_sw (by norm_num)) bset_sw20
    (by reg_omega)) h.2.2.2.2.2.2.2.1 (by rw [h.2.2.2.2.2.1]; omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One arc of the loop.** -/
theorem bArc_irs {C : Chain} {N : NF} {B E : ℕ} {cS : Config} {i : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W cS (sw 20) C)
    (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hNW : NFWithin cS.nmem B E N) (hB : cS.nreg (sw 3) = B) (hE : E ≤ cS.nreg ALLOC)
    (hin : BW (chainModel C) (Qof P) N cS c i) (hi : i < N.arcs.length)
    (hroom : c.nreg ALLOC + bArcK ≤ W) :
    IRS P W c₀ bArc c bArcK (fun c' => BW (chainModel C) (Qof P) N cS c' (i + 1)) := by
  have hK₀ := hK.fix hI
  have hctxc := hin.ctx hctx
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hin
  have hNWc := hNW.transport (fun a ha => w8 a (by omega))
  have hNA := hNWc.holds
  obtain ⟨b1, -, b3, -⟩ := Restore.nf_bounds hNWc
  have vA4 : c.nreg bA4 = c.nmem (B + 4) := by ram_finish
  have harec := hNA.2.2.2.2.2.2.1 i hi
  have hab := b3 i hi
  obtain ⟨⟨hps, hse, hsy⟩, ⟨hpe, hee, hey⟩⟩ := arc_end_facts hP hNF hi
  have hAW := hI.hw.1 ALLOC
  -- the read block
  have hok : okB W c.nmem bRead c.nreg := bRead_ok _ _ hK₀.2.1 (by rw [vA4, w2]; omega)
  refine IRS.mono (K := bRead.length + (11015 + (11015 + (8 + 1)))) (IRS.seq
    (IRS.block bRead hI hok) ?_) (by simp [bRead, bArcK]) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  set c₁ : Config := { c with nreg := regB c.nmem bRead c.nreg } with hc₁
  obtain ⟨r1s, r1s1, r1e, r1e1⟩ := bRead_val c.nmem c.nreg hK₀.2.1
  rw [vA4, w2] at r1s r1s1 r1e r1e1
  have v1s : c₁.nreg gS = (N.arc i).s.edge := by rw [← harec.2.1]; exact r1s
  have v1s1 : c₁.nreg gS1 = (N.arc i).s.hgt := by rw [← harec.2.2.1]; exact r1s1
  have v1e : c₁.nreg gE = (N.arc i).e.edge := by rw [← harec.2.2.2.1]; exact r1e
  have v1e1 : c₁.nreg gE1 = (N.arc i).e.hgt := by rw [← harec.2.2.2.2]; exact r1e1
  have k1 : ∀ q, ¬ BSet q → c₁.nreg q = c.nreg q := fun q hq => bRead_other _ _ hq
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by reg_omega)
  have hctx₁ := hctxc.transport (k1 _ bset_sw20) (fun _ _ => rfl) hA1.ge
  -- normalise the start
  have hy1 : c₁.nreg gS < 6 → c₁.nreg gS ≠ 0 → c₁.nreg gS ≠ 2 → c₁.nreg gS ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₁.nreg gS, c₁.nreg gS1⟩).2| < C.radius := by
    rwa [v1s, v1s1]
  refine IRS.seq (normS_exact (normS_irs (dsc := sw 20) (pe := gS) (ph := gS1) (o := gO) hI₁
    (hK.fix hI₁) hctx₁ (by reg_omega)
    (by reg_omega)
    (by rwa [v1s]) (by rwa [v1s, v1s1]) hy1
    (by rw [hA1]; unfold bArcK at hroom; omega)) (by reg_omega)) ?_
  rintro c₂ hI₂ - - ⟨⟨n2s, n2s1, k2, -, -⟩, hA2, hm2⟩
  have nb : ∀ j, j < 10000 → bandOf (sw j) ∉ oracleBands := fun j hj => nob_sw hj
  have hctx₂ := hctx₁.transport
    (k2 (sw 20) (nb 20 (by norm_num)) (by reg_omega) (by reg_omega)
      (by reg_omega) (by reg_omega))
    (fun a' _ => by rw [hm2]) hA2.ge
  have v2e : c₂.nreg gE = (N.arc i).e.edge := by
    ram_simp [k2, v1e] 
  have v2e1 : c₂.nreg gE1 = (N.arc i).e.hgt := by
    ram_simp [k2, v1e1] 
  -- normalise the end
  have hy2 : c₂.nreg gE < 6 → c₂.nreg gE ≠ 0 → c₂.nreg gE ≠ 2 → c₂.nreg gE ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₂.nreg gE, c₂.nreg gE1⟩).2| < C.radius := by
    rwa [v2e, v2e1]
  refine IRS.seq (normS_exact (normS_irs (dsc := sw 20) (pe := gE) (ph := gE1) (o := gO) hI₂
    (hK.fix hI₂) hctx₂ (by reg_omega)
    (by reg_omega)
    (by rwa [v2e]) (by rwa [v2e, v2e1]) hy2
    (by rw [hA2, hA1]; unfold bArcK at hroom; omega)) (by reg_omega)) ?_
  rintro c₃ hI₃ - - ⟨⟨n3e, n3e1, k3, -, -⟩, hA3, hm3⟩
  have v3s := k3 gS (nb 1016 (by norm_num))
    (by reg_omega) (by reg_omega)
    (by reg_omega) (by reg_omega)
  have v3s1 := k3 gS1 (nb 1017 (by norm_num))
    (by reg_omega) (by reg_omega)
    (by reg_omega) (by reg_omega)
  have ns : (⟨c₃.nreg gS, c₃.nreg gS1⟩ : WPos) =
      Restore.normOf (chainModel C) (Qof P) (N.arc i).s := by
    rw [v3s, v3s1, n2s1, n2s, v1s, v1s1]
    unfold nhgt
    have := (Restore.normOf_facts hps).2.1
    rcases hn : Restore.normOf (chainModel C) (Qof P) (N.arc i).s with ⟨e', h'⟩
    rw [hn] at this
    simp only at this ⊢
    rw [this]
  have ne' : (⟨c₃.nreg gE, c₃.nreg gE1⟩ : WPos) =
      Restore.normOf (chainModel C) (Qof P) (N.arc i).e := by
    rw [n3e1, n3e, v2e, v2e1]
    unfold nhgt
    have := (Restore.normOf_facts hpe).2.1
    rcases hn : Restore.normOf (chainModel C) (Qof P) (N.arc i).e with ⟨e', h'⟩
    rw [hn] at this
    simp only at this ⊢
    rw [this]
  have hA3' : c₃.nreg ALLOC = c.nreg ALLOC := by rw [hA3, hA2, hA1]
  have hm3' : c₃.nmem = c.nmem := by rw [hm3, hm2]
  -- store the record
  refine IRS.seq (put4_irs hI₃ (hK.fix hI₃) (by rw [hA3']; unfold bArcK at hroom; omega)) ?_
  rintro c₄ hI₄ - - ⟨hA4, k4, hm4, -, -, -⟩
  -- the frame from `c` to `c₄`
  have k14 : ∀ q, bandOf q ∉ oracleBands → q ≠ bX → q ≠ gS → q ≠ gS1 → q ≠ gE → q ≠ gE1 →
      q ≠ gO → q ≠ gO + 1 → q ≠ ALLOC → c₄.nreg q = c.nreg q := by
    intro q hq h1 h2 h3 h4 h5 h6 h7 h8
    rw [k4 _ h8, k3 _ hq h5 h6 h7 h8, k2 _ hq h3 h6 h7 h8]
    exact bRead_other' _ _ h1 h2 h3 h4 h5
  have hA4' : c₄.nreg ALLOC = c.nreg ALLOC + 4 := by rw [hA4, hA3']
  have k4T : c₄.nreg bT = i := by
    rw [k14 bT (nb 4005 (by norm_num)) (by reg_omega) (by reg_omega)
      (by reg_omega) (by reg_omega)
      (by reg_omega) (by reg_omega)
      (by reg_omega) (by reg_omega), w2]
  have hK1₄ := (hK.fix hI₄).2.1
  have hok5 : okB W c₄.nmem [.addN bT bT K1] c₄.nreg := by
    have e1 : c₄.nreg 240611 = 1 := hK1₄
    have e3 : c₄.nreg 244005 = i := k4T
    simp only [reg_check, bT, K1, sw]
    simp only [Nat.reduceAdd, e1, e3]
    exact ⟨⟨iscr_sw (by norm_num) (by norm_num), by unfold bArcK at hroom; omega⟩, trivial⟩
  refine (IRS.block _ hI₄ hok5).mono (by simp) ?_
  rintro c₅ rfl
  have r5 : ∀ q, q ≠ bT → regB c₄.nmem [.addN bT bT K1] c₄.nreg q = c₄.nreg q := fun q h1 =>
    regB_other _ _ _ (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl; simp only [dstI]; exact fun h => h1 h.symm)
  have v5T : regB c₄.nmem [.addN bT bT K1] c₄.nreg bT = i + 1 := by
    have e1 : c₄.nreg 240611 = 1 := hK1₄
    have e3 : c₄.nreg 244005 = i := k4T
    simp only [regB, regI, upd, bT, K1, sw]
    simp only [Nat.reduceAdd, ite_true, e1, e3]
  have kk := fun q hq h0 h1 h2 h3 h4 h5 h6 h7 h8 => (r5 q h0).trans (k14 q hq h1 h2 h3 h4 h5 h6 h7 h8)
  have kb : ∀ q, bandOf q ∉ oracleBands → ¬ BSet q → q ≠ ALLOC →
      regB c₄.nmem [.addN bT bT K1] c₄.nreg q = c.nreg q := by
    intro q hq hb hqa
    have ne : ∀ g, BSet g → q ≠ g := fun g hgs h => hb (h ▸ hgs)
    exact kk q hq (ne _ (by reg_omega)) (ne _ (by reg_omega))
      (ne _ (by reg_omega)) (ne _ (by reg_omega))
      (ne _ (by reg_omega)) (ne _ (by reg_omega))
      (ne _ (by reg_omega)) (ne _ (by reg_omega)) hqa
  have kreg : ∀ q, (q = bBase ∨ q = bN ∨ q = bA4) →
      regB c₄.nmem [.addN bT bT K1] c₄.nreg q = c.nreg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl <;>
      exact kk _ (nb _ (by norm_num)) (by decide)
        (by decide) (by decide)
        (by decide) (by decide)
        (by decide) (by decide)
        (by decide) (by decide)
  have hA5 : regB c₄.nmem [.addN bT bT K1] c₄.nreg ALLOC = c.nreg ALLOC + 4 := by
    assumption
  have hmem5 : c₄.nmem = mem4 c.nmem (cS.nreg ALLOC + 4 * i) (c₃.nreg gS) (c₃.nreg gS1)
      (c₃.nreg gE) (c₃.nreg gE1) := by rw [hm4, hm3', hA3', w6]
  refine ⟨?_, v5T, hi, ?_, ?_, ?_, fun k hk => ?_, fun a' ha' => ?_, fun q hq hb hqa => ?_⟩
  · simp [kreg, w1]
  · simp [kreg, w4]
  · simp [kreg, w5]
  · show regB _ _ _ ALLOC = _; rw [hA5, w6]; ring
  · show ShotList.arcAt c₄.nmem _ k = _
    rw [hmem5]
    unfold mem4
    rcases Nat.lt_or_ge k i with hl | hg
    · rw [Restore.arcAt_upd4 hl, w7 k hl]
    · have hk' : k = i := by omega
      subst hk'
      rw [Restore.arcAt_upd4_new]
      unfold nArc
      rw [← ns, ← ne']
  · show c₄.nmem a' = _
    rw [hmem5]
    unfold mem4
    simp only [upd]
    ram_rw [ite_eq_right, ite_eq_right, ite_eq_right, ite_eq_right, w8 a' ha']
  · ram_simp [kb q hq hb hqa, w9 q hq hb hqa] 

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The loop**: the normalised arcs of `N` at the allocator on entry, base in `bBase`, count
in `bN`. -/
theorem bLoop_irs {C : Chain} {N : NF} {B E : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c (sw 20) C)
    (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hNW : NFWithin c.nmem B E N) (hB : c.nreg (sw 3) = B) (hE : E ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + bLoopK N.arcs.length ≤ W) :
    IRS P W c₀ bLoop c (bLoopK N.arcs.length)
      (fun c' => BW (chainModel C) (Qof P) N c c' N.arcs.length) := by
  have hK₀ := hK.fix hI
  obtain ⟨b1, -⟩ := Restore.nf_bounds hNW
  have hNA : NFAt c.nmem B N := hNW.holds
  have hok : okB W c.nmem bHead c.nreg := bHead_ok _ _ hK₀.2.1 hK₀.2.2.2.1
    (by rw [hB]; have := hI.hw.1 ALLOC; omega)
  refine (IRS.seq (IRS.block bHead hI hok) ?_).mono (K := bHead.length + ((bArcK + 2) *
    N.arcs.length + 2)) (by simp [bHead, bLoopK]) (fun _ h => h)
  rintro c₁ hI₁ - - rfl
  obtain ⟨vN, vA4, vB, vT⟩ := bHead_val c.nmem c.nreg hK₀.2.1 hK₀.2.2.2.1
  set A := N.arcs.length with hAd
  have hBW1 : BW (chainModel C) (Qof P) N c { c with nreg := regB c.nmem bHead c.nreg } 0 := by
    refine ⟨vB, vT, Nat.zero_le _, ?_, vA4, ?_, fun k hk => absurd hk (by omega), fun _ _ => rfl,
      fun q _ hq _ => bHead_other _ _ hq⟩
    · show regB _ _ _ bN = _; rw [vN, hB]; exact hNA.2.1
    · show regB _ _ _ ALLOC = _; rw [bHead_other _ _ (by reg_omega)]; ring
  have hT1 : ({ c with nreg := regB c.nmem bHead c.nreg } : Config).nreg bT = 0 := vT
  have hA1 : ({ c with nreg := regB c.nmem bHead c.nreg } : Config).nreg ALLOC = c.nreg ALLOC :=
    bHead_other (q := ALLOC) c.nmem c.nreg (by reg_omega)
  refine (IRS.while (fun c' => ∃ i, BW (chainModel C) (Qof P) N c c' i)
    (fun c' => A - c'.nreg bT) bArcK ?_ ?_ hI₁ ⟨0, hBW1⟩ ?_).mono ?_ ?_
  · rintro c' ⟨i, hw⟩ hlt
    rw [hw.2.1, hw.2.2.2.1] at hlt
    rw [hw.2.1]; omega
  · rintro c' hI' ⟨i, hw⟩ hlt hroom'
    have hi : i < A := by rw [hw.2.1, hw.2.2.2.1] at hlt; exact hlt
    refine (bArc_irs hI' hK hctx hP hNF hNW hB hE hw hi hroom').mono le_rfl
      (fun c'' h => ⟨⟨i + 1, h⟩, ?_⟩)
    rw [h.2.1, hw.2.1]; omega
  · rw [hA1, hT1, Nat.sub_zero]; unfold bLoopK at hroom; omega
  · rw [hT1, Nat.sub_zero]
  · rintro c' ⟨⟨i, hw⟩, hn⟩
    rw [hw.2.1, hw.2.2.2.1] at hn
    have : i = A := by have := hw.2.2.1; omega
    subst this
    exact hw

end

end SweepIo

end Chazelle.Core
