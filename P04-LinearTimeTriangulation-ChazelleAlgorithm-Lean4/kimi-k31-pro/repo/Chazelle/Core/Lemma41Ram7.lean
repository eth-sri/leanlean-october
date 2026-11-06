module

public import Chazelle.Core.Lemma41Ram6
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 16000000

/-!
# WP-J, part 15: one merge step

`pairS sM`: read two consecutive nodes from the level array, write the descriptor of their union,
merge them with the merge program `sM`, and append the cell `[TD, NF, prev]` of the new node
(`pairS_exec`).  Everything below the entry allocator is kept, so earlier nodes survive
(`NodeOK.agree`), and the context keeps holding (with the same capacity).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs SweepPrim SignK WalkKey Chazelle.Merge

@[expose] public section

/-- **One merge step.** -/
def pairS (sM : Stmt) : Stmt := .seq preB (.seq descS (.seq setupB (.seq sM postB)))

/-- The registers of band `bL41` written by a merge step. -/
def PairRG (r : ℕ) : Prop :=
  DescRG r ∨ r = 160035 ∨ r = 160036 ∨ r = 160037 ∨ r = 160090 ∨ r = 160091 ∨ r = 160092 ∨
    r = 160093 ∨ r = 160062 ∨ r = 160063 ∨ r = 160064 ∨ r = 160065

/-- The cost of one merge, in terms of the chord counts `x, y`, the granularity `γ` of the parts
and the length `M` of the union. -/
def mergeCostV (κ F G H : ℕ → ℕ) (x y γ M : ℕ) : ℕ :=
  κ 4 * (x + y + 1) * F (γ + fuseLoss) * G (γ + fuseLoss) *
    (H (γ + fuseLoss) + Nat.clog 2 (M + 1) + 1)

theorem band_l41_notin : bL41 ∉ mergeBands ∪ oracleBands := by decide

theorem band_merge_in : bMerge ∈ mergeBands ∪ oracleBands := by decide

theorem band_sign_in : bSign ∈ mergeBands ∪ oracleBands := by decide

theorem bandOf_l41 {r : ℕ} (h1 : 160000 ≤ r) (h2 : r < 170000) : bandOf r = bL41 := by
  ufo bandOf bL41

theorem bk_false_of {r : ℕ} (h : bandOf r ∉ mergeBands ∪ oracleBands) : Bk r = false := by
  unfold Bk
  by_contra hc
  simp [decide_eq_false_iff_not, not_not] at hc
  have : bandOf r = bSign := by ufo bandOf bSign
  rw [this] at h; exact h band_sign_in

theorem not_mergeReg_of {r : ℕ} (h : bandOf r ∉ mergeBands ∪ oracleBands) :
    r < 100000 ∨ 100009 < r := by
  by_contra hc
  have : bandOf r = bMerge := by ufo bandOf bMerge
  rw [this] at h; exact h band_merge_in

section proofs

variable {P : Polygon} {W : ℕ}

/-- **One merge step on the RAM.** -/
theorem pairS_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P (chainModel C))
    {c : Config} (hw : WordsBounded W c)
    {A ptr prev i j hX γ₀ tgt hp d1 f1 d2 f2 γ1 γ2 : ℕ} {C1 C2 : Chain}
    (hA : c.nreg ALLOC = A) (h65 : c.nreg 160065 = ptr) (h63 : c.nreg 160063 = prev)
    (h62 : c.nreg 160062 = i) (h64 : c.nreg 160064 = j) (h33 : c.nreg 160033 = γ₀)
    (h34 : c.nreg 160034 = tgt) (h00 : c.nreg 160000 = hX)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2) (h81 : c.nreg 160081 = 5)
    (h83 : c.nreg 160083 = 3) (h84 : c.nreg 160084 = 4)
    (m1 : c.nmem ptr = d1) (m2 : c.nmem (ptr + 1) = f1) (m3 : c.nmem (ptr + 2) = d2)
    (m4 : c.nmem (ptr + 3) = f2)
    (hn1 : NodeOK P c.nmem A hp d1 f1 C1 γ1) (hn2 : NodeOK P c.nmem A hp d2 f2 C2 γ2)
    (hγ1 : γ1 ≤ γ₀) (hγ2 : γ2 ≤ γ₀) (hcons : C2.s = C1.s + C1.m)
    (hXh : X.holds P c.nmem hX A) (hcap : γ₀ + fuseLoss ≤ X.cap P c.nmem hX)
    (htg : γ₀ + fuseLoss ≤ tgt)
    (hptr : ptr + 4 ≤ W) (hi : i + 2 ≤ W) (hj : j + 1 ≤ W)
    (hbud : A + 5 + mergeCostV κ F G H (c.nmem f1) (c.nmem f2) γ₀ (C1.m + C2.m) + 3 ≤ W) :
    ∃ c' k, Exec P W (pairS sM) c c' k ∧
      k ≤ mergeCostV κ F G H (c.nmem f1) (c.nmem f2) γ₀ (C1.m + C2.m) + 329 ∧
      WordsBounded W c' ∧ c'.nreg ALLOC ≤ A + k ∧
      ∃ E TD f C, A + 5 ≤ E ∧ E ≤ A + 5 + mergeCostV κ F G H (c.nmem f1) (c.nmem f2) γ₀
          (C1.m + C2.m) ∧
        c'.nreg ALLOC = E + 3 ∧ c'.nmem E = TD ∧ c'.nmem (E + 1) = f ∧ c'.nmem (E + 2) = prev ∧
        C.s = C1.s ∧ C.m = C1.m + C2.m ∧ NodeOK P c'.nmem (E + 3) hp TD f C tgt ∧
        c'.nreg 160063 = E ∧ c'.nreg 160065 = ptr + 4 ∧ c'.nreg 160062 = i + 2 ∧
        c'.nreg 160064 = j + 1 ∧
        (∀ a, a < A → c'.nmem a = c.nmem a) ∧ (∀ a, a < A → c'.rmem a = c.rmem a) ∧
        c'.output = c.output ∧
        X.holds P c'.nmem hX (E + 3) ∧ X.cap P c'.nmem hX = X.cap P c.nmem hX ∧
        (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨d1a, d1P, d1h, d1A, hpA, d1n, N1, hN1, hc1⟩ := hn1
  obtain ⟨d2a, d2P, d2h, d2A, -, d2n, N2, hN2, hc2⟩ := hn2
  have hlen : C1.m + C2.m + 1 ≤ C1.P.n := by rwo [d1P, hQn]
  have hAW : A + 5 ≤ W := by omega
  -- 1. the loads
  obtain ⟨c1, k1, e1, hk1, hw1, l35, l90, l36, l91, l37, lA, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    preB_exec (P := P) hw h65 h24 h81 hA (by omega) hAW
  rw [m1] at l35; rw [m2] at l90; rw [m3] at l36; rw [m4] at l91
  have c1r : ∀ r, 160000 ≤ r → r < 160035 → c1.nreg r = c.nreg r := fun r a b =>
    fr1 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by rwo [hAl])
  -- 2. the descriptor of the union
  have hd1c : ChainDescAt c1.nmem d1 (Qof P) (Host.whole P.n) C1 := by rw [hm1]; exact d1a
  have hd2c : ChainDescAt c1.nmem d2 (Qof P) (Host.whole P.n) C2 := by rw [hm1]; exact d2a
  obtain ⟨c2, k2, e2, hk2, hw2, -, t0, t1, t2, t3, t4, hm2, fr2, frr2, hrm2, ho2⟩ :=
    descS_exec hG hWn hw1 l35 l36 l37 (by rwx [c1r _ (by omega) (by omega)])
      hd1c hd2c d1P d2P hcons (by omega) (by omega) (by omega) hAW
  have c21 : ∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → c2.nreg r = c1.nreg r :=
    fun r h1 h2 => fr2 r (fun h => h2 (Or.inl h)) (bk_false_of h1)
  have c2r : ∀ r, 160000 ≤ r → r < 160035 → c2.nreg r = c.nreg r := fun r a b => by
    rw [fr2 r (by ufo DescRG) (by ufs Bk; omega)]; exact c1r r a b
  have c2A : c2.nreg ALLOC = A + 5 := by
    rw [fr2 _ (by ruo [hAl] DescRG) (by rwd [hAl])]; exact lA
  have c2_37 : c2.nreg 160037 = A := by
    rwx [fr2 _ (by ufo DescRG) (by ufs Bk)]
  have c2_35 : c2.nreg 160035 = d1 := by
    rwx [fr2 _ (by ufo DescRG) (by ufs Bk)]
  have c2_36 : c2.nreg 160036 = d2 := by
    rwx [fr2 _ (by ufo DescRG) (by ufs Bk)]
  have c2_90 : c2.nreg 160090 = f1 := by
    rwx [fr2 _ (by ufo DescRG) (by ufs Bk)]
  have c2_91 : c2.nreg 160091 = f2 := by
    rwx [fr2 _ (by ufo DescRG) (by ufs Bk)]
  have c2_84 : c2.nreg 160084 = 4 := by
    rw [fr2 _ (by ufo DescRG) (by ufs Bk)]
    rw [fr1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rwo [hAl])]; exact h84
  have mem2 : ∀ a, a < A → c2.nmem a = c.nmem a := fun a ha => by
    rw [hm2 a (Or.inl ha), hm1]
  -- the descriptor of the union at `A`
  have hTD : ChainDescAt c2.nmem A (Qof P) (Host.whole P.n) (jOf C1 C2 hlen).whole := by
    have g1 := chainDescAt_agree d1a d1A d1h hpA mem2
    have g2 := chainDescAt_agree d2a d2A d2h hpA mem2
    refine descWhole hlen (by rw [d2P, d1P]) hcons g1 g2 ?_ t1 t2 t3 ?_
    · rw [t0, hm1, mem2 _ (by omega)]
    · rw [t4, hm1, mem2 _ (by omega), mem2 _ (by omega)]
  have hTDm : c2.nmem A = hp := by rw [t0, hm1, d1h]
  -- 3. the merge registers
  obtain ⟨c3, k3, e3, hk3, hw3, r0, r1, r2, r3, r4, r5, r6, r7, r9, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    setupB_exec (P := P) hw2
  rw [c2_35] at r0; rw [c2_36] at r1; rw [c2_37] at r2; rw [c2_90] at r3; rw [c2_91] at r4
  rw [c2r _ (by omega) (by omega), h33] at r5; rw [c2r _ (by omega) (by omega), h34] at r6
  rw [c2_84] at r7; rw [c2r _ (by omega) (by omega), h00] at r9
  have c3A : c3.nreg ALLOC = A + 5 := by rw [fr3 _ (by rwo [hAl])]; exact c2A
  have mem3 : ∀ a, a < A → c3.nmem a = c.nmem a := fun a ha => by rw [hm3]; exact mem2 a ha
  have mem3' : ∀ a, a < A → c.nmem a = c3.nmem a := fun a ha => (mem3 a ha).symm
  -- the context at `c3`
  have hX3 : X.holds P c3.nmem (rd c3 bMerge 9) (c3.nreg ALLOC) := by
    rw [r9, c3A]; exact X.mono _ _ _ _ _ (by omega) (X.local_ _ _ _ _ _ mem3' hXh)
  have hcap3 : X.cap P c3.nmem hX = X.cap P c.nmem hX := hXc _ _ _ _ _ mem3 hXh
  -- the nodes at `c3`
  have hn1' : NodeOK P c3.nmem (c3.nreg ALLOC) hp d1 f1 C1 γ1 := by
    rw [c3A]; exact (NodeOK.agree ⟨d1a, d1P, d1h, d1A, hpA, d1n, N1, hN1, hc1⟩ mem3).mono
      (by omega)
  have hn2' : NodeOK P c3.nmem (c3.nreg ALLOC) hp d2 f2 C2 γ2 := by
    rw [c3A]; exact (NodeOK.agree ⟨d2a, d2P, d2h, d2A, by omega, d2n, N2, hN2, hc2⟩ mem3).mono
      (by omega)
  have hTD3 : ChainDescAt c3.nmem A (Qof P) (Host.whole P.n) (jOf C1 C2 hlen).whole := by
    rwx [hm3]
  have hpre : MergePre X Ok P W c3 :=
    mergePre_of hG hWh hX3 (by rwx [r9, r5, hcap3]) r7 (by rwx [r5, r6])
      hn1' hn2' (by rw [r5]; exact hγ1) (by rw [r5]; exact hγ2) hcons hlen r0 r1 r2 r3 r4 hTD3
      (by rwx [hm3]) (by rw [c3A])
      hOk
  -- the chord counts
  have hf1 : c3.nmem f1 = c.nmem f1 := by
    rw [(hN1.transport mem3).holds.1, hN1.holds.1]
  have hf2 : c3.nmem f2 = c.nmem f2 := by
    rw [(hN2.transport mem3).holds.1, hN2.holds.1]
  have hcost : mergeCost κ F G H c3 =
      mergeCostV κ F G H (c.nmem f1) (c.nmem f2) γ₀ (C1.m + C2.m) := by
    unfold mergeCost mergeCostV
    rw [r7, r3, r4, r5, r2, hf1, hf2, hm3, t2]
  -- 4. the merge
  obtain ⟨c4, k4, e4, hk4, hpost, fr4⟩ := hMM P W c3 hw3 hpre (by show _ + mergeCost κ F G H c3 ≤ W; rwo [c3A, hcost])
  replace hk4 : k4 ≤ mergeCost κ F G H c3 := hk4
  rw [hcost] at hk4
  obtain ⟨fr4r, fr4rr, fr4m, fr4rm, fr4o, fr4a, fr4b⟩ := fr4
  have hJ : JunctionAt c3.nmem (rd c3 bMerge 0) (rd c3 bMerge 1) (rd c3 bMerge 2) (Qof P)
      (Host.whole P.n) (jOf C1 C2 hlen) := by
    rw [r0, r1, r2]
    refine ⟨?_, ?_, hTD3⟩
    · rw [jOf_left]; exact hn1'.1
    · rw [jOf_right hlen (by rw [d2P, d1P]) hcons]; exact hn2'.1
  obtain ⟨N, -, hNW, hNc⟩ := hpost _ _ N1 N2 hJ (by rw [r3]; exact (hN1.transport mem3).holds)
    (by rw [r4]; exact (hN2.transport mem3).holds)
  rw [r6, r7] at hNc
  set E := c4.nreg ALLOC with hE
  have hE5 : A + 5 ≤ E := by rw [hE, ← c3A]; exact fr4a
  have hE6 : E ≤ A + 5 + mergeCostV κ F G H (c.nmem f1) (c.nmem f2) γ₀ (C1.m + C2.m) := by
    rw [hE]; have := fr4b; rwo [c3A] at this
  have c43 : ∀ r, bandOf r ∉ mergeBands ∪ oracleBands → r ≠ ALLOC → c4.nreg r = c3.nreg r :=
    fr4r
  have c4c : ∀ r, 160000 ≤ r → r < 160035 → c4.nreg r = c.nreg r := fun r a b => by
    rw [c43 r (by rw [bandOf_l41 a (by omega)]; exact band_l41_notin) (by rwo [hAl]),
      fr3 r (by omega)]; exact c2r r a b
  have c4_37 : c4.nreg 160037 = A := by
    rw [c43 _ (by rw [bandOf_l41 (by omega) (by omega)]; exact band_l41_notin)
      (by rwo [hAl]), fr3 _ (by omega)]; exact c2_37
  have c4_84 : c4.nreg 160084 = 4 := by
    rw [c43 _ (by rw [bandOf_l41 (by omega) (by omega)]; exact band_l41_notin)
      (by rwo [hAl]), fr3 _ (by omega)]; exact c2_84
  have c4k : ∀ r, 160065 ≤ r → r < 160090 → c4.nreg r = c.nreg r := fun r a b => by
    rw [c43 r (by rw [bandOf_l41 (by omega) (by omega)]; exact band_l41_notin)
      (by rwo [hAl]), fr3 r (by omega),
      fr2 r (by ufo DescRG) (by ufs Bk; omega)]
    exact fr1 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rwo [hAl])
  have c4k' : ∀ r, 160057 ≤ r → r < 160065 → c4.nreg r = c.nreg r := fun r a b => by
    rw [c43 r (by rw [bandOf_l41 (by omega) (by omega)]; exact band_l41_notin)
      (by rwo [hAl]), fr3 r (by omega),
      fr2 r (by ufo DescRG) (by ufs Bk; omega)]
    exact fr1 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rwo [hAl])
  -- 5. the cell and the advance
  obtain ⟨c5, k5, e5, hk5, hw5, w0, w1, w2, hm5, a5, q63, q65, q62, q64, fr5, hrr5, hrm5, ho5⟩ :=
    postB_exec (P := P) e4.wb_right hE.symm c4_37 rfl (by rw [c4k' _ (by omega) (by omega), h63])
      (by rw [c4k _ (by omega) (by omega), h65]) (by rw [c4k' _ (by omega) (by omega), h62])
      (by rw [c4k' _ (by omega) (by omega), h64]) (by rw [c4c _ (by omega) (by omega), h24])
      (by rw [c4k _ (by omega) (by omega), h80]) (by rw [c4k _ (by omega) (by omega), h83])
      c4_84 (by omega) hptr hi hj
  -- memory
  have mem54 : ∀ a, a < E → c5.nmem a = c4.nmem a := fun a ha => hm5 a (Or.inl ha)
  have mem53 : ∀ a, a < A + 5 → c5.nmem a = c3.nmem a := fun a ha => by
    rw [mem54 a (by omega), fr4m a (by rwx [c3A])]
  have mem5 : ∀ a, a < A → c5.nmem a = c.nmem a := fun a ha => by
    rw [mem53 a (by omega)]; exact mem3 a ha
  have mem5' : ∀ a, a < E + 3 → c5.nmem a = c5.nmem a := fun _ _ => rfl
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))),
    by omega, hw5, by rw [a5]; have := fr4b; rwo [c3A] at this, E, A, c4.nreg 100008, (jOf C1 C2 hlen).whole, hE5, hE6, a5, w0, w1, w2,
    rfl, rfl, ⟨?_, ?_, ?_, by omega, by omega, ?_, N, ?_, hNc⟩, q63, q65, q62, q64, mem5,
    fun a ha => ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_⟩
  · exact chainDescAt_agree hTD3 (by omega) (by rw [hm3]; try exact hTDm) (by omega) mem53
  · rw [jOf_whole_P]; exact d1P
  · rwx [mem53 _ (by omega), hm3]
  · show C1.s + (C1.m + C2.m) + 1 ≤ P.n; omega
  · exact (hNW.transport mem54).mono (by omega)
  · rw [hrm5, fr4rm a (by rwo [c3A]), hrm3, hrm2, hrm1]
  · rw [ho5, fr4o, ho3, ho2, ho1]
  · refine X.mono _ _ _ _ _ (show A ≤ E + 3 by omega) (X.local_ _ _ _ _ _ ?_ hXh)
    intro a ha; exact (mem5 a ha).symm
  · exact hXc _ _ _ _ _ mem5 hXh
  · have e1' : ¬ (r = 160092 ∨ r = 160093 ∨ r = 160063 ∨ r = 160065 ∨ r = 160062 ∨
        r = 160064) := fun h => h2 (by ufo PairRG)
    rw [fr5 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h3,
      c43 r h1 h3, fr3 r (not_mergeReg_of h1), c21 r h1 h2]
    exact fr1 r (by ufo PairRG at h2) (by ufo PairRG at h2)
      (by ufo PairRG at h2) (by ufo PairRG at h2)
      (by ufo PairRG at h2) (by ufo PairRG at h2) h3
  · rw [hrr5, fr4rr r h1, hrr3, frr2 r (bk_false_of h1)
      (by intro h; exact h2 (Or.inl (by ufo DescRG))), hrr1]

end proofs

end

end Chazelle.Core.L41
