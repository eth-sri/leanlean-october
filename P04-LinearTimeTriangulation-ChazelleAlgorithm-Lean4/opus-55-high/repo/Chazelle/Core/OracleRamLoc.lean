module

public import Chazelle.Core.OracleRamChord
public import Chazelle.Core.NFLocateSpec

/-!
# Lemma 3.6 (WP-H), RAM part 11: double identification without writing memory

`myLoc` is double identification (`NFLoc.locStmt`) with the binary search replaced by the search
with the stored table (`tsearch`): the direction procedure `locDir`, the setup `locSetup`, the
search with `keyCmp`, and the choice of the spine position `p = t - 1` (or `A - 1` if `t = 0`),
left in register `120170`.  The arc at spine position `p` is the one of `NFLoc.locate_pick`.

Main result: `myLoc_exec` (no memory written, the allocator unchanged).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- The spine position of the answer: `t - 1`, or `A - 1` if `t = 0`. -/
def myFinish : Stmt :=
  .ifLtN 120012 50105 (.instr (.subN 120170 50105 120011)) (.instr (.subN 120170 10504 120011))

/-- **Double identification with the stored table.** -/
def myLoc : Stmt := .seq locDir (.seq locSetup (.seq (tsearch 120041 120042 keyCmp) myFinish))

/-- The registers written by `myLoc`. -/
def BL (r : ℕ) : Bool :=
  Bdir r || Bloc r || Bcmp r || decide (50100 ≤ r ∧ r ≤ 50116) || decide (r = 120170)

/-- **Double identification with the stored table.**  With the model descriptor in `50000`, the
normal form in `50001`, the position in `50002`, `50003`, the table of powers at `TB` (register
`120041`, length `L` in `120042`), it leaves in `120170` a spine position `p` whose arc contains
the key of the position (as in `LocateSpec`). -/
theorem myLoc_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} {c : Config}
    (hw : WordsBounded W c) (hD : LocDPre P W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    {M : Model} {N : NF} (hM : ModelDescAt c.nmem (c.nreg 50000) (Qof P) M) (hGM : GoodModel M)
    (hN : NFAt c.nmem (c.nreg 50001) N) (hNF : IsNF M (Qof P) N)
    (hx : ProperPos M (Qof P) P.n ⟨c.nreg 50002, c.nreg 50003⟩)
    (hst : ∀ j, j < N.arcs.length → ProperPos M (Qof P) P.n (N.arc j).s)
    {TB L : ℕ} (hTBr : c.nreg 120041 = TB) (hLr : c.nreg 120042 = L)
    (h12 : c.nreg 120012 = 0) (h11 : c.nreg 120011 = 1)
    (htab : ∀ j, j < L → c.nmem (TB + j) = 2 ^ j) (hbig : N.arcs.length < 2 ^ L)
    (hB : c.nreg 50001 + 7 ≤ TB)
    (hAB : c.nmem (c.nreg 50001 + 4) + 5 * N.arcs.length ≤ TB)
    (hSB : c.nmem (c.nreg 50001 + 6) + N.arcs.length ≤ TB) (hTW : TB + L ≤ W) :
    ∃ c' k, Exec P W myLoc c c' k ∧ k ≤ 5500 * (L + 1) ∧ FrameB BL c c' ∧
      c'.nreg 120170 < N.arcs.length ∧
      (¬ M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩) →
        N.F M (Qof P) = ∅ ∨ sideInArc (M.key (Qof P) (N.arc (N.seq.getD (c'.nreg 120170) 0)).s)
          (M.key (Qof P) (N.arc (N.seq.getD (c'.nreg 120170) 0)).e)
          (M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩)) ∧
      (M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩) →
        M.key (Qof P) (N.arc (N.seq.getD (c'.nreg 120170) 0)).s =
            M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩ ∨
          M.key (Qof P) (N.arc (N.seq.getD (c'.nreg 120170) 0)).e =
            M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩) := by
  set B := c.nreg 50001 with hBdef
  set A := N.arcs.length with hAdef
  set AB := c.nmem (B + 4) with hABdef
  set SB := c.nmem (B + 6) with hSBdef
  set x : WPos := ⟨c.nreg 50002, c.nreg 50003⟩ with hxdef
  have hA1 : c.nmem (B + 1) = A := hN.2.1
  have hsl : N.seq.length = A := seq_length hNF
  have hseq : ∀ i, i < A → c.nmem (SB + i) = N.seq.getD i 0 := fun i hi =>
    hN.2.2.2.2.2.2.2.2.1 i (by omega)
  obtain ⟨hcov1, hcov2⟩ := hcov M (Qof P) (N.F M (Qof P)) hGM hNF.1
  have hA0 : 0 < A := by
    obtain ⟨U, hU, a, b, hab⟩ := hcov1
    obtain ⟨j, hj, -⟩ := listed_of_isArc hNF hU hab
    omega
  -- 1. the direction
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hd₁⟩ := locDir_ok P W c hw hD
  have d₁ := hd₁ M hM
  have w₁ := e₁.wb_right
  have b1 : c₁.nreg 50001 = B := f₁.1 _ (by decide)
  have b2 : c₁.nreg 50002 = c.nreg 50002 := f₁.1 _ (by decide)
  have b3 : c₁.nreg 50003 = c.nreg 50003 := f₁.1 _ (by decide)
  have m₁ : c₁.nmem = c.nmem := f₁.2.2.1
  -- 2. the setup
  obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W locSetup c₁ c₂ k₂ ∧ k₂ = 14 ∧
      (c₂.nreg 10500 = c.nreg 50002 ∧ c₂.nreg 10501 = c.nreg 50003 ∧
        c₂.nreg 10502 = c₁.nreg 10502 ∧ c₂.nreg 10503 = AB ∧ c₂.nreg 10504 = A ∧
        c₂.nreg 10505 = SB ∧ c₂.nreg 50103 = SB ∧ c₂.nreg 50104 = A) := by
    unfold locSetup
    exec_block
    · omega
    · config_simp; rw [b1]; omega
    · config_simp; rw [b1]; omega
    · config_simp; rw [b1]; omega
    · config_simp; rw [b1]; omega
    · config_simp; rw [b1]; omega
    · config_simp; rw [b1]; omega
    · refine ⟨rfl, ?_⟩
      config_simp
      rw [b1, b2, b3, m₁]
      exact ⟨rfl, rfl, rfl, hA1, rfl, rfl, hA1⟩
  obtain ⟨q500, q501, q502, q503, q504, q505, q103, q104⟩ := q
  have w₂ := e₂.wb_right
  have f₂ := exec_frameB e₂ wr_locSetup
  have m₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans m₁
  have R₂ : ∀ r, Bloc r = false → Bdir r = false → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    (f₂.1 r h1).trans (f₁.1 r h2)
  -- 3. the search
  set d := dirCode M x.edge with hd
  have hJ₂ : CmpJ x d AB A SB TB c.nmem c₂ :=
    ⟨q500, q501, by rw [q502, d₁], q503, q504, q505, fun a _ => by rw [m₂]⟩
  have hcmp := keyCmp_predOK hG hW x hx.2.2 d AB A SB TB c.nmem hAB (by omega)
  have hpr : ∀ i, i < A → (cmpPr P x d AB A c.nmem (c.nmem (SB + i)) = true ↔
      KeyPred M (Qof P) x (N.arc (N.seq.getD i 0)).s) := fun i hi => by
    rw [hseq i hi]
    exact cmpPr_eq hN x hx hst (seq_lt hNF hi)
  obtain ⟨c₃, k₃, e₃, hk₃, hJ₃, hL₃, m₃, a₃, ht₃, hpre₃, hpost₃⟩ := tsearch_exec (P := P) hcmp
    (by decide) (rT := 120041) (rL := 120042) (T := TB) (L := L) (by unfold bandOf bLocate; omega)
    (by unfold bandOf bLocate; omega) w₂ hJ₂ (cmpJ_stable x d AB A SB TB c.nmem)
    (by rw [R₂ _ (by decide) (by decide)]; exact hTBr) (by rw [R₂ _ (by decide) (by decide)]; exact hLr)
    (fun j hj => by rw [m₂]; exact htab j hj) (by rw [q104]; exact hbig)
    (by rw [q103, q104]; exact hSB) hTW
    (fun i j hij hj hprj => by
      rw [q103, m₂] at hprj ⊢
      rw [q104] at hj
      exact (hpr i (by omega)).2 (KeyPred.mono ((hpr j hj).1 hprj) (seq_sorted hNF hij hj)))
    (by omega)
  rw [q104] at ht₃ hpost₃
  rw [q103, m₂] at hpre₃ hpost₃
  obtain ⟨-, -, -, -, h504, -, -⟩ := hJ₃
  -- 4. the spine position
  set t := c₃.nreg 50105 with htdef
  have hpick := locate_pick (fun y hy => hcov2 y hy) hNF x hA0 ht₃
    (fun i hi => (hpr i (by omega)).1 (hpre₃ i hi))
    (fun hi hk => by
      have := (hpr t hi).2 hk
      rw [hpost₃ hi] at this
      exact Bool.false_ne_true this)
  have w₃ := e₃.wb_right
  have c12 : c₃.nreg 120012 = 0 := by
    rw [hL₃.1 _ (by simp [bSign, bandOf]) (by simp [bandOf, bLocate]) (by decide),
      R₂ _ (by decide) (by decide), h12]
  have c11 : c₃.nreg 120011 = 1 := by
    rw [hL₃.1 _ (by simp [bSign, bandOf]) (by simp [bandOf, bLocate]) (by decide),
      R₂ _ (by decide) (by decide), h11]
  obtain ⟨c₄, k₄, e₄, hk₄, v₄⟩ : ∃ c₄ k₄, Exec P W myFinish c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 120170 = (if 0 < t then t - 1 else A - 1) := by
    unfold myFinish
    by_cases h0 : 0 < t
    · exact ⟨_, _, .ifLtN_true (by rw [c12]; exact h0) (Exec.subN w₃ _ _ _), by omega,
        by config_simp; rw [c11, ite_eq_left h0]⟩
    · exact ⟨_, _, .ifLtN_false (by rw [c12]; exact h0) (Exec.subN w₃ _ _ _), by omega,
        by config_simp; rw [c11, h504, ite_eq_right h0]⟩
  have ex : Exec P W myLoc c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have f₃ := exec_frameB e₃ (B := fun r => Bcmp r || decide (50100 ≤ r ∧ r ≤ 50116)) (by decide)
  have f₄ := exec_frameB e₄ (B := fun r => decide (r = 120170)) (by decide)
  have fr : FrameB BL c c₄ :=
    (FrameB.mono f₁ fun r hr => by simp [BL, hr]).trans
      ((FrameB.mono f₂ fun r hr => by simp [BL, hr]).trans
        ((FrameB.mono f₃ fun r hr => by
          simp only [Bool.or_eq_true] at hr
          rcases hr with hr | hr <;> simp [BL, hr]).trans
          (FrameB.mono f₄ fun r hr => by simp only [decide_eq_true_eq] at hr; simp [BL, hr])))
  refine ⟨c₄, _, ex, ?_, fr, ?_, ?_⟩
  · omega
  · rw [v₄]; split_ifs <;> omega
  · rw [v₄]; exact hpick.2
end

end OracleR

end Chazelle.Core
