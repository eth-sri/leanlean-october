module

public import Chazelle.Core.GranPzExec

/-!
# WP-F, init part 4: the ring position of a chord end

`posStmt` is double identification (`NFLoc.locStmt locDir`) stopped after the binary search:
for a query position `x` (in `lr 2`, `lr 3`) with a nonzero height code whose key is a cut of
the normal form `N`, the partition point `t` of the search is one past the position `j` of the
sequence table with start key `key x`; `posStmt` leaves `j = t - 1` in `r116` (`pos_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc

@[expose] public section

/-- **The position of a cut key** in the sequence table: one past it in `lr 105`. -/
def posStmt : Stmt := .seq locDir (.seq locSetup (searchStmt keyCmp))

/-- The partition point is one past the position of the key. -/
theorem pos_pick {M : Model} {Q : Polygon} {N : NF} (hNF : IsNF M Q N) (hne : (N.F M Q).Nonempty)
    (hGM : GoodModel M) {x : WPos} (hx1 : x.hgt ≠ 0) (hcut : M.IsCut (N.F M Q) (M.key Q x))
    {t : ℕ} (ht : t ≤ N.arcs.length)
    (hpre : ∀ i, i < t → KeyPred M Q x (N.arc (N.seq.getD i 0)).s)
    (hpost : t < N.arcs.length → ¬ KeyPred M Q x (N.arc (N.seq.getD t 0)).s) :
    0 < t ∧ t - 1 < N.arcs.length ∧ pk M Q N (t - 1) = M.key Q x := by
  obtain ⟨j, hj, hjk⟩ := cut_pk hNF hGM hcut
  have kp : ∀ i, KeyPred M Q x (N.arc (N.seq.getD i 0)).s ↔ pk M Q N i ≤ M.key Q x := by
    intro i; unfold KeyPred pk; rw [ite_eq_right hx1]
  have htj : t = j + 1 := by
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · -- `t ≤ j`
      have := hpost (by omega)
      rw [kp] at this
      apply this
      rw [← hjk]
      rcases Nat.lt_or_eq_of_le (show t ≤ j by omega) with h' | h'
      · exact (pk_strict hNF hne h' hj).le
      · rw [h']
    · have := (kp _).1 (hpre (j + 1) h)
      rw [← hjk] at this
      exact absurd this (not_le.2 (pk_strict hNF hne (Nat.lt_succ_self j) (by omega)))
  subst htj
  exact ⟨by omega, by simpa using hj, by simpa using hjk⟩

theorem pos_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hD : LocDPre P W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    {M : Model} {N : NF} (hM : ModelDescAt c.nmem (c.nreg 50000) (Qof P) M) (hGM : GoodModel M)
    (hN : NFAt c.nmem (c.nreg 50001) N) (hNF : IsNF M (Qof P) N) (hne : (N.F M (Qof P)).Nonempty)
    (hx : ProperPos M (Qof P) P.n ⟨c.nreg 50002, c.nreg 50003⟩) (hx1 : c.nreg 50003 ≠ 0)
    (hcut : M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩))
    (hst : ∀ j, j < N.arcs.length → ProperPos M (Qof P) P.n (N.arc j).s)
    (hB : c.nreg 50001 + 7 ≤ c.nreg ALLOC)
    (hAB : c.nmem (c.nreg 50001 + 4) + 5 * N.arcs.length ≤ c.nreg ALLOC)
    (hSB : c.nmem (c.nreg 50001 + 6) + N.arcs.length ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + locCost 5100 N.arcs.length ≤ W) :
    ∃ c' k, Exec P W posStmt c c' k ∧ k ≤ locCost 5100 N.arcs.length ∧
      Frame {bLocate, bSign} c c' k ∧ 0 < c'.nreg 50105 ∧ c'.nreg 50105 - 1 < N.arcs.length ∧
      pk M (Qof P) N (c'.nreg 50105 - 1) = M.key (Qof P) ⟨c.nreg 50002, c.nreg 50003⟩ := by
  set B := c.nreg 50001 with hBdef
  set A := N.arcs.length with hAdef
  set AB := c.nmem (B + 4) with hABdef
  set SB := c.nmem (B + 6) with hSBdef
  set x : WPos := ⟨c.nreg 50002, c.nreg 50003⟩ with hxdef
  set A₀ := c.nreg ALLOC with hA₀
  have hA1 : c.nmem (B + 1) = A := hN.2.1
  have hsl : N.seq.length = A := seq_length hNF
  have hseq : ∀ i, i < A → c.nmem (SB + i) = N.seq.getD i 0 := fun i hi =>
    hN.2.2.2.2.2.2.2.2.1 i (by omega)
  have hA0 : 0 < A := by
    obtain ⟨j, hj, -⟩ := cut_pk hNF hGM hcut
    omega
  have hL : 1 ≤ Nat.clog 2 A + 1 := by omega
  have hcostW : c.nreg ALLOC + (5100 + 20 + searchCost 275 A) ≤ W := by
    have : 5100 + 20 + searchCost 275 A ≤ locCost 5100 A := by
      unfold locCost searchCost
      omega
    omega
  -- 1. the direction
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hd₁⟩ := locDir_ok P W c hw hD
  have d₁ := hd₁ M hM
  have w₁ := e₁.wb_right
  have b1 : c₁.nreg 50001 = B := f₁.1 _ (by decide)
  have b2 : c₁.nreg 50002 = c.nreg 50002 := f₁.1 _ (by decide)
  have b3 : c₁.nreg 50003 = c.nreg 50003 := f₁.1 _ (by decide)
  have al₁ : c₁.nreg ALLOC = A₀ := f₁.1 _ (by decide)
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
  have al₂ : c₂.nreg ALLOC = A₀ := (f₂.1 _ (by decide)).trans al₁
  have m₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans m₁
  -- 3. the search
  set d := dirCode M x.edge with hd
  have hJ₂ : CmpJ x d AB A SB A₀ c.nmem c₂ :=
    ⟨q500, q501, by rw [q502, d₁], q503, q504, q505, fun a _ => by rw [m₂]⟩
  have hcmp := keyCmp_predOK hG hW x hx.2.2 d AB A SB A₀ c.nmem hAB (by omega)
  have hpr : ∀ i, i < A → (cmpPr P x d AB A c.nmem (c.nmem (SB + i)) = true ↔
      KeyPred M (Qof P) x (N.arc (N.seq.getD i 0)).s) := fun i hi => by
    rw [hseq i hi]
    exact cmpPr_eq hN x hx hst (seq_lt hNF hi)
  obtain ⟨c₃, k₃, e₃, hk₃, hJ₃, hF₃, ht₃, hpre₃, hpost₃⟩ := searchStmt_exec hcmp
    (by decide) w₂ hJ₂ (by rw [al₂]; exact cmpJ_stable x d AB A SB A₀ c.nmem)
    (by rw [q103, q104, al₂]; exact hSB)
    (fun i j hij hj hprj => by
      rw [q103, m₂] at hprj ⊢
      rw [q104] at hj
      exact (hpr i (by omega)).2 (KeyPred.mono ((hpr j hj).1 hprj) (seq_sorted hNF hij hj)))
    (by rw [al₂, q104]; omega)
  rw [q104] at ht₃ hk₃ hpost₃
  rw [q103, m₂] at hpre₃ hpost₃
  set t := c₃.nreg 50105 with htdef
  obtain ⟨tpos, tlt, tpk⟩ := pos_pick hNF hne hGM (x := x) hx1 hcut ht₃
    (fun i hi => (hpr i (by omega)).1 (hpre₃ i hi))
    (fun hi hk => by
      have := (hpr t hi).2 hk
      rw [hpost₃ hi] at this
      exact Bool.false_ne_true this)
  have F₁ := frame_of_frameB f₁ Bdir_band k₁
  have F₂ := frame_of_frameB f₂ Bloc_band k₂
  refine ⟨_, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ?_,
    (F₁.trans (F₂.trans hF₃)).mono (by simp) le_rfl, tpos, tlt, tpk⟩
  have : 5100 + 20 + searchCost 275 A ≤ locCost 5100 A := by
    unfold locCost searchCost
    omega
  omega

end

end Gran

end Chazelle.Core
