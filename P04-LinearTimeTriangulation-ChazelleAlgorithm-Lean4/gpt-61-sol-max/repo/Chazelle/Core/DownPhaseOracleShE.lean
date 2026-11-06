module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleQPlan

/-!
# WP-M (E7-B, RAM part 12): the parameters of the sub-queries and the answer

* `setOne`, `setTwoA`, `setTwoB`: the parameters `u, sh, ee, eh, L` of the sub-queries
  (`170033 … 170037`) of `plan_one` and `plan_two`;
* `outI`: the answer of the interior shooter from the running best hit: the flag `140010`, and
  the interior-walk position `iPos` of the best hit's boundary symbolic point in `140011`,
  `140012` (`outI_exec`).
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## The programs -/

/-- One sub-query: the normalized query itself. -/
def setOne : Stmt :=
  block [.copyN 170033 170001, .copyN 170034 170002, .copyN 170035 170031, .copyN 170036 170030,
    .copyN 170037 170032]

/-- The first of two sub-queries: two edges from the start. -/
def setTwoA : Stmt :=
  block [.copyN 170033 170001, .copyN 170034 170002, .constN 170035 2, .constN 170036 0,
    .constN 170037 2]

/-- The second of two sub-queries: from the vertex `(e₁ + 2) mod n` to the end. -/
def setTwoB : Stmt :=
  .seq (block [.addN 170033 170001 170018, .constN 170034 0, .subN 170035 170031 170018,
      .copyN 170036 170030, .subN 170037 170032 170018])
    (.ifLtN 170033 170010 .skip (block [.subN 170033 170033 170010]))

/-- The answer at a vertex. -/
def outV : Stmt :=
  .seq (block [.copyN 170095 170072])
    (.seq ivF (block [.constN 140010 1, .copyN 140011 170096, .constN 140012 0]))

/-- The answer on an edge. -/
def outE : Stmt :=
  .seq (block [.copyN 170095 170072])
    (.seq iEdgeF (block [.constN 140010 1, .copyN 140011 170096, .addN 140012 170073 170011]))

/-- **The answer.** -/
def outI : Stmt :=
  .ifLtN 170070 170011 (block [.constN 140010 0]) (.ifLtN 170071 170011 outV outE)

/-- The registers the parameter blocks write. -/
def Bset (r : ℕ) : Bool := decide (170033 ≤ r ∧ r < 170038)

theorem wr_setOne : wr Bset setOne = true := by decide
theorem wr_setTwoA : wr Bset setTwoA = true := by decide
theorem wr_setTwoB : wr Bset setTwoB = true := by decide

/-- The registers the answer writes. -/
def Bout (r : ℕ) : Bool :=
  decide (140010 ≤ r ∧ r < 140013) || decide (r = 170092 ∨ r = 170095 ∨ r = 170096)

theorem wr_outI : wr Bout outI = true := by decide

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

section
variable (c : Config) (hw : WordsBounded W c)
include hw
theorem setOne_exec :
    ∃ c' k, Exec P W setOne c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = c.nreg 170031 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 ∧ FrameB Bset c c' := by
  suffices h : ∃ c' k, Exec P W setOne c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = c.nreg 170031 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameB e wr_setOne⟩
  unfold setOne
  exec_block
  ram_all

theorem setTwoA_exec (hW : 2 ≤ W) :
    ∃ c' k, Exec P W setTwoA c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = 2 ∧ c'.nreg 170036 = 0 ∧
      c'.nreg 170037 = 2 ∧ FrameB Bset c c' := by
  suffices h : ∃ c' k, Exec P W setTwoA c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = 2 ∧ c'.nreg 170036 = 0 ∧
      c'.nreg 170037 = 2 by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameB e wr_setTwoA⟩
  unfold setTwoA
  exec_block
  all_goals simp_all

section
variable (hS : SEnv P W O s c)
include hS
theorem setTwoB_exec
    (he1 : s.e₁ < P.n) :
    ∃ c' k, Exec P W setTwoB c c' k ∧ k ≤ 8 ∧ c'.nreg 170033 = (s.e₁ + 2) % P.n ∧
      c'.nreg 170034 = 0 ∧ c'.nreg 170035 = c.nreg 170031 - 2 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 - 2 ∧
      FrameB Bset c c' := by
  suffices h : ∃ c' k, Exec P W setTwoB c c' k ∧ k ≤ 8 ∧ c'.nreg 170033 = (s.e₁ + 2) % P.n ∧
      c'.nreg 170034 = 0 ∧ c'.nreg 170035 = c.nreg 170031 - 2 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 - 2 by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameB e wr_setTwoB⟩
  have hW := hS.hW
  unfold hostWords at hW
  have hn := hS.n3
  unfold setTwoB
  refine spec_seq ?_
  exec_block
  · ram_grind
  · omega
  by_cases h : s.e₁ + 2 < P.n
  · refine spec_ifLtN_true (by config_simp; ram_grind) ?_
    refine spec_skip ‹_› ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
    · rw [hS.r1, hS.r18, Nat.mod_eq_of_lt h]
    · rw [hS.r18]
    ram_grind
  · refine spec_ifLtN_false (by config_simp; ram_grind) ?_
    exec_block
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
    · rw [hS.r1, hS.r18, hS.r10, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [hS.r18]
    ram_grind

/-- **The answer of the interior shooter.** -/
theorem outI_exec {S : Set Point}
    {z : Point} {σ : ℝ} (hB : BestI P c S z σ) :
    ∃ c' k, Exec P W outI c c' k ∧ k ≤ 20 ∧
      (c'.nreg 140010 = 1 → ∃ t, FirstHit S z σ t ∧
        ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c'.nreg 140011, c'.nreg 140012⟩ ∧
        c'.nreg 140011 < (interiorModel (Qof P)).W.n ∧
        (interiorModel (Qof P)).pos (Qof P) ⟨c'.nreg 140011, c'.nreg 140012⟩ = rayPt z σ t) ∧
      (c'.nreg 140010 ≠ 1 → NoHit S z σ) ∧ FrameB Bout c c' := by
  have hQ : (Qof P).n = P.n := qn'
  have hD : DistinctHeights (Qof P) := (goodShear_epsOf hS.good.2).2.1
  have hn := hS.n3
  have hW := hS.hW
  unfold hostWords at hW
  suffices h : ∃ c' k, Exec P W outI c c' k ∧ k ≤ 20 ∧
      (c'.nreg 140010 = 1 → ∃ t, FirstHit S z σ t ∧
        ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c'.nreg 140011, c'.nreg 140012⟩ ∧
        c'.nreg 140011 < (interiorModel (Qof P)).W.n ∧
        (interiorModel (Qof P)).pos (Qof P) ⟨c'.nreg 140011, c'.nreg 140012⟩ = rayPt z σ t) ∧
      (c'.nreg 140010 ≠ 1 → NoHit S z σ) by
    obtain ⟨c', k, e, h1, h2, h3⟩ := h
    exact ⟨c', k, e, h1, h2, h3, exec_frameB e wr_outI⟩
  obtain ⟨hb1, hb2, hb3⟩ := hB
  unfold outI
  by_cases g : c.nreg 170070 < c.nreg 170011
  · refine spec_ifLtN_true g ?_
    exec_block
    · omega
    refine ⟨by omega, fun h => by simp_all, fun _ => hb3 (by ram_grind)⟩
  refine spec_ifLtN_false g ?_
  obtain ⟨sb, t, hsb, hbs, hfh, hev⟩ := hb2 (by ram_grind)
  have hbsQ := hbs
  rw [← hQ] at hn
  obtain ⟨hpp, hlt, hpos⟩ := iPos_spec hD hn hbsQ
  rw [hev] at hpos
  cases sb with
  | vtx q =>
    obtain ⟨k0, kq⟩ := hsb
    refine spec_ifLtN_true (by ram_grind) ?_
    unfold outV
    refine spec_seq ?_
    exec_block
    have w := ‹WordsBounded W { c with nreg := upd c.nreg 170095 (c.nreg 170072) }›
    obtain ⟨c₂, k₂, e₂, hk₂, rfl⟩ := ivF_exec (P := P) _ w (by config_simp; exact hS.r11)
    refine spec_seq ⟨_, k₂, e₂, ?_⟩
    have w₂ := e₂.wb_right
    exec_block
    · omega
    · omega
    have hiv : ivV (c.nreg 170014) (c.nreg 170019) (c.nreg 170072) = iv (Qof P) q := by
      rw [kq]; exact hS.ivv q
    refine ⟨by omega, fun _ => ⟨t, hfh, ?_, ?_, ?_⟩, fun h => (h (by config_simp)).elim⟩
    · config_simp; rw [hiv]; rw [hQ] at hpp; exact hpp
    · config_simp; rw [hiv, mi_n]; exact hlt
    · config_simp; rw [hiv]; exact hpos
  | onEdge e h =>
    obtain ⟨k0, ke, kh⟩ := hsb
    refine spec_ifLtN_false (by omega) ?_
    unfold outE
    refine spec_seq ?_
    exec_block
    have w := ‹WordsBounded W { c with nreg := upd c.nreg 170095 (c.nreg 170072) }›
    have he : e < P.n := by have := hbs.1; omega
    have hh : h < P.n := by have := hbs.2.1; omega
    obtain ⟨c₂, k₂, e₂, hk₂, i96, ir, im, irr, irm, io⟩ := iEdgeF_exec (P := P) _ w
      (by config_simp; exact hS.r11) (by config_simp; exact hS.r10) (by config_simp; exact hS.r19)
      (by config_simp; ram_grind)
    refine spec_seq ⟨c₂, k₂, e₂, ?_⟩
    have w₂ := e₂.wb_right
    have b73 : c₂.nreg 170073 = h := by ram_simp
    have b11 : c₂.nreg 170011 = 1 := by rw [ir _ (by decide) (by decide)]; config_simp; exact hS.r11
    have hie : c₂.nreg 170096 = iEdge (Qof P) e := by
      rw [i96]; config_simp; rw [ke, ← hS.iev e]
    exec_block
    · omega
    · omega_nf
    refine ⟨by omega, fun _ => ⟨t, hfh, ?_, ?_, ?_⟩, fun h => (h (by config_simp)).elim⟩
    · config_simp; rw [hie, b73, b11]; rw [hQ] at hpp; exact hpp
    · config_simp; rw [hie, mi_n]; exact hlt
    · config_simp; rw [hie, b73, b11]; exact hpos




end

end

end exec

end

end IOrc

end Chazelle.Core
