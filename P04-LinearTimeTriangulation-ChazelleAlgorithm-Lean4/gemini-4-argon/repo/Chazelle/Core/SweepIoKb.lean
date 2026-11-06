module

public import Chazelle.Core.SweepIoSym

/-!
# The sweep RAM (WP-D), answers: symbolic points and sign tests from the run-step framework

* `callSym dsc re rh o`: the symbolic point of a tour or top position (`symKey_meets`) into
  `o + 1 … o + 3` (flag `o`).
* `callKb a b op o`: the sign-kernel bit `SignTest op (eval a) (eval b) (eval a)` of the symbolic
  points in `a … a + 2` and `b … b + 2` into `o` (`kbit`, with a `Meets` contract `kbit_meets`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim SignK
open Chazelle.Visibility (rayPt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The symbolic point of a position -/

/-- `absKey` on the descriptor `dsc` and the position `(re, rh)`, outputs into `o … o + 3`. -/
def callSym (dsc re rh o : ℕ) : Stmt :=
  callP [(50200, dsc), (50201, re), (50202, rh)] absKey
    [(o, 50210), (o + 1, 50211), (o + 2, 50212), (o + 3, 50213)]

theorem symPtIn_copy {c c' : Config} {r r' : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) : SymPtIn c' r' s := by
  cases s with
  | vtx i => obtain ⟨a, b⟩ := h; exact ⟨h0.trans a, h1.trans b⟩
  | onEdge e hh => obtain ⟨a, b, d⟩ := h; exact ⟨h0.trans a, h1.trans b, h2.trans d⟩

set_option maxRecDepth 20000 in
/-- **The symbolic point of a tour or top position.** -/
theorem callSym_irs {dsc re rh o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000)
    (ho : 240700 ≤ o ∧ o + 3 < 250000)
    (he : c.nreg re < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg re, c.nreg rh⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨c.nreg re, c.nreg rh⟩).2| < C.radius)
    (hcls : (6 ≤ c.nreg re ∧ c.nreg re < 2 * C.m + 6) ∨
      (c.nreg re = 2 * C.m + 6 ∧ (chainModel C).param (Qof P) ⟨c.nreg re, c.nreg rh⟩ = 0))
    (hroom : c.nreg ALLOC + 16707 ≤ W) :
    IRS P W c₀ (callSym dsc re rh o) c 16707
      (fun c' => ∃ sp : SymPt, SymPtIn c' (o + 1) sp ∧ sp.Lt P.n ∧
          sp.eval (Qof P) = (chainModel C).pos (Qof P) ⟨c.nreg re, c.nreg rh⟩ ∧
        (∀ r, bandOf r ∉ oracleBands → (r < o ∨ o + 3 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(50200, dsc), (50201, re), (50202, rh)])
    (outs := [(o, 50210), (o + 1, 50211), (o + 2, 50212), (o + 3, 50213)]) symKey_meets
    primBands_oracle hI
    (nodup3 (by norm_num) (by norm_num) (by norm_num))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨band5_oracle (by norm_num) (by norm_num), band5_oracle (by norm_num) (by norm_num),
          band5_oracle (by norm_num) (by norm_num)⟩)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g0, g1, g2⟩ := e1
      have hctx₁ := hctx.transport g0 (fun a _ => by rw [hm]) (by rw [hA])
      refine primPre_of hctx₁ ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · rwa [g1]
      · rwa [g1, g2]
      · rwa [g1, g2]
      · rw [hm, g0]; exact hctx.hostReg
      · rwa [g1, g2])
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g0, g1, g2⟩ := e1
  obtain ⟨k0, k1, k2, k3⟩ := f1
  obtain ⟨H, hC, -⟩ := hctx.2.2.2.1
  have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 50200) (Qof P) H C := by rwa [hm, g0]
  obtain ⟨-, sp, hsp, hlt, hev⟩ := hpost H C hC₁
  rw [g1, g2] at hev
  refine ⟨sp, symPtIn_copy hsp k1 (by rw [show o + 1 + 1 = o + 2 by omega, k2])
    (by rw [show o + 1 + 2 = o + 3 by omega, k3]), hlt, hev, fun r hr h0 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega)
    hra, hA, hm'⟩

/-! ## One sign test -/

/-- The precondition of a kernel bit at the slots `10500`, `10503`, `10506`. -/
def KbPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ P.n + 3 ≤ W ∧ ∃ sa sb sd : SymPt, SymPtIn c 10500 sa ∧ SymPtIn c 10503 sb ∧
    SymPtIn c 10506 sd ∧ sa.Lt P.n ∧ sb.Lt P.n ∧ sd.Lt P.n

/-- The postcondition of a kernel bit. -/
def KbPost (op : ℕ) (_P : Polygon) (c c' : Config) : Prop :=
  c'.nreg 10520 ≤ 1 ∧ ∀ sa sb sd : SymPt, SymPtIn c 10500 sa → SymPtIn c 10503 sb →
    SymPtIn c 10506 sd → (c'.nreg 10520 = 1 ↔ SignTest op (sa.eval (Qof _P)) (sb.eval (Qof _P))
      (sd.eval (Qof _P)))

/-- **Contract of one kernel bit** (at most `241` steps). -/
theorem kbit_meets {op : ℕ} (hop : op ≤ 3) :
    Meets (kbit 10500 10503 10506 op 10520) {bSign} KbPre (KbPost op) (fun _ _ => 241) := by
  intro P W c hw ⟨hG, hW, sa, sb, sd, ha, hb, hd, la, lb, ld⟩ _
  obtain ⟨c', k, ex, hk, hfr, hle, hiff⟩ := kbit_exec (a := 10500) (b := 10503) (d := 10506)
    (op := op) (dst := 10520) hG hW c hw (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hop la lb ld ha hb hd
  refine ⟨c', k, ex, hk, ⟨hle, fun sa' sb' sd' ha' hb' hd' => ?_⟩, NFLoc.frame_of_frameB hfr
    (fun r hr => ?_) k⟩
  · rwa [symPtIn_unique ha' ha, symPtIn_unique hb' hb, symPtIn_unique hd' hd]
  · simp only [Bkb, WalkKey.Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
    refine ⟨?_, ?_⟩
    · have : bandOf r = 1 := by unfold bandOf; rcases hr with h | h <;> omega
      rw [this]; decide
    · unfold ALLOC; rcases hr with h | h <;> omega

/-- The sign test `op` of the symbolic points at `a` and `b` into `o`. -/
def callKb (a b op o : ℕ) : Stmt :=
  callP [(10500, a), (10501, a + 1), (10502, a + 2), (10503, b), (10504, b + 1), (10505, b + 2),
    (10506, a), (10507, a + 1), (10508, a + 2)] (kbit 10500 10503 10506 op 10520) [(o, 10520)]

theorem bSign_oracle {r : ℕ} (h1 : 10000 ≤ r) (h2 : r < 20000) : bandOf r ∈ oracleBands := by
  have : bandOf r = 1 := by unfold bandOf; omega
  rw [this]; decide

set_option maxRecDepth 20000 in
/-- **One sign test.** -/
theorem callKb_irs {a b op o : ℕ} (hop : op ≤ 3) (hI : IInv W c₀ c) (hG : GoodEnv P)
    (hW : P.n + 3 ≤ W) (ha : 240000 ≤ a ∧ a + 2 < 250000) (hb : 240000 ≤ b ∧ b + 2 < 250000)
    (ho : 240700 ≤ o ∧ o < 250000) {sa sb : SymPt} (hsa : SymPtIn c a sa)
    (hsb : SymPtIn c b sb) (hla : sa.Lt P.n) (hlb : sb.Lt P.n)
    (hroom : c.nreg ALLOC + 251 ≤ W) :
    IRS P W c₀ (callKb a b op o) c 251 (fun c' =>
      c'.nreg o ≤ 1 ∧
      (c'.nreg o = 1 ↔ SignTest op (sa.eval (Qof P)) (sb.eval (Qof P)) (sa.eval (Qof P))) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(10500, a), (10501, a + 1), (10502, a + 2), (10503, b), (10504, b + 1),
      (10505, b + 2), (10506, a), (10507, a + 1), (10508, a + 2)])
    (outs := [(o, 10520)]) (kbit_meets hop) (by decide) hI
    (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact bSign_oracle (by norm_num) (by norm_num))
    (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := e1
      exact ⟨hG, hW, sa, sb, sa, symPtIn_copy hsa g0 g1 g2, symPtIn_copy hsb g3 g4 g5,
        symPtIn_copy hsa g6 g7 g8, hla, hlb, hla⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := e1
  obtain ⟨hle, hiff⟩ := hpost
  have := hiff sa sb sa (symPtIn_copy hsa g0 g1 g2) (symPtIn_copy hsb g3 g4 g5)
    (symPtIn_copy hsa g6 g7 g8)
  refine ⟨by rwa [f1], by rw [f1]; exact this, fun r hr h0 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        exact h0) hra, hA, hm'⟩

end

end SweepIo

end Chazelle.Core
