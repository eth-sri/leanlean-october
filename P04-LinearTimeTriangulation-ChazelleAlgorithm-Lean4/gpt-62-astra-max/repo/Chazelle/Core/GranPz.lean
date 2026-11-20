module

public import Chazelle.Core.GranRamLoop
public import Chazelle.Core.OutputNF
public import Chazelle.Core.NFLocateChain

/-!
# WP-F, init part 1: when does a walk position have a nonzero parameter

The bit `pz j` of the state (`StatOK.pz`) records whether the start of ring position `j` lies
strictly inside its walk edge.  With distinct heights of `Q` this is an index comparison:

* interior model (`pz_int`): code `h ≠ 0` and `h - 1` is not the index of the start vertex
  `wv (revOf Q) n e` of the walk edge;
* chain model, tour edge `e = i + 6` (`pz_chain`): code `h ≠ 0`, the two walk vertices (host points
  `sp₁`, `sp₂`) have different height vertices `hv`, and `h - 1 ≠ hv sp₁`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The height vertex of a symbolic point. -/
def hv : SymPt → ℕ
  | .vtx i => i
  | .onEdge _ h => h

theorem eval_snd (Q : Polygon) (sp : SymPt) : (sp.eval Q).2 = (Q.vtx (hv sp)).2 := by
  cases sp <;> rfl

theorem hv_lt {n : ℕ} {sp : SymPt} (h : sp.Lt n) : hv sp < n := by
  cases sp with
  | vtx i => exact h
  | onEdge e k => exact h.2

/-- **Interior model**: a position has a nonzero parameter iff its code names a vertex other than
the start of its walk edge. -/
theorem pz_int {Q : Polygon} (hQ : Q.Simple) (hdh : DistinctHeights Q) {e h : ℕ} (he : e < Q.n)
    (hh : h ≤ Q.n) :
    (interiorModel Q).param Q ⟨e, h⟩ ≠ 0 ↔
      (h ≠ 0 ∧ h - 1 ≠ OutWalk.wv (OutWalk.revOf Q) Q.n e) := by
  cases h with
  | zero => simp [Model.param_code_zero]
  | succ k =>
    simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, true_and, Nat.add_sub_cancel]
    constructor
    · intro hne hk
      apply hne
      rw [OutNF.param_eq hQ hdh he k, OutNF.wa_eq he, ← hk, sub_self, zero_div]
    · intro hk
      exact OutNF.param_ne_zero hQ hdh he (by omega) fun h' => hk h'.symm

/-- The walk vertices of a tour edge of the chain model. -/
theorem chain_wa_wb (C : Chain) {i : ℕ} (hi : i < 2 * C.m) :
    (chainModel C).wa (i + 6) = C.vertex (C.sideIdx C.sideBeta i) ∧
      (chainModel C).wb (i + 6) = C.vertex (C.sideIdx C.sideBeta (i + 1)) := by
  simp only [Model.wa, Model.wb, chainModel]
  rw [C.sideWalk_n, Nat.mod_eq_of_lt (by omega), show i + 6 + 1 = (i + 1) + 6 by ring,
    C.sideWalk_vtx_tour _ (by omega), C.sideWalk_vtx_tour _ (by omega)]
  exact ⟨rfl, rfl⟩

/-- **Chain model, tour edge**: a position has a nonzero parameter iff its code is nonzero, the
edge is not horizontal and the code names another height than the start of the edge. -/
theorem pz_chain (C : Chain) {Q : Polygon} (hdh : DistinctHeights Q) {i h : ℕ} (hi : i < 2 * C.m)
    (hh : h ≤ Q.n) {sp₁ sp₂ : SymPt} (h1 : C.vertex (C.sideIdx C.sideBeta i) = sp₁.eval Q)
    (h2 : C.vertex (C.sideIdx C.sideBeta (i + 1)) = sp₂.eval Q) (l1 : sp₁.Lt Q.n)
    (l2 : sp₂.Lt Q.n) :
    (chainModel C).param Q ⟨i + 6, h⟩ ≠ 0 ↔ (h ≠ 0 ∧ hv sp₁ ≠ hv sp₂ ∧ h - 1 ≠ hv sp₁) := by
  obtain ⟨ea, eb⟩ := chain_wa_wb C hi
  have ya : ((chainModel C).wa (i + 6)).2 = (Q.vtx (hv sp₁)).2 := by rw [ea, h1, eval_snd]
  have yb : ((chainModel C).wb (i + 6)).2 = (Q.vtx (hv sp₂)).2 := by rw [eb, h2, eval_snd]
  have a1 := hv_lt l1
  have a2 := hv_lt l2
  have hinj : ∀ a b, a < Q.n → b < Q.n → ((Q.vtx a).2 = (Q.vtx b).2 ↔ a = b) := fun a b ha hb =>
    ⟨fun e => by by_contra hne; exact hdh a b ha hb hne e, fun e => by rw [e]⟩
  cases h with
  | zero => simp [Model.param_code_zero]
  | succ k =>
    simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, true_and, Nat.add_sub_cancel]
    simp only [Model.param]
    rw [ya, yb]
    by_cases hab : hv sp₁ = hv sp₂
    · rw [ite_eq_left (by rw [hab])]; simp [hab]
    · rw [ite_eq_right (fun e => hab ((hinj _ _ a1 a2).1 e))]
      have hden : (Q.vtx (hv sp₂)).2 - (Q.vtx (hv sp₁)).2 ≠ 0 :=
        sub_ne_zero.2 (fun e => hab ((hinj _ _ a1 a2).1 e.symm))
      rw [div_eq_zero_iff, sub_eq_zero, hinj _ _ (by omega) a1]
      simp only [hab, not_false_eq_true, true_and]
      constructor
      · intro hn e; exact hn (Or.inl e)
      · rintro hn (e | e)
        · exact hn e
        · exact hden e

end

end Gran

end Chazelle.Core
