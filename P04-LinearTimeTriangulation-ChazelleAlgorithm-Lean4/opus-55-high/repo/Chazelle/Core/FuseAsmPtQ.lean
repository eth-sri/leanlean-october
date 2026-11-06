module

public import Chazelle.Core.FuseAsmHt

/-!
# WP-F fusion assembly, part 14: the answer to a point query

A point query `(z, σ)` of side `i` (a point `z` of `Cᵢ` not above its top, a vertex `hv` of `Q`
at the height of `z`) is answered by `arrivalPos`: either an arrival position `(e', h')`, giving
the sweep query `(e', hv + 1, ρ)` (`ptAns_some`), or none, and then `σ` is not free for `C` at
`z` (`ptAns_none`).  `PtAns` records the outcome as a list of at most one query.
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Merge (FreeAt)

variable (J : Merge.Junction) (Q : Polygon)

/-- The answer to a point query `(z, σ)` of side `i`: a list of valid queries at `z` in
direction `σ`, empty only if `σ` is not free for `C` at `z`. -/
def PtAns (i : ℕ) (z : Point) (σ : ℝ) (l : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ q ∈ l, QueryOK J Q i q ∧ HeightOK J Q i q ∧
    (chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩ = z ∧ dirOf q.2.2 = σ) ∧
    (l = [] → ¬ FreeAt J.whole z σ)

/-- The parameter of a position does not depend on the height code, among codes of the height of
its point. -/
theorem param_eq_of_pos (M : Model) {e h' hv : ℕ} {z : Point} (hpos : M.pos Q ⟨e, h'⟩ = z)
    (hhv : (Q.vtx hv).2 = z.2) : M.param Q ⟨e, hv + 1⟩ = M.param Q ⟨e, h'⟩ := by
  cases h' with
  | zero =>
    have hwa : M.wa e = z := by
      rw [← hpos]; unfold Model.pos; rw [show M.param Q ⟨e, 0⟩ = 0 from rfl, Geometry.lerp_zero]
    rw [param_of_vertex M Q e hv (by rw [hhv, hwa])]; rfl
  | succ h =>
    by_cases hh : (M.wa e).2 = (M.wb e).2
    · unfold Model.param; simp only; rw [ite_eq_left hh, ite_eq_left hh]
    · have hy : (Q.vtx h).2 = (Q.vtx hv).2 := by
        have hpos' := hpos
        unfold Model.pos Model.param at hpos'
        simp only at hpos'
        rw [ite_eq_right hh] at hpos'
        rw [hhv, ← hpos', Geometry.lerp_snd]
        have : (M.wb e).2 - (M.wa e).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hh)
        field_simp
        ring
      exact param_congr M Q e hy.symm

/-- **An arrival position gives a point query.** -/
theorem ptAns_some (i : ℕ) {e' h' ρ hv : ℕ} {z : Point}
    (hA : Sweep.Arrival (chainModel (sideChain J i)).W z (-dirOf ρ) e'
      ((chainModel (sideChain J i)).param Q ⟨e', h'⟩))
    (hhv : (Q.vtx hv).2 = z.2) (hvn : hv < Q.n) (hz2 : z.2 ≤ (sideChain J i).top.2) :
    PtAns J Q i z (dirOf ρ) [(e', hv + 1, ρ)] := by
  set M := chainModel (sideChain J i)
  have hpos : M.pos Q ⟨e', h'⟩ = z := by
    rw [SweepPrim.pos_eq_sidePt]; exact hA.2.2.2.1
  have hpar := param_eq_of_pos Q M hpos hhv
  obtain ⟨hq, hp⟩ := queryOK_of_arrival J Q i (h := hv) hA hpar (by omega) hz2
  refine ⟨fun q hq' => ?_, fun h => absurd h (by simp)⟩
  simp only [List.mem_singleton] at hq'
  subst hq'
  refine ⟨hq, ?_, hp, rfl⟩
  unfold HeightOK; simp only; rw [hp, ← hhv]; rfl

/-- **No arrival position: the direction is not free.** -/
theorem ptAns_none (hP : J.P.Simple) (i : ℕ) {ρ : ℕ} {z : Point}
    (hz : z ∈ (sideChain J i).set) (hz2 : z.2 ≤ (sideChain J i).top.2)
    (hnone : ∀ p t, ¬ Sweep.Arrival (chainModel (sideChain J i)).W z (-dirOf ρ) p t) :
    PtAns J Q i z (dirOf ρ) [] :=
  ⟨fun q hq => absurd hq (by simp), fun _ =>
    not_free_of_none J hP i (SweepPrim.dirOf_cases' ρ) hz hz2 hnone⟩

end

end FuseAsm

end Chazelle.Core
