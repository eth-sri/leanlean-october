module

public import Chazelle.Core.RestoreNodeEndMath
public import Chazelle.Core.RestoreFEndP

/-!
# WP-E, the search: the candidate at a node chord end

The host position `((g + d) mod n, code)` of a node chord end `(g' + d, h + 1)` in the edge range
is a candidate the test accepts (`CandOK`) with height vertex `h`, in both directions.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sidePt SideAttach sideInArc)

variable {E : FEnv} {c₀ : Config} {Cα : Chain} {g g' L : ℕ}

theorem pos_of_param {M : Model} {Q : Polygon} {e a b : ℕ} (h : M.param Q ⟨e, a⟩ = M.param Q ⟨e, b⟩) :
    M.pos Q ⟨e, a⟩ = M.pos Q ⟨e, b⟩ := by
  show Geometry.lerp (M.wa e) (M.wb e) (M.param Q ⟨e, a⟩) =
    Geometry.lerp (M.wa e) (M.wb e) (M.param Q ⟨e, b⟩)
  rw [h]

/-- **The candidate at a node chord end.** -/
theorem end_cand (hE : FGood E c₀) (hS : Stretch E.M Cα g g' L) {c : Set Point} {h : ℕ} {d : ℕ}
    (hd : d < L) (hpe : PosOK Cα (Qof E.P) E.P.n ⟨g' + d, h + 1⟩)
    (hA : SideAttach (chainModel Cα).W c (g' + d) ((chainModel Cα).param (Qof E.P) ⟨g' + d, h + 1⟩))
    (hc : ∀ z ∈ c, z.2 = ((Qof E.P).vtx h).2)
    (hr : InRange c₀ ((g + d) % E.M.W.n)) {σb : ℕ} (hσb : σb ≤ 1) :
    CandOK E ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ h σb := by
  set t := (chainModel Cα).param (Qof E.P) ⟨g' + d, h + 1⟩ with ht
  obtain ⟨-, ⟨ht0, ht1, hhn⟩, -⟩ := hpe
  have hn : 0 < E.M.W.n := by have := hS.hg; omega
  -- the parameter and the point
  have hpar : E.M.param (Qof E.P) ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ = t ∧
      E.M.pos (Qof E.P) ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ =
        (chainModel Cα).pos (Qof E.P) ⟨g' + d, h + 1⟩ := by
    rw [endM_param hS hd, endM_pos hS hd]
    unfold endCode
    split_ifs with hk
    · exact ⟨rfl, rfl⟩
    · have h0 : t = 0 := by
        rw [key_pz] at hk; push Not at hk; exact le_antisymm hk ht0
      have e : (chainModel Cα).param (Qof E.P) ⟨g' + d, 0⟩ =
          (chainModel Cα).param (Qof E.P) ⟨g' + d, h + 1⟩ := by
        rw [← ht, h0]; rfl
      exact ⟨by rw [e], pos_of_param e⟩
  obtain ⟨hp, hpos⟩ := hpar
  have hy : ((Qof E.P).vtx h).2 = (E.M.pos (Qof E.P)
      ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩).2 := by
    rw [hpos, pos_eq_sidePt]
    exact (hc _ hA.2.2.2.1).symm
  have hcode : endCode Cα (Qof E.P) (g' + d) (h + 1) ≤ E.P.n := by
    unfold endCode; split_ifs <;> omega
  have hpp : ProperPos E.M (Qof E.P) E.P.n
      ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ :=
    ⟨by rwa [hp], by rwa [hp], hcode⟩
  refine ⟨Nat.mod_lt _ hn, hpp, ?_, fun C hM => ?_, by simp only at hhn; omega, hy, hσb⟩
  · have hp' := hp
    unfold endCode at hp' ⊢
    split_ifs at hp' ⊢ with hk
    · right; rw [hp']; rwa [key_pz] at hk
    · left; rfl
  · exact hE.ehr _ _ (Nat.mod_lt _ hn) hr.1 hr.2 hpp C hM

end

end Restore

end Chazelle.Core
