import Mathlib.Tactic

import RequestProject.GenusLoops
import RequestProject.BarycentricCocycleDescent

/-! Exact boundary incidences and cocycle values of the genuine marked loops. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

def markedBoundaryPos (x : Fin q × Bool) (b : Bool) : Fin (8 * q) :=
  ⟨8 * x.1.val + (if x.2 then 2 else 0) + (if b then 1 else 0), by
    grind⟩

section
omit [NeZero q]
variable (x : Fin q × Bool)
  (b : Bool)
theorem markedBoundaryPos_div   :
    (markedBoundaryPos q x b).val / 2 / 4 = x.1.val := by
  grind [markedBoundaryPos]

theorem markedBoundaryPos_mod   :
    (markedBoundaryPos q x b).val / 2 % 4 = if x.2 then 1 else 0 := by
  grind [markedBoundaryPos]

theorem markedBoundaryPos_par   :
    (markedBoundaryPos q x b).val % 2 = if b then 1 else 0 := by
  grind [markedBoundaryPos]

theorem gvc_markedBoundaryPos_false  :
    gvc q (markedBoundaryPos q x false) = none := by
  rw [gvc, markedBoundaryPos_par]
  rfl

theorem gvc_markedBoundaryPos_true  :
    gvc q (markedBoundaryPos q x true) = some x := by
  aesop (add simp [gvc, markedBoundaryPos_par, markedBoundaryPos_div, markedBoundaryPos_mod])

theorem gec_markedBoundaryPos   :
    gec q (markedBoundaryPos q x b) = (x.1, x.2, b) := by
  apply Prod.ext
  · apply Fin.ext
    exact markedBoundaryPos_div q x b
  · change (decide ((markedBoundaryPos q x b).val / 2 % 4 % 2 = 1),
      xor (decide ((markedBoundaryPos q x b).val % 2 = 1))
        (decide (2 ≤ (markedBoundaryPos q x b).val / 2 % 4))) = (x.2, b)
    rw [markedBoundaryPos_mod, markedBoundaryPos_par]
    cases x.2 <;> cases b <;> rfl
end

theorem markedBoundaryPos_succ (x : Fin q × Bool) :
    markedBoundaryPos q x false + 1 = markedBoundaryPos q x true := by
  apply Fin.ext
  rw [fin_succ_val]
  have ht := (markedBoundaryPos q x true).isLt
  change (8 * x.1.val + (if x.2 then 2 else 0) + 0 + 1) % (8 * q) =
    8 * x.1.val + (if x.2 then 2 else 0) + 1
  change 8 * x.1.val + (if x.2 then 2 else 0) + 1 < 8 * q at ht
  simpa [add_zero] using Nat.mod_eq_of_lt ht

theorem gvc_markedBoundaryPos_end (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x true + 1) = none := by
  rw [gvc, if_pos]
  rw [fin_succ_val]
  have ht : (markedBoundaryPos q x true).val + 1 < 8 * q := by
    grind [markedBoundaryPos]
  rw [Nat.mod_eq_of_lt ht]
  have hpar : (markedBoundaryPos q x true).val % 2 = 1 := markedBoundaryPos_par q x true
  omega

omit [NeZero q] in
theorem gvc_endpoint (p : Fin (8 * q)) :
    gvc q p = none ∨ gvc q p = some ((gec q p).1, (gec q p).2.1) := by
  unfold gvc
  split_ifs with hp
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gvc_succ_endpoint (p : Fin (8 * q)) :
    gvc q (p + 1) = none ∨ gvc q (p + 1) = some ((gec q p).1, (gec q p).2.1) := by
  
  have hv := fin_succ_val p
  by_cases he : (p + 1).val % 2 = 0
  · exact Or.inl (by rw [gvc, if_pos he])
  · have hs : (p + 1).val = p.val + 1 := by
      rw [hv]
      apply Nat.mod_eq_of_lt
      by_contra hn
      have hn' : p.val + 1 = 8 * q := by omega
      rw [hv, hn', Nat.mod_self] at he
      exact he rfl
    
    apply Or.inr
    rw [gvc, if_neg he]
    apply congrArg some
    apply Prod.ext
    · apply Fin.ext
      change (p + 1).val / 2 / 4 = p.val / 2 / 4
      omega
    · change decide ((p + 1).val / 2 % 4 % 2 = 1) = decide (p.val / 2 % 4 % 2 = 1)
      have hhalf : (p + 1).val / 2 = p.val / 2 := by omega
      rw [hhalf]

theorem gSig_boundary_path (x : Fin q × Bool) :
    gSig q (x.1.val, x.2) =
      bdEdge (gc q) (markedBoundaryPos q x false) ++ bdEdge (gc q) (markedBoundaryPos q x true) := by
  rw [gSig, Nat.mod_eq_of_lt x.1.isLt]
  change pPath (gc q) (8 * x.1.val + (if x.2 then 2 else 0)) = _
  rw [pPath_eq]
  have h₀ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0)) =
      markedBoundaryPos q x false := by
    apply Fin.ext
    have ht := (markedBoundaryPos q x false).isLt
    simpa [cyc, markedBoundaryPos, Bool.false_eq_true, ↓reduceIte, add_zero] using
      Nat.mod_eq_of_lt ht
  have h₁ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0) + 1) =
      markedBoundaryPos q x true := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (markedBoundaryPos q x true).isLt
  rw [h₀, h₁]

variable {G : Type v} [Group G]
  (c : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

theorem read_bdEdge (p : Fin (8 * q)) :
    c.readPath (bdEdge (gc q) p) =
      (barycentricCocycle c).val (cV (gc q) p) (cE (gc q) p) *
        ((barycentricCocycle c).val (cV (gc q) (p + 1)) (cE (gc q) p))⁻¹ := by
  rw [bdEdge, OrdCocycle.readPath_append, ← revPath_edgeHop, OrdCocycle.readPath_revPath,
    barycentricCocycle_val c (cV_le_cE (gc q) p),
    barycentricCocycle_val c (cV1_le_cE (gc q) p)]

def boundaryMarkValue (d : OrdCocycle (SCell (gvc q) (gec q) (gc q)) G) (x : Fin q × Bool)  :=
  d.val (.vtx none) (.bed (x.1, x.2, false)) *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, false)))⁻¹ *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, true)) *
      (d.val (.vtx none) (.bed (x.1, x.2, true)))⁻¹)

theorem read_gSig_boundaryMarkValue (x : Fin q × Bool) :
    c.readPath (gSig q (x.1.val, x.2)) = boundaryMarkValue q (barycentricCocycle c) x := by
  aesop (add simp [gSig_boundary_path, read_bdEdge, markedBoundaryPos_succ, cV, cE, gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true, gvc_markedBoundaryPos_end, gec_markedBoundaryPos])

end FiniteChains.Davis.Genus
