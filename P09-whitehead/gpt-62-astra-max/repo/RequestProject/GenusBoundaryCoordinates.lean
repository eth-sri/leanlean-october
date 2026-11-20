module

public import RequestProject.GenusLoops
public import RequestProject.BarycentricCocycleDescent

@[expose] public section

/-! Exact boundary incidences and cocycle values of the genuine marked loops. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

variable (x : Fin q × Bool)

variable (b : Bool)

def markedBoundaryPos : Fin (8 * q) :=
  ⟨8 * x.1.val + (if x.2 then 2 else 0) + (if b then 1 else 0), by
    grind⟩

omit [NeZero q] in
theorem markedBoundaryPos_div :
    (markedBoundaryPos q x b).val / 2 / 4 = x.1.val := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem markedBoundaryPos_mod :
    (markedBoundaryPos q x b).val / 2 % 4 = if x.2 then 1 else 0 := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem markedBoundaryPos_par :
    (markedBoundaryPos q x b).val % 2 = if b then 1 else 0 := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem gvc_markedBoundaryPos_false :
    gvc q (markedBoundaryPos q x false) = none := by
  simp [gvc, markedBoundaryPos_par]

omit [NeZero q] in
theorem gvc_markedBoundaryPos_true :
    gvc q (markedBoundaryPos q x true) = some x := by
  rw [gvc, markedBoundaryPos_par]
  apply congrArg some
  apply Prod.ext
  · apply Fin.ext
    apply markedBoundaryPos_div
  · rw [markedBoundaryPos_mod]
    grind

omit [NeZero q] in
theorem gec_markedBoundaryPos (b : Bool) :
    gec q (markedBoundaryPos q x b) = (x.1, x.2, b) := by
  apply Prod.ext
  · apply Fin.ext
    apply markedBoundaryPos_div
  · change (decide ((markedBoundaryPos q x b).val / 2 % 4 % 2 = 1),
      xor _
        _) = (x.2, b)
    rw [markedBoundaryPos_mod, markedBoundaryPos_par] <;> aesop

theorem markedBoundaryPos_succ :
    markedBoundaryPos q x false + 1 = markedBoundaryPos q x true := by
  apply Fin.ext
  rw [fin_succ_val]
  have ht := (markedBoundaryPos q x true).isLt
  change (8 * x.1.val + (if x.2 then 2 else 0) + 0 + 1) % (8 * q) =
    8 * x.1.val + (if x.2 then 2 else 0) + 1
  change 8 * x.1.val + (if x.2 then 2 else 0) + 1 < 8 * q at ht
  simpa only [add_zero] using Nat.mod_eq_of_lt ht

theorem gvc_markedBoundaryPos_end :
    gvc q (markedBoundaryPos q x true + 1) = none := by
  rw [gvc, if_pos]
  rw [fin_succ_val]
  have ht : (markedBoundaryPos q x true).val + 1 < 8 * q := by
    obtain ⟨h, t⟩ := x
    cases t <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega
  rw [Nat.mod_eq_of_lt ht]
  grind [markedBoundaryPos_par]

variable (p : Fin (8 * q))

omit [NeZero q] in
theorem gvc_endpoint :
    gvc q p = none ∨ gvc q p = some ((gec q p).1, (gec q p).2.1) := by
  unfold gvc
  split_ifs with hp
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gvc_succ_endpoint :
    gvc q (p + 1) = none ∨ gvc q (p + 1) = some ((gec q p).1, (gec q p).2.1) := by
  have hv := fin_succ_val p
  by_cases he : (p + 1).val % 2 = 0
  · simp_all [gvc, if_pos]
  · have hs : (p + 1).val = p.val + 1 := by
      rw [hv]
      apply Nat.mod_eq_of_lt
      by_contra hn
      have hn' : p.val + 1 = 8 * q := by omega
      simp_all
    apply Or.inr
    rw [gvc, if_neg he]
    apply congrArg some
    apply Prod.ext
    · apply Fin.ext
      change (p + 1).val / 2 / 4 = p.val / 2 / 4
      omega
    · change decide ((p + 1).val / 2 % 4 % 2 = 1) = decide (p.val / 2 % 4 % 2 = 1)
      have hhalf : (p + 1).val / 2 = p.val / 2 := by omega
      simp [hhalf]

theorem gSig_boundary_path (x : Fin q × Bool) :
    gSig q (x.1.val, x.2) =
      bdEdge (gc q) (markedBoundaryPos q x false) ++ bdEdge (gc q) (markedBoundaryPos q x true) := by
  rw [gSig, Nat.mod_eq_of_lt x.1.isLt]
  change pPath (gc q) _ = _
  rw [pPath_eq]
  have h₀ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0)) =
      markedBoundaryPos q x false := by
    apply Fin.ext
    simpa only [cyc, markedBoundaryPos, Bool.false_eq_true, ↓reduceIte, add_zero] using
      Nat.mod_eq_of_lt (markedBoundaryPos q x false).isLt
  have h₁ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0) + 1) =
      markedBoundaryPos q x true := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (markedBoundaryPos q x true).isLt
  simp_all

universe v
variable {G : Type v} [Group G]
  (c : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

theorem read_bdEdge (p : Fin _) :
    c.readPath (bdEdge (gc q) p) =
      (barycentricCocycle c).val (cV (gc q) p) (cE (gc q) p) *
        ((barycentricCocycle c).val (cV (gc q) (p + 1)) (cE (gc q) p))⁻¹ := by
  rw [bdEdge, OrdCocycle.readPath_append, ← revPath_edgeHop, OrdCocycle.readPath_revPath,
    barycentricCocycle_val c _,
    barycentricCocycle_val c _]

def boundaryMarkValue (d : OrdCocycle (SCell (gvc q) (gec q) (gc q)) G) (x : Fin q × Bool) :=
  d.val (.vtx none) (.bed (x.1, x.2, false)) *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, false)))⁻¹ *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, true)) *
      (d.val (.vtx none) (.bed (x.1, x.2, true)))⁻¹)

theorem read_gSig_boundaryMarkValue (x : Fin q × Bool) :
    c.readPath (gSig q (x.1.val, x.2)) = boundaryMarkValue q (barycentricCocycle c) x := by
  rw [gSig_boundary_path, OrdCocycle.readPath_append, read_bdEdge, read_bdEdge,
    markedBoundaryPos_succ]
  simp [cV, cE, gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true, gvc_markedBoundaryPos_end, gec_markedBoundaryPos, boundaryMarkValue, toS]

end FiniteChains.Davis.Genus
