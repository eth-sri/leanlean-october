module

public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# The dual board graph is connected
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

theorem step_of_inner {m : Cell} (hm : m ∈ R.inner) :
    StepRel dualEnds R.inner (dualEnds m).1 (dualEnds m).2 := ⟨m, hm, Or.inl rfl⟩

/-- Every odd cell is joined to a bottom-row odd cell. -/
theorem dual_to_bottom (hw : 0 < R.w) :
    ∀ n : ℕ, ∀ z : Cell, z ∈ R.dcells → z.2 - R.y0 = n →
      ∃ b ∈ R.dcells, b.2 = R.y0 ∧ Relation.ReflTransGen (StepRel dualEnds R.inner) z b := by
  intro n
  induction n with
  | zero =>
    intro z hz hn
    exact ⟨z, hz, by omega, Relation.ReflTransGen.refl⟩
  | succ n ih =>
    intro z hz hn
    have hzc := mem_cells.1 (mem_dcells.1 hz).1
    have hzp := (mem_dcells.1 hz).2
    let d : ℤ := if R.x0 < z.1 then -1 else 1
    let m := if R.x0 < z.1 then z else (z.1 + 1, z.2)
    let z' : Cell := (z.1 + d, z.2 - 1)
    have hm : m ∈ R.inner := by rw [mem_inner]; dsimp [m]; split_ifs <;> omega
    have hends : dualEnds m = (z, z') := by
      unfold IsPrimal at hzp
      by_cases hx : R.x0 < z.1
      · simp [m, z', d, hx, dualEnds, hzp, sub_eq_add_neg]
      · have hp : (z.1 + 1 + z.2) % 2 = 0 := by omega
        simp [m, z', d, hx, dualEnds, hp]
    have hz' : z' ∈ R.dcells := by
      simp only [mem_dcells, mem_cells, IsPrimal, z', d] at *
      split_ifs <;> omega
    obtain ⟨b, hb, hb2, hr⟩ := ih z' hz' (by dsimp [z']; omega)
    have hs := R.step_of_inner hm
    rw [hends] at hs
    exact ⟨b, hb, hb2, hr.head hs⟩


/-- Two bottom-row odd cells two apart are joined through the cell between them one row up. -/
theorem bottom_step (hh : 0 < R.h) {z : Cell} (hz : z ∈ R.dcells) (hzy : z.2 = R.y0)
    (hx : z.1 + 2 ≤ R.x0 + R.w) :
    Relation.ReflTransGen (StepRel dualEnds R.inner) z (z.1 + 2, z.2) := by
  have hzc := mem_cells.1 (mem_dcells.1 hz).1
  have hzp := (mem_dcells.1 hz).2
  unfold IsPrimal at hzp
  have hm1 : (z.1 + 1, z.2 + 1) ∈ R.inner := by rw [mem_inner]; dsimp only; omega
  have hm2 : (z.1 + 2, z.2 + 1) ∈ R.inner := by rw [mem_inner]; dsimp only; omega
  have e1 : dualEnds (z.1 + 1, z.2 + 1) = ((z.1 + 1, z.2 + 1), z) := by
    unfold dualEnds; rw [ite_eq_right (by dsimp only; omega)]
    ext <;> simp
  have e2 : dualEnds (z.1 + 2, z.2 + 1) = ((z.1 + 1, z.2 + 1), (z.1 + 2, z.2)) := by
    unfold dualEnds; rw [ite_eq_left (by dsimp only; omega)]
    ext <;> simp; ring
  have s1 := R.step_of_inner hm1
  have s2 := R.step_of_inner hm2
  rw [e1] at s1
  rw [e2] at s2
  exact (Relation.ReflTransGen.single (stepRel_symm s1)).tail s2

/-- An equivalence relation valid across successive dual cells of a row is valid
between any two of its dual cells. -/
theorem rel_of_same_dual_row {r : ℤ} {rel : Cell → Cell → Prop} (hrel : Equivalence rel)
    (hstep : ∀ z ∈ R.dcells, z.2 = r → (z.1 + 2, z.2) ∈ R.dcells → rel z (z.1 + 2, z.2))
    {z z' : Cell} (hz : z ∈ R.dcells) (hz' : z' ∈ R.dcells) (hr : z.2 = r) (hr' : z'.2 = r) :
    rel z z' := by
  let rec go (x y : Cell) (hx : x ∈ R.dcells) (hy : y ∈ R.dcells)
      (hxr : x.2 = r) (hyr : y.2 = r) (hle : x.1 ≤ y.1) : rel x y := by
    have hxc := mem_dcells.1 hx
    have hyc := mem_dcells.1 hy
    simp only [mem_cells, IsPrimal] at hxc hyc
    by_cases he : x.1 = y.1
    · rw [Prod.ext he (hxr.trans hyr.symm)]
      exact hrel.refl _
    · have hlim : x.1 + 2 ≤ y.1 := by omega
      have hmid : ((x.1 + 2, x.2) : Cell) ∈ R.dcells := by
        simp only [mem_dcells, mem_cells, IsPrimal]
        omega
      exact hrel.trans (hstep x hx hxr hmid) (go _ y hmid hy hxr hyr hlim)
  termination_by (y.1 - x.1).toNat
  decreasing_by omega
  rcases le_total z.1 z'.1 with h | h
  · exact go z z' hz hz' hr hr' h
  · exact hrel.symm (go z' z hz' hz hr' hr h)

/-- The dual board graph (all inner edges) is connected. -/
theorem dual_connected (hw : 0 < R.w) (hh : 0 < R.h) {z z' : Cell} (hz : z ∈ R.dcells)
    (hz' : z' ∈ R.dcells) :
    Relation.ReflTransGen (StepRel dualEnds R.inner) z z' := by
  obtain ⟨b, hb, hby, hr⟩ := R.dual_to_bottom hw (z.2 - R.y0).toNat z hz (by
    have := mem_cells.1 (mem_dcells.1 hz).1; omega)
  obtain ⟨b', hb', hby', hr'⟩ := R.dual_to_bottom hw (z'.2 - R.y0).toNat z' hz' (by
    have := mem_cells.1 (mem_dcells.1 hz').1; omega)
  have hbb := R.rel_of_same_dual_row
    ⟨fun _ => Relation.ReflTransGen.refl, symm, Relation.ReflTransGen.trans⟩
    (fun z hz hy hz' => R.bottom_step hh hz hy (mem_cells.1 (mem_dcells.1 hz').1).2.1)
    hb hb' hby hby'
  exact hr.trans (hbb.trans (symm hr'))

end Rect

end PottsDiscontinuity.TorusCrossing
