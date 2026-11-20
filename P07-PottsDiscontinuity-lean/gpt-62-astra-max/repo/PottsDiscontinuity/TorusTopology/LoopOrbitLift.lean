module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import PottsDiscontinuity.TorusLoops.HorizontalHomology

/-! Ordered periods and integer displacement of the actual dart orbits.
These are lift bookkeeping results; geometric simplicity and the turning
classification are separate statements. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops

section Permutation
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (p : Equiv.Perm α) (d : α)

/-- A full period lists each point of the selected permutation cycle once. -/
noncomputable def orbitPeriodEquiv :
    Fin (Function.minimalPeriod p d) ≃ {e : α // p.SameCycle d e} :=
  Equiv.ofBijective (fun k => ⟨p^[k.val] d,by
    exact ((Equiv.Perm.SameCycle.refl p d).pow_right (n := k.val))⟩) (by
    constructor
    · intro k l h
      apply Fin.ext
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod k.isLt l.isLt).mp
        (congrArg Subtype.val h)
    · intro e
      obtain ⟨n,_,_,hn⟩ := Equiv.Perm.SameCycle.exists_pow_eq p e.property
      refine ⟨⟨n % Function.minimalPeriod p d,Nat.mod_lt _ (Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts d))⟩,?_⟩
      apply Subtype.ext
      change p^[n % Function.minimalPeriod p d] d = e.val
      rw [Function.iterate_mod_minimalPeriod_eq]
      exact hn)

/-- Summing once around a period is exactly summing over its quotient fiber. -/
theorem sum_period_eq_sum_cycle (f : α → ℤ) :
    (∑ k : Fin (Function.minimalPeriod p d), f (p^[k.val] d)) =
      ∑ e with p.SameCycle e d, f e := by
  classical
  have hh : (∑ e with p.SameCycle e d, f e) =
      ∑ e : {e : α // p.SameCycle e d}, f e.val :=
    Finset.sum_subtype _ (by simp) f
  rw [hh]
  exact ((orbitPeriodEquiv p d).trans (Equiv.subtypeEquivRight (fun _ => Equiv.Perm.sameCycle_comm))).sum_comp (fun e => f e.val)

end Permutation

variable {N M : ℕ}

section
variable {ω : ArrowConfig N M} {s : Smoothing N M} (h : CompatibleConfig ω s) (d : DirectedDart ω)
include h d

/-- The least positive period of a chosen outgoing dart. -/
noncomputable def loopPeriod : ℕ :=
  Function.minimalPeriod (directedStep h) d

lemma loopPeriod_pos : 0 < loopPeriod h d :=
  Function.minimalPeriod_pos_of_mem_periodicPts ((directedStep h).injective.mem_periodicPts d)

/-- Position in the literal integer lift, starting at the chosen representative's
integer coordinates, after n directed edges. -/
noncomputable def loopLiftPosition (n : ℕ) : ℤ × ℤ :=
  (d.val.1.1.val + ∑ k ∈ range n,
      horizontalIncrement ((directedStep h)^[k] d).val,
   d.val.1.2.val + ∑ k ∈ range n,
      verticalIncrement ((directedStep h)^[k] d).val)

end

variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω)
    (i : Fin N) (j : Fin M)

lemma loopLiftPosition_zero :
    loopLiftPosition h d 0 = (↑d.val.1.1.val,↑d.val.1.2.val) := by
  simp [loopLiftPosition]

lemma loopLiftPosition_succ (n : ℕ) :
    loopLiftPosition h d (n+1) = loopLiftPosition h d n +
      (horizontalIncrement ((directedStep h)^[n] d).val,
       verticalIncrement ((directedStep h)^[n] d).val) := by
  ext <;> simp [loopLiftPosition,Finset.sum_range_succ] <;> ring

lemma loopSum_eq_sum_period (f : Dart N M → ℤ) :
    loopSum f (directedLoopOf h d) =
      ∑ k ∈ range (loopPeriod h d), f ((directedStep h)^[k] d).val := by
  classical
  unfold loopSum
  have he (e : DirectedDart ω) : directedLoopOf h e = directedLoopOf h d ↔
      (directedStep h).SameCycle e d := Quotient.eq
  simp_rw [he]
  rw [← sum_period_eq_sum_cycle _ d (fun e => f e.val)]
  exact Fin.sum_univ_eq_sum_range (fun k => f ((directedStep h)^[k] d).val) _

/-- One lifted period has precisely the two signed seam displacements. -/
theorem loopLiftPosition_period :
    loopLiftPosition h d (loopPeriod h d) =
      (d.val.1.1.val + N * loopSum (horizontalCross i) (directedLoopOf h d),
       d.val.1.2.val + M * loopVertical j (directedLoopOf h d)) := by
  have hx := loop_horizontal_displacement h i (directedLoopOf h d)
  have hy := loop_vertical_displacement h j (directedLoopOf h d)
  rw [loopSum_eq_sum_period] at hx hy
  exact Prod.ext (congrArg ((d.val.1.1.val : ℤ) + ·) hx)
    (congrArg ((d.val.1.2.val : ℤ) + ·) hy)

/-- Zero seam winding is exactly closure of the actual integer lift. -/
theorem loopLiftPosition_period_eq_start_iff :
    loopLiftPosition h d (loopPeriod h d) = loopLiftPosition h d 0 ↔
      loopVertical j (directedLoopOf h d) = 0 ∧
      loopSum (horizontalCross i) (directedLoopOf h d) = 0 := by
  rw [loopLiftPosition_period ω s h d i j,loopLiftPosition_zero,Prod.mk.injEq]
  have hn : (N : ℤ) ≠ 0 := by grind
  have hm : (M : ℤ) ≠ 0 := by grind
  simp only [add_eq_left,mul_eq_zero,hn,hm,false_or]
  exact and_comm

end PottsDiscontinuity.TorusTopology
