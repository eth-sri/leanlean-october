module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import PottsDiscontinuity.TorusLoops.HorizontalHomology

/-! Ordered periods and integer displacement of the actual dart orbits.
These are lift bookkeeping results; geometric simplicity and the turning
classification are separate statements. -/

@[expose] public noncomputable section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops

section Permutation
variable {α : Type*} [Fintype α] [DecidableEq α]

section
variable (p : Equiv.Perm α) (d : α)
/-- A full period lists each point of the selected permutation cycle once. -/
def orbitPeriodEquiv  :
    Fin (Function.minimalPeriod p d) ≃ {e : α // p.SameCycle d e} :=
  Equiv.ofBijective (fun k => ⟨p^[k.val] d,by
    simpa only [Equiv.Perm.coe_pow] using
      ((Equiv.Perm.SameCycle.refl p d).pow_right (n := k.val))⟩) (by
    constructor
    · intro k l h
      apply Fin.ext
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod k.isLt l.isLt).mp
        (congrArg Subtype.val h)
    · intro e
      obtain ⟨n,_,_,hn⟩ := Equiv.Perm.SameCycle.exists_pow_eq p e.property
      have hp := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts d)
      refine ⟨⟨n % Function.minimalPeriod p d,Nat.mod_lt _ hp⟩,?_⟩
      aesop)

/-- Summing once around a period is exactly summing over its quotient fiber. -/
theorem sum_period_eq_sum_cycle (f : α → ℤ) :
    (∑ k : Fin (Function.minimalPeriod p d), f (p^[k.val] d)) =
      ∑ e : α with p.SameCycle e d, f e := by
  have hh : (∑ e : α with p.SameCycle e d, f e) =
      ∑ e : {e : α // p.SameCycle e d}, f e.val :=
    Finset.sum_subtype _ (by simp) f
  rw [hh]
  let E : {e : α // p.SameCycle d e} ≃ {e : α // p.SameCycle e d} :=
    Equiv.subtypeEquivRight (fun _ => Equiv.Perm.sameCycle_comm)
  exact ((orbitPeriodEquiv p d).trans E).sum_comp (fun e => f e.val)
end

end Permutation

variable {N M : ℕ}

section
variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω)
/-- The least positive period of a chosen outgoing dart. -/
def loopPeriod  : ℕ :=
  Function.minimalPeriod (directedStep ω s h) d

theorem loopPeriod_pos  : 0 < loopPeriod ω s h d :=
  Function.minimalPeriod_pos_of_mem_periodicPts ((directedStep ω s h).injective.mem_periodicPts d)

/-- Position in the literal integer lift, starting at the chosen representative's
integer coordinates, after n directed edges. -/
def loopLiftPosition (n : ℕ) : ℤ × ℤ :=
  ((d.val.1.1.val : ℤ) + ∑ k ∈ range n,
      horizontalIncrement ((directedStep ω s h)^[k] d).val,
   (d.val.1.2.val : ℤ) + ∑ k ∈ range n,
      verticalIncrement ((directedStep ω s h)^[k] d).val)

theorem loopLiftPosition_zero  :
    loopLiftPosition ω s h d 0 = ((d.val.1.1.val : ℤ),(d.val.1.2.val : ℤ)) := by
  rfl

theorem loopLiftPosition_succ (n : ℕ) :
    loopLiftPosition ω s h d (n+1) = loopLiftPosition ω s h d n +
      (horizontalIncrement ((directedStep ω s h)^[n] d).val,
       verticalIncrement ((directedStep ω s h)^[n] d).val) := by
  ext <;> simp [loopLiftPosition,Finset.sum_range_succ] <;> ring

theorem loopSum_eq_sum_period (f : Dart N M → ℤ) :
    loopSum ω s h f (directedLoopOf ω s h d) =
      ∑ k ∈ range (loopPeriod ω s h d), f ((directedStep ω s h)^[k] d).val := by
  unfold loopSum
  have he (e : DirectedDart ω) : directedLoopOf ω s h e = directedLoopOf ω s h d ↔
      (directedStep ω s h).SameCycle e d := Quotient.eq
  simp_rw [he]
  rw [← sum_period_eq_sum_cycle (directedStep ω s h) d (fun e => f e.val)]
  exact Fin.sum_univ_eq_sum_range (fun k => f ((directedStep ω s h)^[k] d).val) _

/-- One lifted period has precisely the two signed seam displacements. -/
theorem loopLiftPosition_period (i : Fin N) (j : Fin M) :
    loopLiftPosition ω s h d (loopPeriod ω s h d) =
      ((d.val.1.1.val : ℤ) + (N : ℤ) * loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d),
       (d.val.1.2.val : ℤ) + (M : ℤ) * loopVertical ω s h j (directedLoopOf ω s h d)) := by
  have hx := loop_horizontal_displacement ω s h i (directedLoopOf ω s h d)
  have hy := loop_vertical_displacement ω s h j (directedLoopOf ω s h d)
  rw [loopSum_eq_sum_period] at hx hy
  exact Prod.ext (congrArg ((d.val.1.1.val : ℤ) + ·) hx)
    (congrArg ((d.val.1.2.val : ℤ) + ·) hy)

/-- Zero seam winding is exactly closure of the actual integer lift. -/
theorem loopLiftPosition_period_eq_start_iff (i : Fin N) (j : Fin M) :
    loopLiftPosition ω s h d (loopPeriod ω s h d) = loopLiftPosition ω s h d 0 ↔
      loopVertical ω s h j (directedLoopOf ω s h d) = 0 ∧
      loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d) = 0 := by
  rw [loopLiftPosition_period ω s h d i j,loopLiftPosition_zero,Prod.mk.injEq]
  have hn : (N : ℤ) ≠ 0 := by grind
  have hm : (M : ℤ) ≠ 0 := by grind
  simp
  omega
end

end PottsDiscontinuity.TorusTopology
