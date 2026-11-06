module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordPartition

/-!
# Root-incident fibers as the canonical T₁ index

The condition that every ML edge of a nonconstant word touches the root slot
is exactly the good fiber represented by one root-incident term index.
-/

@[expose] public noncomputable section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Raw data for a permutation, word, and root slot. -/
abbrev RootFiberRawData (n : ℕ) :=
  Fin (n + 1) × (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool))

/-- A nonconstant word fiber for which every ML edge touches the root slot. -/
def RootIncidentFiberPredicate {n : ℕ} (l : Fin (n + 1))
    (d : RootFiberRawData n) : Prop :=
  d.2.1 d.1 = l ∧
    d.2.2 ≠ (fun _ => true) ∧ d.2.2 ≠ (fun _ => false) ∧
      ∀ a, d.2.2 a = false → d.2.2 (finRotate (n + 1) a) = true →
        d.1 = a ∨ d.1 = finRotate (n + 1) a

/-- Root-slot data satisfying the unique-root-incident ML condition. -/
abbrev RootIncidentFiberTermIndex (n : ℕ) (l : Fin (n + 1)) :=
  {d : RootFiberRawData n // RootIncidentFiberPredicate l d}

section
variable {n : ℕ} {l : Fin (n + 1)}
include l
/-- Forget the marked edge and endpoint side of a root-incident index. -/
def rootIncidentFiberUnderlying (i : RootIncidentTermIndex n l) : RootIncidentFiberTermIndex n l := by
  let r := if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge
  have htrue : i.w ≠ fun _ => true := by
    intro h
    have := congrFun h (t1EdgeLeft i.edge)
    rw [i.hleft] at this
    simp_all
  have hfalse : i.w ≠ fun _ => false := by
    intro h
    have := congrFun h (t1EdgeRight i.edge)
    rw [i.hright] at this
    simp_all
  have hAll : ∀ a, i.w a = false → i.w (finRotate (n + 1) a) = true →
      r = a ∨ r = finRotate (n + 1) a := by
    intro a ha hb
    have hEdge := i.hunique a ha hb
    cases hs : i.side
    · right
      calc
        r = t1EdgeRight i.edge := by grind
        _ = finRotate (n + 1) (t1EdgeLeft i.edge) :=
          (t1EdgeLeft_rotate i.edge).symm
        _ = finRotate (n + 1) a := by simp_all
    grind
  exact ⟨(r, (i.σ.1, i.w)), ⟨i.σ.2, htrue, hfalse, hAll⟩⟩

/-- The forgotten raw data are injective on root-incident indices. -/
theorem rootIncidentFiberUnderlying_injective (hn : 0 < n) :
    Function.Injective (rootIncidentFiberUnderlying (n := n) (l := l)) := by
  intro i j hij
  apply rootIncidentUnderlying_injective hn
  have hraw := congrArg Subtype.val hij
  apply Prod.ext
  · exact congrArg (fun d : RootFiberRawData n => d.2.1) hraw
  · exact congrArg (fun d : RootFiberRawData n => d.2.2) hraw

/-- Every good root-slot fiber determines its unique marked ML edge and its
root endpoint orientation. -/
theorem rootIncidentFiberUnderlying_surjective  :
    Function.Surjective (rootIncidentFiberUnderlying (n := n) (l := l)) := by
  intro q
  rcases q with ⟨⟨r, σ, w⟩, ⟨hσ, hL, hM, hAll⟩⟩
  let σ' : RootSlotPerm l r := ⟨σ, hσ⟩
  obtain ⟨i, hiσ, hiw⟩ :=
    exists_rootIncidentTerm_of_allMLIncident r σ' w hL hM hAll
  have hslot : (if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge) = r := by
    apply σ.injective
    grind
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · tauto
  · apply Prod.ext
    · tauto
    tauto

/-- Good nonconstant root-slot fibers are in bijection with the root-incident
T₁ term indices. -/
def rootIncidentFiberEquiv (hn : 0 < n) : RootIncidentTermIndex n l ≃ RootIncidentFiberTermIndex n l :=
  Equiv.ofBijective (rootIncidentFiberUnderlying (n := n) (l := l))
    ⟨rootIncidentFiberUnderlying_injective hn,
      rootIncidentFiberUnderlying_surjective⟩
end

end PottsDiscontinuity.BetheAnsatz
