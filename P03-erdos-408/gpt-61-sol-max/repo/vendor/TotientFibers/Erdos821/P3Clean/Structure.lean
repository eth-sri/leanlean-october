module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Edge.ColReversal

public import Erdos821.S2.EdgeTasks

/-! The literal clean mask and the diagonal memory translation. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData} {J m : ℕ}

def emptyTransfer {M } (s : P.MemoryState M) : TransferChoice s :=
  ⟨fun _ => ∅, ⟨fun _ => ∅,
    fun _ (i : {i : Fin M // i ∈ (∅ : Finset (Fin M))}) =>
      False.elim (Finset.notMem_empty i.val i.property)⟩⟩

section
variable {M : ℕ}

theorem clean_transfer_iff   {s : P.MemoryState M} (c : TransferChoice s) :
    transferModeAccept .clean c ↔ c = emptyTransfer s := by
  constructor
  · intro h
    rcases c with ⟨B, A, f⟩
    have hB : B = fun _ => ∅ := funext (fun g => (h g).1)
    have hA : A = fun _ => ∅ := funext (fun g => (h g).2)
    subst B A
    congr 2
    funext g i
    exact False.elim (Finset.notMem_empty i.val i.property)
  · rintro rfl
    exact fun _ => ⟨rfl, rfl⟩

theorem sum_clean_transfer   (s : P.MemoryState M)
    (h : TransferChoice s → Prop) (f : TransferChoice s → ℂ) :
    (∑ c : TransferChoice s, if h c ∧ transferModeAccept .clean c then f c else 0) =
      if h (emptyTransfer s) then f (emptyTransfer s) else 0 := by
  classical
  simp_rw [clean_transfer_iff]
  rw [Finset.sum_eq_single (emptyTransfer s)]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

def cleanEdgeKernel (A : Model F P J m) (n ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell))  :=
  (edgeSymmetryFactor P (J + F.ell) : ℂ) *
    ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
      ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
        if rawEdgeValid A (A.pattern v) (edgeForward i) u
            (permuteActive π s) (permuteActive τ t) (emptyTransfer s) then
          edgeChoiceCoefficient A n rho theta i s t ⟨π, τ, v, u, emptyTransfer s⟩
        else 0

theorem memoryEdgeKernel_clean (A : Model F P J m)  n   rho theta 
     i  (s t : P.MemoryState (J + F.ell)) :
    memoryEdgeKernel A n rho theta i .clean (fun _ _ _ => 1) s t =
      cleanEdgeKernel A n rho theta i s t := by
  classical
  unfold memoryEdgeKernel cleanEdgeKernel
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro π _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [edgeChoiceValid, mul_one]
  exact sum_clean_transfer s _ _

theorem deleteMemoryIndices_empty {g : P.Group} (z : P.Memory g) :
    deleteMemoryIndices z ∅ = z := by
  classical
  simp only [deleteMemoryIndices, Finset.sdiff_empty]
  rw [← Multiset.map_coe, Finset.coe_toList, Fin.univ_val_map]
  unfold memoryEntry
  have h (l : List (P.Particle g)) (n : ℕ) (hn : l.length = n) :
      List.ofFn (fun i : Fin n => l.get ⟨i.val, by omega⟩) = l := by
    subst n
    exact List.ofFn_get l
  aesop

theorem retrievedIndices_empty   (s : P.MemoryState M) (g : P.BigGroup) :
    retrievedIndices (emptyTransfer s) g = ∅ := by
  rfl

theorem storedMemory_empty   {g : P.Group} (a : Fin M → P.Prime g) :
    storedMemory a ∅ = 0 := by simp [storedMemory]

end

theorem rawEdgeValid_empty (A : Model F P J m) (ν : Pattern P J F.ell m)
     forward  (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) :
    rawEdgeValid A ν forward u s t (emptyTransfer s) ↔
      P.smallPhysical s.1 s.2.1 ∧ P.smallPhysical t.1 t.2.1 ∧
      ν.compatible s.2.1 t.2.1 ∧ ν.ban s.2.1 t.2.1 u ∧
      t.1 = translateSmallResidues (edgeDelta A ν forward s.2.1 u) s.1 ∧
      ∀ g : P.BigGroup,
        t.2.2 g = translateMemory (edgeDelta A ν forward s.2.1 u) (s.2.2 g) := by
  classical
  unfold rawEdgeValid
  have hr (g : P.BigGroup) : retrievedIndices (emptyTransfer s) g = ∅ :=
    retrievedIndices_empty s g
  simp only [hr]
  simp [emptyTransfer, storedMemory_empty, deleteMemoryIndices_empty, Function.Injective]



theorem translateMemory_groupMass  F   n   delta 
     g   z  :
    P.groupMemoryMass F n g (translateMemory delta z) = P.groupMemoryMass F n g z := by solve_by_elim [_root_.Erdos821.P3Edge.groupMemoryMass_translateMemory]

end Erdos821.P3Clean
