module
public import Mathlib

public import PottsDiscontinuity.FK.WiredRemoval
public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge

/-! # The right-half interior and the exterior measurability of B -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Indexed edges in the right half of the lifted strip, excluding the
horizontal seam. Index zero is the right boundary column N in the cover. -/
def rightHalfInteriorSite (e : Fin N × Fin M)  :=
  (e.1.val = 0 ∨ N / 2 < e.1.val) ∧ e.2.val ≠ 0

section

variable (hN : 0 < N) (hM : 0 < M)
include hN hM

/-- Every edge used by a left-strip path has a strictly positive horizontal
index no larger than the strip width. -/
theorem leftStrip_edge_index_range 
    (A : RCConfig N M) (K : ℕ) (hK : K < N) {u v : RotatedVertex}
    (huv : (liftedStripGraph hN hM A 0 (K : ℤ)).Adj u v) :
    1 ≤ (liftedEdgeIndex hN hM u v).1.val ∧
      (liftedEdgeIndex hN hM u v).1.val ≤ K := by
  have hdist  := huv.1.1
  have hne : u.val.1 ≠ v.val.1 := by
    grind
  have hmax1 : 1 ≤ max u.val.1 v.val.1 := by
    have hu := huv.2.2.1.1
    have hv := huv.2.2.2.1
    omega
  have hmaxK  :=
    max_le huv.2.2.1.2 huv.2.2.2.2
  have hval :  (liftedEdgeIndex hN hM u v).1.val  = max u.val.1 v.val.1 := by
    change ((periodicCoordinate hN (max u.val.1 v.val.1)).val : ℤ) = _
    rw [periodicCoordinate_val, Int.emod_eq_of_lt (by omega) (by omega)]
  constructor <;> omega

section

variable (A B : RCConfig N M)
include A B

theorem leftStripGraph_le_of_agree 
     (K : ℕ) (hK : K < N)
    (hAB : ∀ e : Fin N × Fin M, 1 ≤ e.1.val → e.1.val ≤ K → A e = B e) :
    liftedStripGraph hN hM A 0 (K : ℤ) ≤ liftedStripGraph hN hM B 0 (K : ℤ) := by
  intro u v huv
  have hi := leftStrip_edge_index_range hN hM A K hK huv
  refine ⟨huv.1, ?_, huv.2.2⟩
  rw [← hAB (liftedEdgeIndex hN hM u v) hi.1 hi.2]
  exact huv.2.1

/-- The left annular crossing depends only on indices `1,...,3n` and does
not inspect the right-half interior edges. -/
theorem leftStripCrossing_congr 
     (n : ℕ) (hn : 3 * n < N)
    (hAB : ∀ e : Fin N × Fin M, 1 ≤ e.1.val → e.1.val ≤ 3 * n → A e = B e) :
    torusRCLeftStripCrossing hN hM A n ↔ torusRCLeftStripCrossing hN hM B n := by
  
  unfold torusRCLeftStripCrossing
  rw [ le_antisymm (leftStripGraph_le_of_agree hN hM A B (3 * n) hn hAB)
           (leftStripGraph_le_of_agree hN hM B A (3 * n) hn
              fun e hi1 hin => (hAB e hi1 hin).symm ) ]

/-- The source barrier event is determined by the configuration outside the
right-half interior (including all seam-edge states). -/
theorem barrier_congr_outside_rightHalf 
     (n : ℕ) (hn : 3 * n ≤ N / 2)
    (hAB : ∀ e : Fin N × Fin M, ¬ rightHalfInteriorSite e → A e = B e) :
    A ∈ torusRCBarrier hN hM n ↔ B ∈ torusRCBarrier hN hM n := by
  
  have hseam : torusRCSeamAllButOneOpen hM A ↔ torusRCSeamAllButOneOpen hM B := by
    grind [rightHalfInteriorSite, torusRCSeamAllButOneOpen]
  change  ¬ torusRCLeftStripCrossing hN hM A n ∧ torusRCSeamAllButOneOpen hM A  ↔
     ¬ torusRCLeftStripCrossing hN hM B n ∧ torusRCSeamAllButOneOpen hM B 
  rw [ leftStripCrossing_congr hN hM A B n (by omega)
          fun e hi1 hin => hAB e (by
           intro he
           rcases he.1 with he | he <;> omega)  , hseam]

end

end

noncomputable section

local instance rightHalfGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

local instance rightHalfGraphDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

/-- Exactly the edges outside the right-half interior, including row zero. -/
def rightHalfFrozenEdges (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    FK.Configuration (fullDiamondGraph hN hM) := by
  classical
  exact Finset.univ.filter fun e =>
    ¬ rightHalfInteriorSite ((torusIndexedEdgeEquiv hN hM hN4 hM4).symm e)

@[simp] theorem mem_rightHalfFrozenEdges (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (v : Fin N × Fin M) :
    torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ rightHalfFrozenEdges hN hM hN4 hM4 ↔
      ¬ rightHalfInteriorSite v := by
  
  simp [rightHalfFrozenEdges]

/-- Restore an exterior state and a remaining state to the original indexed
configuration; every frozen open and closed edge keeps its exact state. -/
def rightHalfRestore (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))  :=
  (torusRCConfigurationEquiv hN hM hN4 hM4).symm (A.val ∪ H.val)

section

variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
include hN hM hN4 hM4

private theorem configurationEquiv_symm_true 
    (C : FK.Configuration (fullDiamondGraph hN hM)) (v : Fin N × Fin M) :
    (torusRCConfigurationEquiv hN hM hN4 hM4).symm C v = true ↔
      torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ C := by
  have h := mem_torusRCConfigurationEquiv hN hM hN4 hM4
    ((torusRCConfigurationEquiv hN hM hN4 hM4).symm C) v
  change _ ↔ torusIndexedEdgeEmbedding hN hM hN4 hM4 v ∈ C
  simp_all

section

variable (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))


theorem rightHalfRestore_true_iff 
    
    (A : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) (v : Fin N × Fin M) :
    rightHalfRestore hN hM hN4 hM4 H A v = true ↔
      torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ A.val ∨
      torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ H.val := by
  simp_all [rightHalfRestore, configurationEquiv_symm_true]

theorem rightHalfRestore_mono 
    
    {A B : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)} (hAB : A ≤ B) :
    rightHalfRestore hN hM hN4 hM4 H A ≤ rightHalfRestore hN hM hN4 hM4 H B := by
  intro v
  cases ha : rightHalfRestore hN hM hN4 hM4 H A v
  · exact Bool.false_le _
  · 
    
    rw [ (rightHalfRestore_true_iff hN hM hN4 hM4 H B v).mpr
           (((rightHalfRestore_true_iff hN hM hN4 hM4 H A v).mp ha).imp (fun h => hAB h) id) ]

theorem rightHalfRestore_agree_outside 
    
    (A B : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) (v : Fin N × Fin M)
    (hv : ¬ rightHalfInteriorSite v) :
    rightHalfRestore hN hM hN4 hM4 H A v = rightHalfRestore hN hM hN4 hM4 H B v := by
  
  have hvR := (mem_rightHalfFrozenEdges hN hM hN4 hM4 v).mpr hv
  have hnotA  :=
    fun h => Finset.disjoint_left.mp A.property h hvR
  have hnotB  :=
    fun h => Finset.disjoint_left.mp B.property h hvR
  have htrue : rightHalfRestore hN hM hN4 hM4 H A v = true ↔
      rightHalfRestore hN hM hN4 hM4 H B v = true := by
    simp_all [rightHalfRestore, configurationEquiv_symm_true]
  cases ha : rightHalfRestore hN hM hN4 hM4 H A v <;>
    cases hb : rightHalfRestore hN hM hN4 hM4 H B v <;> simp_all

end

/-- Membership in B is constant on every right-half conditional fiber. -/
theorem barrier_rightHalfRestore_iff  (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (hn : 3 * n ≤ N / 2)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A B : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :
    rightHalfRestore hN hM hN4 hM4 H A ∈ torusRCBarrier hNp hMp n ↔
      rightHalfRestore hN hM hN4 hM4 H B ∈ torusRCBarrier hNp hMp n :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.TorusRC.barrier_congr_outside_rightHalf, _root_.PottsDiscontinuity.TorusRC.rightHalfRestore_agree_outside]

end

/-- The actual exterior event corresponding to B, evaluated by restoring the
empty interior state. Fiber constancy proves this choice immaterial. -/
def rightHalfBarrierExterior (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M) (n : ℕ)  :=
  {H | rightHalfRestore hN hM hN4 hM4 H ⟨∅, Finset.disjoint_empty_left _⟩ ∈
    torusRCBarrier hNp hMp n}

/-- Exact exterior-measurability identity for use with the joint fiber law. -/
theorem barrier_iff_rightHalfExterior (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (hn : 3 * n ≤ N / 2) (A : RCConfig N M) :
    A ∈ torusRCBarrier hNp hMp n ↔
      (FK.configurationSplitEquiv (fullDiamondGraph hN hM)
        (rightHalfFrozenEdges hN hM hN4 hM4)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A)).2 ∈
          rightHalfBarrierExterior hN hM hN4 hM4 hNp hMp n := by
  let P := FK.configurationSplitEquiv (fullDiamondGraph hN hM)
    (rightHalfFrozenEdges hN hM hN4 hM4)
    (torusRCConfigurationEquiv hN hM hN4 hM4 A)
  have hrestore : rightHalfRestore hN hM hN4 hM4 P.2 P.1 = A := by
    unfold rightHalfRestore
    have hsplit := (FK.configurationSplitEquiv (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)).symm_apply_apply
      (torusRCConfigurationEquiv hN hM hN4 hM4 A)
    change P.1.val ∪ P.2.val = torusRCConfigurationEquiv hN hM hN4 hM4 A at hsplit
    rw [hsplit, Equiv.symm_apply_apply]
  change A ∈ torusRCBarrier hNp hMp n ↔
    rightHalfRestore hN hM hN4 hM4 P.2 ⟨∅, Finset.disjoint_empty_left _⟩ ∈
      torusRCBarrier hNp hMp n
  rw [← hrestore]
  exact barrier_rightHalfRestore_iff hN hM hN4 hM4 hNp hMp n hn P.2 P.1 _

end

end PottsDiscontinuity.TorusRC
