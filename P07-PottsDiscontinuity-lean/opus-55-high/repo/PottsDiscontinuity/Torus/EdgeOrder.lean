module

public import PottsDiscontinuity.Torus.RibbonEmpty

/-!
# Explicit finite orders for indexed edge attachment

Configurations are represented by lists of their open indexed edges. A fixed
coordinate enumeration supplies a canonical list without choosing an arbitrary order.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Open exactly the indexed edges appearing in a list. -/
def configOfList (L : List (Fin N × Fin M)) : RCConfig N M := fun v => decide (v ∈ L)

@[simp] theorem configOfList_nil : configOfList ([] : List (Fin N × Fin M)) = closedRCConfig N M := rfl

theorem configOfList_cons (v : Fin N × Fin M) (L : List (Fin N × Fin M))
    (hv : v ∉ L) : configOfList (v :: L) = toggleEdge (configOfList L) v := by
  funext w
  by_cases hw : w = v
  · simp_all [configOfList]
  · rw [toggleEdge_away _ hw]
    simp_all [configOfList]

section
variable (L : List (Fin N × Fin M))
theorem openCount_configOfList  :
    openCount (configOfList L) = L.toFinset.card := by
  unfold openCount
  congr 1
  ext v
  simp [configOfList]

theorem openCount_configOfList_of_nodup (hL : L.Nodup) :
    openCount (configOfList L) = L.length := by
  rw [openCount_configOfList, List.toFinset_card_of_nodup hL]
end

/-- Coordinate order of every indexed diamond edge. -/
def diamondEdgeOrder (N M : ℕ) : List (Fin N × Fin M) :=
  List.ofFn (finProdFinEquiv.symm : Fin (N * M) → Fin N × Fin M)

theorem diamondEdgeOrder_nodup : (diamondEdgeOrder N M).Nodup :=
  List.nodup_ofFn.mpr finProdFinEquiv.symm.injective

@[simp] theorem mem_diamondEdgeOrder (v : Fin N × Fin M) : v ∈ diamondEdgeOrder N M :=
  List.mem_ofFn.mpr ⟨finProdFinEquiv v, finProdFinEquiv.symm_apply_apply v⟩

section
variable (A : RCConfig N M)
/-- The open indexed edges in the specified coordinate order. -/
def openEdgeList  : List (Fin N × Fin M) :=
  (diamondEdgeOrder N M).filter A

theorem openEdgeList_nodup  : (openEdgeList A).Nodup :=
  diamondEdgeOrder_nodup.filter A

@[simp] theorem configOfList_openEdgeList  :
    configOfList (openEdgeList A) = A := by
  funext v
  simp only [configOfList, openEdgeList, List.mem_filter, mem_diamondEdgeOrder,
    true_and, Bool.decide_eq_true]

theorem length_openEdgeList  : (openEdgeList A).length = openCount A := by
  grind [openCount_configOfList_of_nodup, openEdgeList_nodup, configOfList_openEdgeList]
end

end PottsDiscontinuity.Torus
