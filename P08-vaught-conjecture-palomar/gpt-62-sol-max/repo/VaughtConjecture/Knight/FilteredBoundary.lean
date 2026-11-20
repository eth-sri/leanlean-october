/- Restriction to a downward-closed family of graded indices. -/
module

public import VaughtConjecture.Knight.CellBelowEquiv
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Value

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}

structure FilteredBoundary (D : CellScheme A) (B : Finset ι) where
  keep : Finset ι × ℕ → Prop
  decideKeep : DecidablePred keep
  down : ∀ {I J}, GradedLe I J → keep J → keep I
  plan : Finset (Finset ι)
  valid : Plan.IsPlan B plan
  supports : ∀ d : Cell D, keep (D.cell d) → D.cell d ∈ Plan.gradedPlan plan

namespace FilteredBoundary

noncomputable section

variable {D : CellScheme A} (F : FilteredBoundary D B)

local instance : DecidablePred (fun d : Cell D => F.keep (D.cell d)) :=
  fun d => F.decideKeep (D.cell d)

def inventory : Finset (Cell D) := Finset.univ.filter (fun d => F.keep (D.cell d))

def toCell : Fin F.inventory.card ↪o Cell D := F.inventory.orderEmbOfFin rfl

theorem retained (d : Fin F.inventory.card) : F.keep (D.cell (F.toCell d)) :=
  (Finset.mem_filter.mp (F.inventory.orderEmbOfFin_mem rfl d)).2

def scheme : CellScheme B where
  plan := F.plan
  isPlan := F.valid
  card := F.inventory.card
  cell d := D.cell (F.toCell d)
  cell_mem d := F.supports _ (F.retained d)

theorem exhaustive {d : Cell D} (hd : F.keep (D.cell d)) : ∃ c, F.toCell c = d := by
  change d ∈ Set.range (F.inventory.orderEmbOfFin (k := F.inventory.card) rfl)
  rw [Finset.range_orderEmbOfFin]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩

def belowEquiv (J : Finset ι × ℕ) (hJ : F.keep J) : F.scheme.below J ≃ D.below J :=
  CellScheme.belowEquivOfIndex F.toCell F.toCell.injective (fun _ => rfl)
    (fun _ hd => F.exhaustive (F.down hd hJ))

variable (sem : Semantics D)

def rows : Semantics F.scheme where
  E c d := sem.E (F.toCell c) (F.belowEquiv _ (F.retained c) d)
  orderly c _ := sem.orderly (F.toCell c) _

theorem respects_iff (J : Finset ι × ℕ) (hJ : F.keep J) (p : F.scheme.below J → ExtOrd) :
    RespectsSemanticsBelow (F.rows sem) J p ↔
      RespectsSemanticsBelow sem J (p ∘ (F.belowEquiv J hJ).symm) :=
  respects_iff_of_index_equiv (F.belowEquiv J hJ) (fun _ => rfl) (fun _ _ _ => rfl) p

theorem pullback_respects {J : Finset ι × ℕ} (hJ : F.keep J)
    {p : D.below J → ExtOrd} (hp : RespectsSemanticsBelow sem J p) :
    RespectsSemanticsBelow (F.rows sem) J (p ∘ F.belowEquiv J hJ) :=
  (F.respects_iff sem J hJ _).mpr (by simpa [Function.comp_def] using hp)

theorem consistent (hs : sem.IsConsistent) : (F.rows sem).IsConsistent :=
  fun c => F.pullback_respects sem (F.retained c) (hs (F.toCell c))

end

end FilteredBoundary

end VaughtConjecture.Knight
