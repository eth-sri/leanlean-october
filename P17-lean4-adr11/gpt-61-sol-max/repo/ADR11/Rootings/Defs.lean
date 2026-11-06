module
public import ADR11.SmallTrees
public import ADR11.MSC.Basic
@[expose] public section
namespace ADR11
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted trees on `Fin 4`: `U4 1` has the split `AB|CD`, `U4 0` is the star. -/
def U4 : ℕ → Family (Fin 4)
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The unrooted trees on `Fin 5`: `U5 2` has the splits `AB|CDE` and `ABC|DE`, `U5 1` the split
`AB|CDE`, and `U5 0` is the star. -/
def U5 : ℕ → Family (Fin 5)
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

instance (H : Family X) : Decidable (IsHierarchy H) := by
  unfold IsHierarchy
  infer_instance
def rootingsOf (U : Family X) : Finset (Family X) :=
  (((U.filter fun A => 2 ≤ #A).powerset).filter
    fun N => IsHierarchy (hierarchyOf N) ∧ unroot (hierarchyOf N) = U).image hierarchyOf

end ADR11
