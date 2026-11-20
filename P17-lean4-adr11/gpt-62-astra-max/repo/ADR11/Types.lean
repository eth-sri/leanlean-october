module
public import ADR11.Defs
@[expose] public section
namespace ADR11
open Finset
abbrev Clusters (X : Type*) := Finset (Finset X)

abbrev Compatible {X : Type*} (A B : Finset X) := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
abbrev Laminar {X : Type*} (F : Clusters X) := ∀ A ∈ F, ∀ B ∈ F, Compatible A B

/-- Complete a list of internal clades by adding the root and leaves. -/
def hierarchyOf {X : Type*} [Fintype X] [DecidableEq X] (C : Clusters X) := insert univ (C ∪ univ.image fun x => {x})

/-- The merge rate, indexed by the number of remaining jumps. -/
def rate (k : ℕ) := (k+1).choose 2

variable {L : Type*} [DecidableEq L]
/-- The lineages of a forest: the union of its clusters. -/
def lineages (F : Clusters L) : Finset L := F.sup id

def joined (F P : Clusters L) := insert (lineages P) F
def merges [Fintype L] (F : Clusters L) := ((roots F).powersetCard 2).image (joined F)

end ADR11
