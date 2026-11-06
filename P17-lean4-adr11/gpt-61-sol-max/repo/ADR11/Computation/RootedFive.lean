module
public import ADR11.Rootings.Proofs
import all Mathlib.Data.Multiset.Functor
import all Mathlib.Control.Traversable.Basic
public meta import ADR11.Rootings.Proofs
public meta import ADR11.Computation.Engine
public import ADR11.Rootings.Defs
/-! A common linear representation of the distributions of the 24 rootings on five taxa.
The first five coordinates depend only on the unrooted metric tree. The final coordinate
records the root location. Its allowed interval distinguishes the rootings. -/
@[expose] public section
namespace ADR11.Five
open Finset _root_.ADR11.Computation
set_option maxHeartbeats 0
set_option maxRecDepth 8000

def codes (k j : ℕ) : List ℕ :=
  ([[[], [30], [29], [27], [23], [15]], [[3], [28], [3, 28], [28, 30], [28, 29], [3, 27], [3, 23], [3, 15]], [[3, 7, 15], [3, 7, 23], [24, 28, 30], [24, 28, 29], [3, 24, 27], [3, 7, 24], [3, 24, 28], [3, 24], [3, 7], [24, 28]]]).getD k [] |>.getD j []

def rKey (k j : ℕ) : Key :=
  (codes k j).map fun c =>
    (c, if c == 3 || c == 24 then 1 else if c == 7 || c == 28 then 3 else 6)

def aKey (k j : ℕ) : Key :=
  ((codes k j).filter (fun c => c == 3 || c == 28)).map (·, 1)
def bKey (k j : ℕ) : Key :=
  ((codes k j).filter (fun c => c == 7 || c == 24)).map (·, 1)
def mixKey (k j a b : ℕ) : Key :=
  ((codes k j).filter (fun c => c == 3 || c == 28 || c == 7 || c == 24)).map
    (fun c => (c, if c == 3 || c == 28 then a else b))
def keys (k j : ℕ) : List (Key) :=
  [[], aKey k j, bKey k j, mixKey k j 1 1, mixKey k j 1 3, mixKey k j 3 1, rKey k j]

def hierarchy (k j : ℕ) : Family (Fin 5) := hierarchyOf (decF 5 (codes k j))

def shape (k j : ℕ) : PTree := buildTree 5 31 ([1, 2, 4, 8, 16, 31] ++ codes k j)
/-- Four unrooted gene-tree topologies that suffice for root identification. -/
def geneTree (i : ℕ) : Family (Fin 5) :=
  let p := [(3, 7), (3, 11), (3, 19), (5, 7)].getD i (0, 0)
  treeOfClusters (decF 5 [p.1, p.2])

def table : List (List (List (List (ℚ × ℕ)))) := eval%
  ((List.range 3).map fun k => (List.range (6 + 2 * k)).map fun j =>
    let M := ((shape k j).out 5 5 id).getD 0
    (List.range 4).map fun i =>
      let c := coefficients (collect M (geneTree i))
      ((keys k j).dedup.filter fun t => c t != 0).map
        fun t => (90 * c t, (keys k j).idxOf t))

def coeffs (k j i : ℕ) : List (ℚ × ℕ) :=
  ((table.getD k []).getD j []).getD i []

def poly (k j i : ℕ) : Poly :=
  Multiset.ofList ((coeffs k j i).map fun (c, l) => (c / 90, (keys k j).getD l []))

def targets (k j : ℕ) : List (Family (Fin 5) × Poly) :=
  (List.range 4).map fun i => (geneTree i, poly k j i)

theorem checks (k : Fin 3) (j : Fin (6 + 2 * k.val)) :
    root_certsB 5 (hierarchy k j) (shape k j) (targets k j) = true := by
  fin_cases k <;> fin_cases j <;> decide +kernel

theorem hierarchies : ∀ k : Fin 3,
    rootingsOf (U5 k) = univ.image (fun j : Fin (6 + 2 * k.val) => hierarchy k j) := by decide +kernel

noncomputable def param (len : Finset (Fin 5) → ℝ) (k j l : ℕ) : ℝ :=
  monoVal len ((keys k j).getD l [])

end ADR11.Five
