module
public import ADR11.Trees.Classify
public import ADR11.Rootings.Proofs
import all Mathlib.Data.Multiset.Functor
import all Mathlib.Control.Traversable.Basic
public import ADR11.Model
@[expose] public section
namespace ADR11.Q4
open Finset Real _root_.ADR11.Computation
set_option maxHeartbeats 0
set_option maxRecDepth 16000

def codes (k j : ℕ) : List ℕ :=
  ([[[], [7], [11], [13], [14]],
    [[3, 7], [3, 11], [12, 13], [12, 14], [3, 12], [3], [12]]]).getD k [] |>.getD j []
def hierarchy (k j : ℕ) : Family (Fin 4) := hierarchyOf (decF 4 (codes k j))
def key (k j : ℕ) : Key :=
  ((codes k j).filter (fun c => c == 3 || c == 12)).map (·, 1)
def shape (k j : ℕ) : PTree := buildTree 4 15 ([1, 2, 4, 8, 15] ++ codes k j)

theorem checks (k : Fin 2) (j : Fin (5 + 2 * k.val)) :
    root_certsB 4 (hierarchy k j) (shape k j)
      [(treeOfClusters {{0, 1}}, {(1, []), (-2 / 3, key k j)}),
       (treeOfClusters {{0, 2}}, {(1 / 3, key k j)}),
       (treeOfClusters {{0, 3}}, {(1 / 3, key k j)})] = true := by
  fin_cases k <;> fin_cases j <;> decide +kernel

theorem hierarchies : ∀ k : Fin 2,
    rootingsOf (U4 k) = univ.image (fun j : Fin (5 + 2 * k.val) => hierarchy k j) := by decide +kernel

theorem dist (k : Fin 2) (j : Fin (5 + 2 * k.val)) (τ : SpeciesTree (Fin 4))
    (hc : τ.clusters = hierarchy k j) :
    let x := monoVal τ.length (key k j)
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * x ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * x ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * x := by
  have hd := @root_unrootedDist_eq_evalPoly 4 τ _ _ (hc.symm ▸ checks k j)
  simpa [evalPoly, sub_eq_add_neg, neg_div] using @hd

theorem core (k : Fin 2) (τ : SpeciesTree (Fin 4)) (hc : unroot τ.clusters = U4 k) :
    let x := if k.val = 0 then 1 else exp (-τ.unrootedLength {0, 1})
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * x ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * x ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * x := by
  obtain ⟨j, -, hj⟩ := mem_image.1 ((hierarchies k) ▸ mem_rootings τ hc)
  have hx : monoVal τ.length (key k j) = if k.val = 0 then 1 else exp (-τ.unrootedLength {0, 1}) := by
    simp only [SpeciesTree.unrootedLength, hj.symm, ← root_decC4_3]
    fin_cases k <;> fin_cases j <;>
      simp (disch := decide +kernel) [key, codes, decF, hierarchy, hierarchyOf,
        Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton, ite_eq_left, ite_eq_right, exp_add] <;> ring
  simpa only [hx] using dist k j τ hj.symm

end ADR11.Q4
