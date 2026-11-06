module

public import Erdos821.Blueprint.ResiduePaths

/-! Expanded histories record births before global distinctness is imposed. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- At each visit, before/after refer to the ghost operation.
Edges go from `after i.castSucc` to `before i.succ`. -/
structure MemoryHistory (A : Model F P J m) (n : ℕ) where
  before : Fin (n + 1) → P.MemoryState (J + F.ell)
  after : Fin (n + 1) → P.MemoryState (J + F.ell)
  ghost : (i : Fin (n + 1)) → GhostChoice (before i) (after i)
  edge : (i : Fin n) → EdgeChoice A (after i.castSucc)

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

def Valid  :=
  (∀ g, (H.before 0).2.2 g = 0) ∧
  (∀ g, (H.after (Fin.last n)).2.2 g = 0) ∧
  (∀ i, (H.before i).1 = (H.after i).1 ∧
    (H.before i).2.1 = (H.after i).2.1 ∧ ghostChoiceValid (H.ghost i)) ∧
  (∀ i, edgeChoiceValid A .all i (H.after i.castSucc) (H.before i.succ) (H.edge i))

def initialBirthValues : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ i : Fin (J + F.ell), {((H.before 0).2.1 g.val i).val}

def ghostBirthValues (i : Fin (n + 1)) : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ h : Fin ((H.ghost i).2.1 g).val, {((H.ghost i).2.2 g h).val}

def freshTargetSlots (i : Fin n) (g : P.BigGroup)  :=
  Finset.univ.filter (fun h => ¬ (A.pattern (H.edge i).2.2.1).shared g.val h ∧
    h ∉ (H.edge i).2.2.2.2.2.1 g)

def freshBirthValues (i : Fin n) : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ h ∈ H.freshTargetSlots i g,
    {((permuteActive (H.edge i).2.1 (H.before i.succ)).2.1 g.val h).val}

/-- Initial slots, fresh target slots and ghost batches; auxiliary draws are absent. -/
def birthValues  :=
  H.initialBirthValues + ∑ i, H.ghostBirthValues i + ∑ i, H.freshBirthValues i

def DistinctBirths  := H.birthValues.Nodup

def Weight (rho theta : ℝ)  :=
  (P.memoryMass F J n (H.before 0) : ℂ) *
    (∏ i : Fin (n + 1), (ghostChoiceWeight F n rho i (H.ghost i) : ℂ)) *
    (∏ i : Fin n, (edgeSymmetryFactor P (J + F.ell) : ℂ) *
      edgeChoiceCoefficient A n rho theta i (H.after i.castSucc) (H.before i.succ) (H.edge i))

end MemoryHistory

/-- This is a sum over individual histories, with global birth distinctness
inside the expansion. Summability must be proved before tsum manipulations. -/
def distinctMemoryExpression (A : Model F P J m) (n : ℕ) (rho theta : ℝ)  :=
  ∑' H : MemoryHistory A n, if H.Valid ∧ H.DistinctBirths then H.Weight rho theta else 0

/-- Fixed potential addresses after memory truncation. -/
abbrev BirthAddress (P : PrimeGroups) (M n B ) :=
  (P.BigGroup × Fin M) ⊕ ((Fin n × P.BigGroup × Fin M) ⊕
    (Fin (n + 1) × P.BigGroup × Fin B))

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

end MemoryHistory

end Erdos821.Blueprint.Graph
