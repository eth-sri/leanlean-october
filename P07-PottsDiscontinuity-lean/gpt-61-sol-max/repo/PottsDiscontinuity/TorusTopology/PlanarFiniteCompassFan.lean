/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Factored finite table proof to avoid repeated cardinal computations; namespace/import relocation; antipodal turn is the principal value +2, agreeing with the original on every nonbacktracking pair. -/
module
public import Mathlib

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

/-- For a set of compass sectors, the signed boundary at direction `d` is its
indicator minus the indicator of the preceding sector. Directions are the
cyclic compass labels `0 = E, 1 = N, 2 = W, 3 = S`. -/
def compassSectorBoundary (Q : Finset (Fin 4)) (d : Fin 4) : ℤ :=
  (if d ∈ Q then 1 else 0) -  if d - 1 ∈ Q then 1 else 0 

/-- The signed quarter-turn for travel directions. The input directions are
those of travel; the antipodal case uses the principal value +2.
Nonbacktracking circuits exclude that case. -/
def primalCompassQuarterTurn (a b : Fin 4) : ℤ :=
  if b = a + 1 then 1 else if b = a + 3 then -1 else if b = a + 2 then 2 else 0

theorem compassSectorBoundary_zero_eq_empty_or_univ (Q : Finset (Fin 4))
    (h : ∀ d, compassSectorBoundary Q d = 0) : Q = ∅ ∨ Q = Finset.univ := by
  have hstep (d : Fin 4) : d ∈ Q ↔ d - 1 ∈ Q := by
    have hd := h d
    simp [compassSectorBoundary] at hd
    aesop
  
  
  
  have hall (x : Fin 4) : x ∈ Q ↔  0  ∈ Q := by
    fin_cases x
    
    all_goals grind
  by_cases hQ : Q.Nonempty
  · grind
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hQ

theorem primalCompassQuarterTurn_eq_sector_boundary_formula
    (Q : Finset (Fin 4)) (a b : Fin 4) (k : ℤ) (hab : a ≠ b)
    (hk : k = -1 ∨ k = 1)
    (h : ∀ d, compassSectorBoundary Q d =
      if d = b then k else if d = a then -k else 0) :
    primalCompassQuarterTurn (a + 2) b = k * (2 - (Q.card : ℤ)) := by
  have hcard : (Q.card : ℤ) =
      (if  0  ∈ Q then 1 else 0) + (if  1  ∈ Q then 1 else 0) +
      (if  2  ∈ Q then 1 else 0) +  if  3  ∈ Q then 1 else 0  := by
    have hs := Finset.sum_boole (R := ℤ) (fun d  => d ∈ Q) Finset.univ
    rw [Fin.sum_univ_four] at hs
    simpa using hs.symm
  have hb (d : Fin 4) : 0 ≤ (if d ∈ Q then  1  else 0) ∧
      (if d ∈ Q then  1  else 0) ≤ 1 := by split_ifs <;> omega
  
  
  
  
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  clear h hb
  rcases hk with hk | hk <;> subst k
  fin_cases a <;> fin_cases b
  try contradiction
  all_goals
    grind +locals

end PottsDiscontinuity.TorusTopology.Planar.Medial
