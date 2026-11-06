module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Toroidal

/-!
# Finite cyclic gap configurations

Companion paper, `cor:expressionRsi` and the domain of the sum `R_σ`.
The lower coordinates are the actual predecessor coordinates on the integer cover.
Residue distinctness is retained in the definition, including the wraparound endpoints.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- All integer choices in the closed predecessor gaps. -/
def gapTuples {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ) : Finset (Fin (n + 1) → ℤ) :=
  Fintype.piFinset  fun k => Icc (cyclicPredecessorPositions N x k) (x k) 

/-- Gap choices whose positions are distinct modulo the circumference. -/
def distinctGapTuples {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ)  :=
  (gapTuples N x).filter  fun y => Function.Injective  fun k => y k % (N : ℤ)  

/-- The extended weight in the companion paper's gap sum. -/
noncomputable def gapWeight {n : ℕ} (c : ℝ) (N : ℕ)
    (x y : Fin (n + 1) → ℤ) : ℂ :=
  ∏ k, if y k = cyclicPredecessorPositions N x k ∨ y k = x k then 1 else (c : ℂ) ^ 2

/-- The finite cyclic gap sum `R_σ`; no Bethe equation is part of its definition. -/
noncomputable def cyclicGapSum {n : ℕ} (c : ℝ) (N : ℕ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))  :=
  ∑ y ∈ distinctGapTuples N x, gapWeight c N x y * planeWave p σ y

/-- A collision of consecutive gap choices at their common endpoint, including the seam. -/
def gapCollision {n : ℕ} (N : ℕ) (x y : Fin (n + 1) → ℤ) (k : Fin (n + 1))  :=
  y k = x k ∧ y (finRotate (n + 1) k) =
    cyclicPredecessorPositions N x (finRotate (n + 1) k)

@[simp] theorem mem_gapTuples {n N : ℕ} {x y : Fin (n + 1) → ℤ} :
    y ∈ gapTuples N x ↔ ∀ k, cyclicPredecessorPositions N x k ≤ y k ∧ y k ≤ x k := by
  grind +locals

section

variable {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ)


@[simp] theorem cyclicPredecessorPositions_zero  :
    cyclicPredecessorPositions N x 0 = x (Fin.last n) - N := rfl

@[simp] theorem cyclicPredecessorPositions_succ  (k : Fin n) :
    cyclicPredecessorPositions N x k.succ = x k.castSucc := by
  have h : (finRotate (n + 1)).symm k.succ = k.castSucc :=
    (Equiv.symm_apply_eq _).mpr (finRotate_of_lt k.isLt).symm
  simp only [cyclicPredecessorPositions, h, Fin.succ_ne_zero, ↓reduceIte, sub_zero]

end

section

variable {N n : ℕ}
include N n

theorem positions_strictMono  (x : SixVertex.State N n) : StrictMono (positions x) := by
  intro i j hij
  
  unfold positions
  exact_mod_cast  (x.1.orderEmbOfFin x.2).strictMono hij 

theorem positions_span_lt  (x : SixVertex.State N (n + 1)) :
    positions x (Fin.last n) - positions x 0 < (N : ℤ) := by
  grind [positions]

section

variable {x y : Fin (n + 1) → ℤ}


/-- Gap choices are weakly increasing, before imposing residue distinctness. -/
theorem gapTuples_monotone  
    (hy : y ∈ gapTuples N x) : Monotone y := by
  apply Fin.monotone_iff_le_succ.mpr
  intro k
  
  have h2 := (mem_gapTuples.mp hy) k.succ
  rw [cyclicPredecessorPositions_succ] at h2
  exact ((mem_gapTuples.mp hy) k.castSucc).2.trans h2.1

section

variable (hx : StrictMono x) (hy : y ∈ gapTuples N x)
include hx hy

/-- Every coordinate belongs to the same closed interval of length N. -/
theorem gapTuples_global_bounds  
     (k : Fin (n + 1)) :
    x (Fin.last n) - N ≤ y k ∧ y k ≤ x (Fin.last n) := by
  
  
  
  exact ⟨((mem_gapTuples.mp hy) 0).1.trans ((gapTuples_monotone hy) (Fin.zero_le k)), ((mem_gapTuples.mp hy) k).2.trans
    (hx.monotone (Fin.le_last k))⟩

section

variable {i j : Fin (n + 1)} (hij : i < j)
include i j hij

/-- Two ordered coordinates in a gap tuple with the same residue differ by 0 or N. -/
theorem gapTuples_equal_residue  
    
     (he : y i % (N : ℤ) = y j % (N : ℤ)) :
    y j = y i ∨ y j - y i = N := by
  have hb1 := gapTuples_global_bounds hx hy i
  have hb2 := gapTuples_global_bounds hx hy j
  have hm := gapTuples_monotone hy hij.le
  
  by_cases h : y j - y i = N
  · exact Or.inr h
  · 
    
    have hz := Int.eq_zero_of_abs_lt_dvd (Int.modEq_iff_dvd.mp he) (by
                                               grind)
    omega

/-- Equal ordered gap coordinates can only be a common endpoint of neighboring gaps. -/
theorem gapTuples_equal_coordinates  
    
     (he : y i = y j) :
    ∃ k : Fin n, i = k.castSucc ∧ j = k.succ ∧ y i = x i ∧ y j = x i := by
  have hj : j ≠ 0 := by grind
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
  have hl := ((mem_gapTuples.mp hy) k.succ).1
  rw [cyclicPredecessorPositions_succ] at hl
  have hu := ((mem_gapTuples.mp hy) i).2
  
  have hi : i = k.castSucc := by
    by_contra hne
    have hstrict := hx (lt_of_le_of_ne (by
                                          grind) hne)
    omega
  subst i
  refine ⟨k, rfl, rfl, ?_, ?_⟩ <;> omega

end

end

/-- A gap-coordinate difference N occurs only at the two endpoints of the period. -/
theorem gapTuples_period_difference  
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ))
    (hy : y ∈ gapTuples N x) {i j : Fin (n + 1)}
    (he : y j - y i = N) :
    i = 0 ∧ j = Fin.last n ∧ y i = x (Fin.last n) - N ∧ y j = x (Fin.last n) := by
  have hbi := gapTuples_global_bounds hx hy i
  have hbj := gapTuples_global_bounds hx hy j
  
  
  
  
  exact ⟨ by
            by_contra hi
            obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hi
            have hl := ((mem_gapTuples.mp hy) k.succ).1
            rw [cyclicPredecessorPositions_succ] at hl
            have hx0 := hx.monotone (Fin.zero_le k.castSucc)
            omega ,  by
                by_contra hj
                have hstrict := hx (lt_of_le_of_ne (Fin.le_last j) hj)
                have hu := ((mem_gapTuples.mp hy) j).2
                omega ,  by omega ,  by omega ⟩

theorem gapCollision_equal_residue  
    {k : Fin (n + 1)} (hk : gapCollision N x y k) :
    y k % (N : ℤ) = y (finRotate (n + 1) k) % (N : ℤ) := by
  rw [hk.1, hk.2]
  simp only [cyclicPredecessorPositions]
  split_ifs <;> simp

end

/-- Residue distinctness is exactly exclusion of the local endpoint collisions.
At least two gaps are present, so each successor is a different coordinate. -/
theorem distinct_residues_iff_no_gapCollision  {x y : Fin (n + 2) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ))
    (hy : y ∈ gapTuples N x) :
    Function.Injective (fun k => y k % (N : ℤ)) ↔ ∀ k, ¬ gapCollision N x y k := by
  constructor
  · intro hinj k hk
    
    
    exact (Equiv.Perm.mem_support.mp (by rw [support_finRotate]; exact mem_univ k)) (hinj (gapCollision_equal_residue hk)).symm
  · intro hn
    have hord : ∀ i j , i < j → y i %  N  ≠ y j %  N  := by
      intro i j hij he
      rcases gapTuples_equal_residue hx hy hij he with heq | hperiod
      · obtain ⟨k, hi, hj, hu, hl⟩ := gapTuples_equal_coordinates hx hy hij heq.symm
        apply hn i
        refine ⟨hu, ?_⟩
        simp_all
      · obtain ⟨hi, hj, hl, hu⟩ := gapTuples_period_difference hx hspan hy hperiod
        apply hn j
        refine ⟨?_, ?_⟩
        all_goals simp_all
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hord i j hij he).elim
    · exact hij
    · exact (hord j i hij he.symm).elim

end

end PottsDiscontinuity.BetheAnsatz
