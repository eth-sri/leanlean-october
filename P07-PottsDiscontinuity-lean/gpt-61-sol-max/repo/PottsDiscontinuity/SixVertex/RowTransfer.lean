module
public import Mathlib

public import PottsDiscontinuity.SixVertex.LocalWeight
public import PottsDiscontinuity.SixVertex.TransferMatrix

/-!
# One row of the torus: the transfer matrix `Ṽ` equals `V`

Companion paper arXiv:1611.09909v1, §4 (Lemma `lem:Interlacement` and Corollary
`cor:MatrixEquality`).  For states `x, y ⊆ Fin N` (up arrows below/above one row of vertices) the
weights of the ice-rule arrow configurations of the row graph `G` (horizontal edges of the cycle
`ℤ/N`, with the vertical edges prescribed by `x` below and `y` above) sum to `V(x, y)`.

The horizontal arrows `h : Fin N → Bool` of a row satisfy the ice rule iff the "flux equation"
`h(i) - h(i-1) = [i ∈ x] - [i ∈ y]` holds for all `i` (`Flux`); this is solved explicitly:
`h(i) = h(N-1) + cnt x i - cnt y i`.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c : ℝ}

/-! ### Cyclic successor/predecessor on `Fin (n + 1)` -/

theorem nxt_castSucc {n : ℕ} (i : Fin n) : nxt (Fin.castSucc i) = Fin.succ i := by
  simp 

theorem prv_succ {n : ℕ} (i : Fin n) : prv (Fin.succ i) = Fin.castSucc i := by
  
  rw [Equiv.symm_apply_eq]
  exact (nxt_castSucc i).symm

theorem prv_zero {n : ℕ} : prv (0 : Fin (n + 1)) = Fin.last n := rfl

/-! ### Counting functions along the cycle -/

section

variable {n : ℕ} (x : Finset (Fin (n + 1)))


theorem cnt_zero  :
    cnt x 0 = if (0 : Fin (n + 1)) ∈ x then 1 else 0 := by
  unfold cnt
  have : x.filter (· ≤ 0) = if  0  ∈ x then {0} else ∅ := by
    aesop
  rw [this]
  split_ifs <;> simp

theorem cnt_succ  (i : Fin n) :
    cnt x (Fin.succ i) = cnt x (Fin.castSucc i) + if Fin.succ i ∈ x then 1 else 0 := by
  unfold cnt
  have : x.filter (· ≤ Fin.succ i) =
      if Fin.succ i ∈ x then insert (Fin.succ i) (x.filter (· ≤ Fin.castSucc i))
      else x.filter (· ≤ Fin.castSucc i) := by
    grind
  rw [this]
  split_ifs with h
  · 
    simp
  · rfl

theorem cnt_last  : cnt x (Fin.last n) = x.card := by
  unfold cnt
  congr 1
  grind

end

/-! ### The flux equation -/

/-- `1` for `true` and `0` for `false`, as an integer. -/
def toInt (b : Bool) : ℤ := if b then 1 else 0

/-- The ice rule on a row, in terms of the horizontal arrows `h` (`h i = true`: the edge from `i`
to `i + 1` points right), the up arrows `x` below and `y` above the row:
`h(i) = h(i - 1) + [i ∈ x] - [i ∈ y]` for all `i`. -/
def Flux (x y : Finset (Fin N)) (h : Fin N → Bool)  :=
  ∀ i, toInt (h i) = toInt (h (prv i)) + toInt (decide (i ∈ x)) - toInt (decide (i ∈ y))

instance (x y : Finset (Fin N)) (h : Fin N → Bool) : Decidable (Flux x y h) := by
  unfold Flux; infer_instance

/-- The weight of a row of vertices with horizontal arrows `h`, up arrows `x` below and `y`
above (`a = b = 1`). -/
def rowWeight (c : ℝ) (x y : Finset (Fin N)) (h : Fin N → Bool)  :=
  ∏ i : Fin N, localWeight 1 1 c (h (prv i)) (h i) (decide (i ∈ x)) (decide (i ∈ y))

/-- The total weight `Ṽ(x, y)` of the ice-rule row configurations between `x` and `y`. -/
def rowSum (c : ℝ) (x y : Finset (Fin N))  := ∑ h : Fin N → Bool, rowWeight c x y h

theorem inDegree_eq_two_iff (l r d u : Bool) :
    inDegree l r d u = 2 ↔ toInt r = toInt l + toInt d - toInt u := by
  grind [inDegree, toInt]

theorem prod_ite_vertical (c : ℝ) (x y : Finset (Fin N)) :
    (∏ i : Fin N, if decide (i ∈ x) = decide (i ∈ y) then (1 : ℝ) else c) =
      c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have : (univ.filter fun i => ¬  decide (i ∈ x) = decide (i ∈ y) ) =
       univ.filter fun i => Psi x i ≠ Psi y i  := by
    grind [Psi]
  rw [this]

theorem rowWeight_eq (c : ℝ) (x y : Finset (Fin N)) (h : Fin N → Bool) :
    rowWeight c x y h =
      if Flux x y h then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0 := by
  have key : rowWeight c x y h =
      if Flux x y h then  ∏ i : Fin N, if decide (i ∈ x) = decide (i ∈ y) then  1  else c 
      else 0 := by
    unfold rowWeight
    simp_rw [localWeight_one_one, inDegree_eq_two_iff]
    rw [Finset.prod_ite_zero]
    simp only [mem_univ, forall_const]
    rfl
  rw [key]
  by_cases hf : Flux x y h
  · simp only [hf]
    exact prod_ite_vertical c x y
  · simp only [hf, ↓reduceIte]

/-! ### Solving the flux equation -/

section

variable {n : ℕ}

@[simp] theorem toInt_decide_mem {α : Type*} [DecidableEq α] (a : α) (x : Finset α) :
    toInt (decide (a ∈ x)) = if a ∈ x then 1 else 0 := by
  aesop

/-- `D(i) = cnt x i - cnt y i`: the accumulated flux up to position `i`. -/
def Dd (x y : Finset (Fin (n + 1))) (i : Fin (n + 1))  := (cnt x i : ℤ) - cnt y i

/-- The flux increment at position `i`. -/
def eFlux (x y : Finset (Fin (n + 1))) (i : Fin (n + 1))  :=
  toInt (decide (i ∈ x)) - toInt (decide (i ∈ y))

section

variable (x y : Finset (Fin (n + 1)))


theorem Dd_zero  : Dd x y 0 = eFlux x y 0 := by
  simp [Dd, eFlux, cnt_zero]

theorem Dd_succ  (i : Fin n) :
    Dd x y (Fin.succ i) = Dd x y (Fin.castSucc i) + eFlux x y (Fin.succ i) := by
  grind [Dd, eFlux, cnt_succ, toInt_decide_mem]

theorem Dd_last  : Dd x y (Fin.last n) = (x.card : ℤ) - y.card := by
  simp [Dd, cnt_last]

end

section

variable {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h)
include hf

/-- Every solution of the flux equation is `h(i) = h(last) + D(i)`. -/
theorem Flux.eq_add_Dd  :
    ∀ i, toInt (h i) = toInt (h (Fin.last n)) + Dd x y i := by
  intro i
  induction i using Fin.induction with
  | zero =>
    have := hf 0
    rw [prv_zero] at this
    rw [this, Dd_zero]
    simp [eFlux]
    ring
  | succ i ih =>
    have := hf (Fin.succ i)
    rw [prv_succ] at this
    rw [this, ih, Dd_succ]
    simp [eFlux]
    ring

/-- A solution of the flux equation forces `|x| = |y|`. -/
theorem Flux.card_eq  :
    x.card = y.card := by
  have := hf.eq_add_Dd (Fin.last n)
  rw [Dd_last] at this
  omega

end

/-- The parameter `s ∈ {0, 1}` (the value of the arrow entering position `0`) is admissible. -/
def ValidS (x y : Finset (Fin (n + 1))) (s : Bool)  :=
  Dd x y (Fin.last n) = 0 ∧ ∀ i, toInt s + Dd x y i = 0 ∨ toInt s + Dd x y i = 1

instance (x y : Finset (Fin (n + 1))) (s : Bool) : Decidable (ValidS x y s) := by
  unfold ValidS; infer_instance

/-- The explicit solution `h(i) = s + D(i)` of the flux equation. -/
def hOf (x y : Finset (Fin (n + 1))) (s : Bool) (i : Fin (n + 1))  :=
  decide (toInt s + Dd x y i = 1)

section

variable {x y : Finset (Fin (n + 1))}


theorem toInt_hOf  {s : Bool} (hs : ValidS x y s) (i : Fin (n + 1)) :
    toInt (hOf x y s i) = toInt s + Dd x y i := by
  grind +locals

theorem flux_hOf  {s : Bool} (hs : ValidS x y s) :
    Flux x y (hOf x y s) := by
  intro i
  induction i using Fin.cases with
  | zero =>
    rw [prv_zero, toInt_hOf hs, toInt_hOf hs, Dd_zero, hs.1]
    simp [eFlux]
    ring
  | succ i =>
    rw [prv_succ, toInt_hOf hs, toInt_hOf hs, Dd_succ]
    simp [eFlux]
    ring

theorem validS_of_flux  {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    ValidS x y (h (Fin.last n)) := by
  refine ⟨?_, fun i => ?_⟩
  · have := hf.eq_add_Dd (Fin.last n)
    omega
  · rw [← hf.eq_add_Dd i]
    cases h i <;> simp [toInt]

theorem hOf_last  {s : Bool} (hs : ValidS x y s) :
    hOf x y s (Fin.last n) = s := by
  grind +locals

theorem hOf_h_last  {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    hOf x y (h (Fin.last n)) = h := by
  funext i
  have := hf.eq_add_Dd i
  
  cases hi : h i
  · grind +locals
  · grind +locals

end

section

variable (x y : Finset (Fin (n + 1)))
include x y

/-- The number of solutions of the flux equation equals the number of admissible parameters. -/
theorem card_flux_eq  :
    (univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card =
      (univ.filter fun s : Bool => ValidS x y s).card := by
  symm
  refine Finset.card_nbij' (hOf x y) (fun h => h (Fin.last n)) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
    exact ⟨mem_univ _, flux_hOf hs.2⟩
  · intro h hh
    rw [Finset.mem_coe, Finset.mem_filter] at hh ⊢
    exact ⟨mem_univ _, validS_of_flux hh.2⟩
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter] at hs
    exact hOf_last hs.2
  · intro h hh
    rw [Finset.mem_coe, Finset.mem_filter] at hh
    exact hOf_h_last hh.2

theorem eq_iff_Dd_zero  : x = y ↔ ∀ i, Dd x y i = 0 := by
  constructor
  · rintro rfl i
    simp [Dd]
  · intro hD
    have he : ∀ i, eFlux x y i = 0 := by
      intro i
      induction i using Fin.cases with
      | zero => rw [← Dd_zero]; exact hD 0
      | succ j =>
        have := Dd_succ x y j
        simp_all
    ext i
    have := he i
    simp only [eFlux, toInt_decide_mem] at this
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp_all

theorem validS_false_iff  :
    ValidS x y false ↔ x.card = y.card ∧ ∀ t, cnt y t ≤ cnt x t ∧ cnt x t ≤ cnt y t + 1 := by
  unfold ValidS
  simp only [toInt, Bool.false_eq_true, ↓reduceIte, Dd_last]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun t => ?_⟩
    have := h2 t
    simp only [Dd] at this
    omega
  · grind +locals

theorem validS_true_iff  :
    ValidS x y true ↔ x.card = y.card ∧ ∀ t, cnt x t ≤ cnt y t ∧ cnt y t ≤ cnt x t + 1 := by
  unfold ValidS
  simp only [toInt, ↓reduceIte, Dd_last]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun t => ?_⟩
    have := h2 t
    simp only [Dd] at this
    omega
  · grind +locals

theorem interlaced_iff_validS  :
    Interlaced x y ↔ ValidS x y false ∨ ValidS x y true := by
  rw [interlaced_iff, validS_false_iff, validS_true_iff]
  aesop

/-- Lemma `lem:Interlacement` of the companion paper: the number of ice-rule horizontal arrow
configurations of a row between `x` and `y`. -/
theorem card_flux  :
    (univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card =
      if x = y then 2 else if Interlaced x y then 1 else 0 := by
  rw [card_flux_eq, Finset.card_filter, Fintype.sum_bool]
  by_cases hxy : x = y
  · grind +locals
  · have hnot : ¬ (ValidS x y false ∧ ValidS x y true) := by
      rintro ⟨h1, h2⟩
      apply hxy
      rw [eq_iff_Dd_zero]
      intro i
      rw [validS_false_iff] at h1
      rw [validS_true_iff] at h2
      have a := h1.2 i
      have b := h2.2 i
      simp only [Dd]
      omega
    have hI := interlaced_iff_validS x y
    grind

end

end

/-- `Ṽ = V`: the total weight of the ice-rule configurations of one row of vertices with the
vertical arrows prescribed by `x` below and `y` above equals the entry `V(x, y)` of (1.5)
(companion paper, Corollary `cor:MatrixEquality`). -/
theorem rowSum_eq_transferMatrix (hN : 0 < N) (c : ℝ) (x y : Finset (Fin N)) :
    rowSum c x y = transferMatrix N c x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  unfold rowSum
  simp_rw [rowWeight_eq]
  rw [← Finset.sum_filter, Finset.sum_const]
  
  
  rw [ card_flux x y , transferMatrix_apply]
  simp_all

end PottsDiscontinuity.SixVertex
