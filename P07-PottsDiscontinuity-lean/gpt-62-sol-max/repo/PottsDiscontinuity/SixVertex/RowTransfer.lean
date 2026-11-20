module

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

theorem prv_succ {n : ℕ} (i : Fin n) : prv (Fin.succ i) = Fin.castSucc i := by
  simp only [prv]
  rw [Equiv.symm_apply_eq]
  simp

theorem prv_zero {n : ℕ} : prv (0 : Fin (n + 1)) = Fin.last n := rfl

section

variable {n : ℕ} (x : Finset (Fin (n + 1)))

/-! ### Counting functions along the cycle -/

theorem cnt_zero :
    cnt x 0 = if (0 : Fin (n + 1)) ∈ x then 1 else 0 := by
  unfold cnt
  have : x.filter (· ≤ 0) = if (0 : Fin (n + 1)) ∈ x then {0} else ∅ := by
    ext a
    simp only [mem_filter, nonpos_iff_eq_zero]
    split_ifs with h
    · simp_all
    aesop
  rw [this]
  split_ifs <;> simp

theorem cnt_succ (i : Fin n) :
    cnt x (Fin.succ i) = cnt x (Fin.castSucc i) + if Fin.succ i ∈ x then 1 else 0 := by
  unfold cnt
  have : x.filter (· ≤ Fin.succ i) =
      if Fin.succ i ∈ x then insert (Fin.succ i) (x.filter (· ≤ Fin.castSucc i))
      else x.filter (· ≤ Fin.castSucc i) := by
    grind
  rw [this]
  split_ifs with h
  · simp
  · rfl

theorem cnt_last : cnt x (Fin.last n) = x.card := by
  unfold cnt
  congr 1
  apply filter_true_of_mem
  intro a _
  exact Fin.le_last a

end

/-! ### The flux equation -/

/-- `1` for `true` and `0` for `false`, as an integer. -/
def toInt (b : Bool) : ℤ := if b then 1 else 0

/-- The ice rule on a row, in terms of the horizontal arrows `h` (`h i = true`: the edge from `i`
to `i + 1` points right), the up arrows `x` below and `y` above the row:
`h(i) = h(i - 1) + [i ∈ x] - [i ∈ y]` for all `i`. -/
def Flux (x y : Finset (Fin N)) (h : Fin N → Bool) : Prop :=
  ∀ i, toInt (h i) = toInt (h (prv i)) + toInt (decide (i ∈ x)) - toInt (decide (i ∈ y))

instance (x y : Finset (Fin N)) (h : Fin N → Bool) : Decidable (Flux x y h) := by
  unfold Flux; infer_instance

section

variable (c : ℝ) (x y : Finset (Fin N))

/-- The weight of a row of vertices with horizontal arrows `h`, up arrows `x` below and `y`
above (`a = b = 1`). -/
def rowWeight (h : Fin N → Bool) : ℝ :=
  ∏ i : Fin N, localWeight 1 1 c (h (prv i)) (h i) (decide (i ∈ x)) (decide (i ∈ y))

/-- The total weight `Ṽ(x, y)` of the ice-rule row configurations between `x` and `y`. -/
def rowSum : ℝ := ∑ h : Fin N → Bool, rowWeight c x y h

end

theorem inDegree_eq_two_iff (l r d u : Bool) :
    inDegree l r d u = 2 ↔ toInt r = toInt l + toInt d - toInt u := by
  grind [inDegree, toInt]

section

variable (c : ℝ) (x y : Finset (Fin N))

theorem prod_ite_vertical :
    (∏ i : Fin N, if decide (i ∈ x) = decide (i ∈ y) then (1 : ℝ) else c) =
      c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have : (univ.filter fun i => ¬ (decide (i ∈ x) = decide (i ∈ y))) =
      (univ.filter fun i => Psi x i ≠ Psi y i) := by
    refine Finset.filter_congr fun i _ => ?_
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp [Psi, hy]
  rw [this]

theorem rowWeight_eq (h : Fin N → Bool) :
    rowWeight c x y h =
      if Flux x y h then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0 := by
  have key : rowWeight c x y h =
      if Flux x y h then (∏ i : Fin N, if decide (i ∈ x) = decide (i ∈ y) then (1 : ℝ) else c)
      else 0 := by
    unfold rowWeight
    simp_rw [localWeight_one_one, inDegree_eq_two_iff]
    rw [Finset.prod_ite_zero]
    simp only [mem_univ, forall_const]
    rfl
  rw [key]
  by_cases hf : Flux x y h
  · simp only [hf, ↓reduceIte]
    exact prod_ite_vertical c x y
  · simp [hf]

end

/-! ### Solving the flux equation -/

section Count

variable {n : ℕ}

@[simp] theorem toInt_decide_mem {α : Type*} [DecidableEq α] (a : α) (x : Finset α) :
    toInt (decide (a ∈ x)) = if a ∈ x then 1 else 0 := by
  aesop

section

variable (x y : Finset (Fin (n + 1)))

/-- `D(i) = cnt x i - cnt y i`: the accumulated flux up to position `i`. -/
def Dd (i : Fin (n + 1)) : ℤ := (cnt x i : ℤ) - cnt y i

/-- The flux increment at position `i`. -/
def eFlux (i : Fin (n + 1)) : ℤ :=
  toInt (decide (i ∈ x)) - toInt (decide (i ∈ y))

theorem Dd_zero : Dd x y 0 = eFlux x y 0 := by
  simp [Dd, eFlux, cnt_zero]

theorem Dd_succ (i : Fin n) :
    Dd x y (Fin.succ i) = Dd x y (Fin.castSucc i) + eFlux x y (Fin.succ i) := by
  simp [Dd, eFlux, cnt_succ]
  ring

theorem Dd_last : Dd x y (Fin.last n) = (x.card : ℤ) - y.card := by
  simp [Dd, cnt_last]

end

/-- Every solution of the flux equation is `h(i) = h(last) + D(i)`. -/
theorem Flux.eq_add_Dd {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
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
theorem Flux.card_eq {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    x.card = y.card := by
  have := hf.eq_add_Dd (Fin.last n)
  rw [Dd_last] at this
  omega

/-- The parameter `s ∈ {0, 1}` (the value of the arrow entering position `0`) is admissible. -/
def ValidS (x y : Finset (Fin (n + 1))) (s : Bool) : Prop :=
  Dd x y (Fin.last n) = 0 ∧ ∀ i, toInt s + Dd x y i = 0 ∨ toInt s + Dd x y i = 1

instance (x y : Finset (Fin (n + 1))) (s : Bool) : Decidable (ValidS x y s) := by
  unfold ValidS; infer_instance

/-- The explicit solution `h(i) = s + D(i)` of the flux equation. -/
def hOf (x y : Finset (Fin (n + 1))) (s : Bool) (i : Fin (n + 1)) : Bool :=
  decide (toInt s + Dd x y i = 1)

theorem toInt_hOf {x y : Finset (Fin (n + 1))} {s : Bool} (hs : ValidS x y s) (i : Fin (n + 1)) :
    toInt (hOf x y s i) = toInt s + Dd x y i := by
  rcases hs.2 i with h | h
  · simp_all [toInt, hOf]
  · unfold hOf
    aesop

theorem flux_hOf {x y : Finset (Fin (n + 1))} {s : Bool} (hs : ValidS x y s) :
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

theorem validS_of_flux {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    ValidS x y (h (Fin.last n)) := by
  refine ⟨?_, fun i => ?_⟩
  · have := hf.eq_add_Dd (Fin.last n)
    omega
  · rw [← hf.eq_add_Dd i]
    cases h i <;> trivial

theorem hOf_last {x y : Finset (Fin (n + 1))} {s : Bool} (hs : ValidS x y s) :
    hOf x y s (Fin.last n) = s := by
  have := toInt_hOf hs (Fin.last n)
  rw [hs.1] at this
  grind [toInt]

theorem hOf_h_last {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    hOf x y (h (Fin.last n)) = h := by
  funext i
  have := hf.eq_add_Dd i
  unfold hOf
  grind [toInt]

section

variable (x y : Finset (Fin (n + 1)))

/-- The number of solutions of the flux equation equals the number of admissible parameters. -/
theorem card_flux_eq :
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

theorem eq_iff_Dd_zero : x = y ↔ ∀ i, Dd x y i = 0 := by
  constructor
  · rintro rfl i
    simp [Dd]
  · intro hD
    have he : ∀ i, eFlux x y i = 0 := by
      intro i
      induction i using Fin.cases with
      | zero => simpa [← Dd_zero] using hD 0
      | succ j =>
        have := Dd_succ x y j
        simp_all
    ext i
    have := he i
    grind [eFlux, toInt_decide_mem]

theorem validS_false_iff :
    ValidS x y false ↔ x.card = y.card ∧ ∀ t, cnt y t ≤ cnt x t ∧ cnt x t ≤ cnt y t + 1 := by
  unfold ValidS
  simp only [toInt, Bool.false_eq_true, ↓reduceIte, zero_add, Dd_last]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun t => ?_⟩
    have := h2 t
    simp only [Dd] at this
    omega
  · rintro ⟨h1, h2⟩
    grind [Dd]

theorem validS_true_iff :
    ValidS x y true ↔ x.card = y.card ∧ ∀ t, cnt x t ≤ cnt y t ∧ cnt y t ≤ cnt x t + 1 := by
  unfold ValidS
  simp only [toInt, ↓reduceIte, Dd_last]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun t => ?_⟩
    have := h2 t
    simp only [Dd] at this
    omega
  · rintro ⟨h1, h2⟩
    grind [Dd]

theorem interlaced_iff_validS :
    Interlaced x y ↔ ValidS x y false ∨ ValidS x y true := by
  grind [interlaced_iff, validS_false_iff, validS_true_iff]

/-- Lemma `lem:Interlacement` of the companion paper: the number of ice-rule horizontal arrow
configurations of a row between `x` and `y`. -/
theorem card_flux :
    (univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card =
      if x = y then 2 else if Interlaced x y then 1 else 0 := by
  rw [card_flux_eq, Finset.card_filter, Fintype.sum_bool]
  by_cases hxy : x = y
  · subst hxy
    have hf := (validS_false_iff x x).2 ⟨rfl, fun t => ⟨le_rfl, Nat.le_succ _⟩⟩
    have ht := (validS_true_iff x x).2 ⟨rfl, fun t => ⟨le_rfl, Nat.le_succ _⟩⟩
    simp_all
  · have hnot : ¬ (ValidS x y false ∧ ValidS x y true) := by
      rintro ⟨h1, h2⟩
      apply hxy
      rw [eq_iff_Dd_zero]
      grind [Dd, validS_true_iff, validS_false_iff]
    have hI := interlaced_iff_validS x y
    grind

end

end Count

/-- `Ṽ = V`: the total weight of the ice-rule configurations of one row of vertices with the
vertical arrows prescribed by `x` below and `y` above equals the entry `V(x, y)` of (1.5)
(companion paper, Corollary `cor:MatrixEquality`). -/
theorem rowSum_eq_transferMatrix (hN : 0 < N) (c : ℝ) (x y : Finset (Fin N)) :
    rowSum c x y = transferMatrix N c x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  unfold rowSum
  simp_rw [rowWeight_eq]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have := card_flux x y
  change ((univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card : ℝ) * _ = _
  rw [this, transferMatrix_apply]
  simp_all

end PottsDiscontinuity.SixVertex
