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

theorem nxt_castSucc {n : ℕ} (i : Fin n) : nxt (Fin.castSucc i) = Fin.succ i := by
  simp [nxt]

theorem prv_succ {n : ℕ} (i : Fin n) : prv (Fin.succ i) = Fin.castSucc i := by
  simp only [prv]
  rw [Equiv.symm_apply_eq]
  exact (nxt_castSucc i).symm

theorem prv_zero {n : ℕ} : prv (0 : Fin (n + 1)) = Fin.last n := by
  simp only [prv]
  rw [Equiv.symm_apply_eq]
  simp

/-! ### Counting functions along the cycle -/

theorem cnt_zero {n : ℕ} (x : Finset (Fin (n + 1))) :
    cnt x 0 = if (0 : Fin (n + 1)) ∈ x then 1 else 0 := by
  unfold cnt
  rw [show x.filter (· ≤ 0) = if (0 : Fin (n + 1)) ∈ x then {0} else ∅ by
    ext a; simp only [mem_filter, nonpos_iff_eq_zero]
    split_ifs with h <;> [exact ⟨fun h => mem_singleton.mpr h.2, fun ha => ⟨mem_singleton.mp ha ▸ h, mem_singleton.mp ha⟩⟩;
      exact iff_of_false (fun ⟨ha, heq⟩ => h (heq ▸ ha)) (notMem_empty a)]]
  split_ifs <;> simp

theorem cnt_succ {n : ℕ} (x : Finset (Fin (n + 1))) (i : Fin n) :
    cnt x (Fin.succ i) = cnt x (Fin.castSucc i) + if Fin.succ i ∈ x then 1 else 0 := by
  unfold cnt
  rw [show x.filter (· ≤ Fin.succ i) =
      if Fin.succ i ∈ x then insert (Fin.succ i) (x.filter (· ≤ Fin.castSucc i))
      else x.filter (· ≤ Fin.castSucc i) by
    ext a
    split_ifs with h <;> simp only [mem_filter, mem_insert, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    · exact ⟨fun ⟨ha, hle⟩ => (Nat.le_succ_iff.mp hle).elim (fun h1 => Or.inr ⟨ha, h1⟩)
        (fun h1 => Or.inl (Fin.ext h1)),
        fun h' => h'.elim (fun h1 => h1 ▸ ⟨h, le_rfl⟩) (fun ⟨ha, _⟩ => ⟨ha, by omega⟩)⟩
    · exact ⟨fun ⟨ha, hle⟩ => ⟨ha, (Nat.le_succ_iff.mp hle).resolve_right fun h1 => h ((Fin.ext h1 : a = i.succ) ▸ ha)⟩,
        fun ⟨ha, _⟩ => ⟨ha, by omega⟩⟩]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_last {n : ℕ} (x : Finset (Fin (n + 1))) : cnt x (Fin.last n) = x.card := by
  unfold cnt; congr 1; exact filter_true_of_mem fun a _ => Fin.le_last a

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

/-- The weight of a row of vertices with horizontal arrows `h`, up arrows `x` below and `y`
above (`a = b = 1`). -/
def rowWeight (c : ℝ) (x y : Finset (Fin N)) (h : Fin N → Bool) : ℝ :=
  ∏ i : Fin N, localWeight 1 1 c (h (prv i)) (h i) (decide (i ∈ x)) (decide (i ∈ y))

/-- The total weight `Ṽ(x, y)` of the ice-rule row configurations between `x` and `y`. -/
def rowSum (c : ℝ) (x y : Finset (Fin N)) : ℝ := ∑ h : Fin N → Bool, rowWeight c x y h

theorem inDegree_eq_two_iff (l r d u : Bool) :
     inDegree l r d u = 2 ↔ toInt r = toInt l + toInt d - toInt u := by
  cases l <;> cases r <;> cases d <;> cases u <;> simp [inDegree, toInt]

theorem prod_ite_vertical (c : ℝ) (x y : Finset (Fin N)) :
    (∏ i : Fin N, if decide (i ∈ x) = decide (i ∈ y) then (1 : ℝ) else c) =
      c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2; refine Finset.filter_congr fun i _ => ?_
  by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp [Psi, hx, hy]

theorem rowWeight_eq (c : ℝ) (x y : Finset (Fin N)) (h : Fin N → Bool) :
    rowWeight c x y h =
      if Flux x y h then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0 := by
  unfold rowWeight
  simp_rw [localWeight_one_one, inDegree_eq_two_iff]
  rw [Finset.prod_ite_zero]
  simp only [mem_univ, forall_const, ← prod_ite_vertical]
  rfl

/-! ### Solving the flux equation -/

section Count

variable {n : ℕ}

@[simp] theorem toInt_decide_mem {α : Type*} [DecidableEq α] (a : α) (x : Finset α) :
    toInt (decide (a ∈ x)) = if a ∈ x then 1 else 0 := by
  by_cases h : a ∈ x <;> simp [toInt, h]

/-- `D(i) = cnt x i - cnt y i`: the accumulated flux up to position `i`. -/
def Dd (x y : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℤ := (cnt x i : ℤ) - cnt y i

/-- The flux increment at position `i`. -/
def eFlux (x y : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℤ :=
  toInt (decide (i ∈ x)) - toInt (decide (i ∈ y))

theorem Dd_zero (x y : Finset (Fin (n + 1))) : Dd x y 0 = eFlux x y 0 := by
  simp [Dd, eFlux, cnt_zero]

theorem Dd_succ (x y : Finset (Fin (n + 1))) (i : Fin n) :
    Dd x y (Fin.succ i) = Dd x y (Fin.castSucc i) + eFlux x y (Fin.succ i) := by
  simp only [Dd, eFlux, cnt_succ, toInt_decide_mem]; push_cast; ring

theorem Dd_last (x y : Finset (Fin (n + 1))) : Dd x y (Fin.last n) = (x.card : ℤ) - y.card := by
  simp [Dd, cnt_last]

/-- Every solution of the flux equation is `h(i) = h(last) + D(i)`. -/
theorem Flux.eq_add_Dd {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    ∀ i, toInt (h i) = toInt (h (Fin.last n)) + Dd x y i := by
  intro i
  induction i using Fin.induction with
  | zero => rw [hf 0, prv_zero, Dd_zero]; simp [eFlux]; ring
  | succ i ih => rw [hf (Fin.succ i), prv_succ, ih, Dd_succ]; simp [eFlux]; ring

/-- A solution of the flux equation forces `|x| = |y|`. -/
theorem Flux.card_eq {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    x.card = y.card := by
  have := hf.eq_add_Dd (Fin.last n); rw [Dd_last] at this; omega

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
  unfold hOf
  rcases hs.2 i with h | h <;> rw [h] <;> simp [toInt]

theorem flux_hOf {x y : Finset (Fin (n + 1))} {s : Bool} (hs : ValidS x y s) :
    Flux x y (hOf x y s) := by
  intro i
  induction i using Fin.cases with
  | zero => rw [prv_zero, toInt_hOf hs, toInt_hOf hs, Dd_zero, hs.1]; simp [eFlux]; ring
  | succ i => rw [prv_succ, toInt_hOf hs, toInt_hOf hs, Dd_succ]; simp [eFlux]; ring

theorem validS_of_flux {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    ValidS x y (h (Fin.last n)) :=
  ⟨by have := hf.eq_add_Dd (Fin.last n); omega,
   fun i => by rw [← hf.eq_add_Dd i]; cases h i <;> simp [toInt]⟩

theorem hOf_last {x y : Finset (Fin (n + 1))} {s : Bool} (hs : ValidS x y s) :
    hOf x y s (Fin.last n) = s := by
  have := toInt_hOf hs (Fin.last n)
  rw [hs.1] at this
  cases s <;> cases h : hOf x y _ (Fin.last n) <;> simp_all [toInt]

theorem hOf_h_last {x y : Finset (Fin (n + 1))} {h : Fin (n + 1) → Bool} (hf : Flux x y h) :
    hOf x y (h (Fin.last n)) = h := by
  funext i
  unfold hOf
  rw [← hf.eq_add_Dd i]
  cases h i <;> simp [toInt]

/-- The number of solutions of the flux equation equals the number of admissible parameters. -/
theorem card_flux_eq (x y : Finset (Fin (n + 1))) :
    (univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card =
      (univ.filter fun s : Bool => ValidS x y s).card :=
  (Finset.card_nbij' (hOf x y) (fun h => h (Fin.last n))
    (fun _ hs => mem_coe.mpr <| mem_filter.mpr ⟨mem_univ _, flux_hOf (mem_filter.mp hs).2⟩)
    (fun _ hh => mem_coe.mpr <| mem_filter.mpr ⟨mem_univ _, validS_of_flux (mem_filter.mp hh).2⟩)
    (fun _ hs => hOf_last (mem_filter.mp hs).2)
    (fun _ hh => hOf_h_last (mem_filter.mp hh).2)).symm

theorem eq_iff_Dd_zero (x y : Finset (Fin (n + 1))) : x = y ↔ ∀ i, Dd x y i = 0 := by
  refine ⟨by rintro rfl _; simp [Dd], fun hD => ?_⟩
  ext i
  have he : eFlux x y i = 0 := by
    induction i using Fin.cases with
    | zero => rw [← Dd_zero]; exact hD 0
    | succ j => have := Dd_succ x y j; rw [hD, hD] at this; omega
  simp only [eFlux, toInt_decide_mem] at he
  by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp_all

theorem validS_false_iff (x y : Finset (Fin (n + 1))) :
    ValidS x y false ↔ x.card = y.card ∧ ∀ t, cnt y t ≤ cnt x t ∧ cnt x t ≤ cnt y t + 1 := by
  rw [ValidS, Dd_last]
  simp only [toInt, Bool.false_eq_true, ↓reduceIte, zero_add, Dd]
  exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, fun t => by have := h2 t; omega⟩,
    fun ⟨h1, h2⟩ => ⟨by omega, fun t => by have := h2 t; omega⟩⟩

theorem validS_true_iff (x y : Finset (Fin (n + 1))) :
    ValidS x y true ↔ x.card = y.card ∧ ∀ t, cnt x t ≤ cnt y t ∧ cnt y t ≤ cnt x t + 1 := by
  rw [ValidS, Dd_last]
  simp only [toInt, ↓reduceIte, Dd]
  exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, fun t => by have := h2 t; omega⟩,
    fun ⟨h1, h2⟩ => ⟨by omega, fun t => by have := h2 t; omega⟩⟩

theorem interlaced_iff_validS (x y : Finset (Fin (n + 1))) :
    Interlaced x y ↔ ValidS x y false ∨ ValidS x y true := by
  rw [interlaced_iff, validS_false_iff, validS_true_iff, ← and_or_left]

/-- Lemma `lem:Interlacement` of the companion paper: the number of ice-rule horizontal arrow
configurations of a row between `x` and `y`. -/
theorem card_flux (x y : Finset (Fin (n + 1))) :
    (univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card =
      if x = y then 2 else if Interlaced x y then 1 else 0 := by
  rw [card_flux_eq, Finset.card_filter, Fintype.sum_bool]
  by_cases hxy : x = y
  · subst hxy
    simp [(validS_false_iff x x).2 ⟨rfl, fun _ => ⟨le_rfl, Nat.le_succ _⟩⟩,
      (validS_true_iff x x).2 ⟨rfl, fun _ => ⟨le_rfl, Nat.le_succ _⟩⟩]
  · have hnot : ¬ (ValidS x y false ∧ ValidS x y true) := fun ⟨h1, h2⟩ => hxy <|
      (eq_iff_Dd_zero x y).mpr fun i => by
        have := (validS_false_iff x y).mp h1 |>.2 i
        have := (validS_true_iff x y).mp h2 |>.2 i
        simp only [Dd]; omega
    simp only [interlaced_iff_validS]
    by_cases h1 : ValidS x y false <;> by_cases h2 : ValidS x y true <;>
      simp_all

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
  change ((univ.filter fun h : Fin (n + 1) → Bool => Flux x y h).card : ℝ) * _ = _
  rw [card_flux x y, transferMatrix_apply]
  split_ifs with h1 <;> [subst h1; skip; skip] <;> simp

end PottsDiscontinuity.SixVertex
