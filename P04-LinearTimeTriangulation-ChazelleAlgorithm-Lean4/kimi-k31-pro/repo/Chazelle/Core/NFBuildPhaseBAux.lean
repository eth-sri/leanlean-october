module

public import Chazelle.Core.NFBuildPhaseBSetup

/-!
# WP-C (BuildNF), RAM part 21: auxiliary facts for phase B

* the size of the list table: `offF_R_le` (`off R ≤ A + 2K`);
* congruence of the counting functions (`lstF_congr`, …);
* `twice_m_le`: the counted interval of a chain descriptor fits the word bound.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

theorem sum_ind (k R : ℕ) :
    ((List.range R).map fun r => if k = r then 1 else 0).sum = if k < R then 1 else 0 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

theorem sum_cntF (key : ℕ → ℕ) {n R : ℕ} (h : ∀ j, j < n → key j < R) :
    ((List.range R).map (cntF key n)).sum = n := by
  induction n with
  | zero => simp [show cntF key 0 = fun _ => 0 from funext fun r => rfl]
  | succ n ih =>
    have e : (List.range R).map (cntF key (n + 1)) =
        (List.range R).map fun r => cntF key n r + (if key n = r then 1 else 0) := by
      apply List.map_congr_left; intro r _; exact cntF_succ key n r
    rw [e, List.sum_map_add, ih (fun j hj => h j (by omega)), sum_ind, ite_eq_left (h n (by omega))]

theorem sum_cnt2F_le (u v : ℕ → ℕ) (n R : ℕ) : ((List.range R).map (cnt2F u v n)).sum ≤ 2 * n := by
  induction n with
  | zero => simp [show cnt2F u v 0 = fun _ => 0 from funext fun r => rfl]
  | succ n ih =>
    have e : (List.range R).map (cnt2F u v (n + 1)) =
        (List.range R).map fun r => cnt2F u v n r + (if u n = r ∨ v n = r then 1 else 0) := by
      apply List.map_congr_left; intro r _; exact cnt2F_succ u v n r
    have hle : ((List.range R).map fun r => if u n = r ∨ v n = r then 1 else 0).sum ≤ 2 := by
      have : ∀ r, (if u n = r ∨ v n = r then 1 else 0) ≤
          (if u n = r then 1 else 0) + (if v n = r then 1 else 0) := fun r => by split_ifs <;> omega
      calc _ ≤ ((List.range R).map fun r =>
              (if u n = r then 1 else 0) + (if v n = r then 1 else 0)).sum :=
            List.sum_le_sum (fun r _ => this r)
        _ = _ := by rw [List.sum_map_add]
        _ ≤ 2 := by rw [sum_ind, sum_ind]; split_ifs <;> omega
    rw [e, List.sum_map_add]
    omega

theorem offF_eq (cA cC : ℕ → ℕ) (R : ℕ) :
    offF cA cC R = ((List.range R).map cA).sum + ((List.range R).map cC).sum := by
  unfold offF; rw [List.sum_map_add]

/-- **The size of the list table.** -/
theorem offF_R_le (key u v : ℕ → ℕ) {A K R : ℕ} (h : ∀ j, j < A → key j < R) :
    offF (cntF key A) (cnt2F u v K) R ≤ A + 2 * K := by
  rw [offF_eq, sum_cntF key h]
  have := sum_cnt2F_le u v K R
  omega

theorem lstF_congr {key key' : ℕ → ℕ} {n : ℕ} (h : ∀ j, j < n → key j = key' j) (r : ℕ) :
    lstF key n r = lstF key' n r := by
  unfold lstF
  apply List.filter_congr
  intro j hj
  rw [h j (List.mem_range.1 hj)]

theorem cntF_congr {key key' : ℕ → ℕ} {n : ℕ} (h : ∀ j, j < n → key j = key' j) :
    cntF key n = cntF key' n := by
  funext r; unfold cntF; rw [lstF_congr h]

theorem wmaxF_congr {key key' w w' : ℕ → ℕ} {n : ℕ} (h : ∀ j, j < n → key j = key' j)
    (hw : ∀ j, j < n → w j = w' j) : wmaxF key w n = wmaxF key' w' n := by
  funext r
  unfold wmaxF
  rw [lstF_congr h]
  congr 1
  apply List.map_congr_left
  intro j hj
  unfold lstF at hj
  exact hw j (List.mem_range.1 (List.mem_filter.1 hj).1)

theorem lst2F_congr {u v u' v' : ℕ → ℕ} {n : ℕ} (hu : ∀ i, i < n → u i = u' i)
    (hv : ∀ i, i < n → v i = v' i) (r : ℕ) : lst2F u v n r = lst2F u' v' n r := by
  unfold lst2F
  apply List.filter_congr
  intro i hi
  rw [hu i (List.mem_range.1 hi), hv i (List.mem_range.1 hi)]

theorem cnt2F_congr {u v u' v' : ℕ → ℕ} {n : ℕ} (hu : ∀ i, i < n → u i = u' i)
    (hv : ∀ i, i < n → v i = v' i) : cnt2F u v n = cnt2F u' v' n := by
  funext r; unfold cnt2F; rw [lst2F_congr hu hv]

/-- The counted interval of a chain descriptor fits the word bound. -/
theorem twice_m_le {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {D : ℕ} {M : Model}
    (hM : ModelDescAt m D (Qof P) M) (hCW : LocChainWF P W m D) (h0 : m D = 0) :
    2 * m (D + 3) ≤ W := by
  rcases hM with ⟨-, H, C, hC, -⟩ | ⟨h1, -, -⟩
  · obtain ⟨-, -, -, -, h2⟩ := hCW h0 H C hC
    have hm : m (D + 1 + 2) = C.m := hC.2.2.2.1
    rw [show D + 3 = D + 1 + 2 by omega, hm]
    have := C.m_lt
    omega
  · omega

end

end BuildRam

end Chazelle.Core
