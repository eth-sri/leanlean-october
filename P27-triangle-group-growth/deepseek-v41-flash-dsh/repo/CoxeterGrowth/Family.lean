module
public import CoxeterGrowth.Instances

@[expose] public section
/-!
# The `(p, q, ∞)` family: monotonicity, minimality of `ρ`, and the growth rates

Write `a_{p,q}(n)` for the number of elements of length `n` in a Coxeter system of type
`(p, q, ∞)`.  We prove monotonicity and symmetry in `(p, q)`, the minimality of the plastic number
`ρ` in the family, the existence of the growth rate `τ_{p,q}` of every hyperbolic member and its
monotonicity, and that `τ_{p,q} → 2` as `p, q → ∞`.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries Filter Topology

/-- `S_m(x) = x + x² + ⋯ + x^{m-1}`. -/
abbrev S (m : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Ico 1 m, x ^ i

/-! ## Monotonicity and symmetry of the normal-form counts -/

theorem VT_mono (r : List ℕ) :
    ∀ {m₁ m₂ m₁' m₂' : ℕ}, m₁ ≤ m₁' → m₂ ≤ m₂' → VT m₁ m₂ r → VT m₁' m₂' r := by
  induction r with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons k r ih =>
    intro m₁ m₂ m₁' m₂' h1 h2 h
    simp only [VT] at h ⊢
    exact ⟨h.1, lt_of_lt_of_le h.2.1 h1, ih h2 h1 h.2.2⟩

theorem V_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (v : Raw) (h : V p q v) :
    V p' q' v := by
  rw [V_mk] at h ⊢
  exact ⟨⟨h.1.1, le_trans h.1.2 hp⟩, VT_mono v.2 hq hp h.2⟩

theorem NFs_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (n : ℕ) :
    NFs p q n ⊆ NFs p' q' n := fun v hv => by
  rw [mem_NFs] at hv ⊢
  exact ⟨V_mono hp hq v hv.1, hv.2⟩

theorem card_NFs_swap_le {p q : ℕ} (hq : 1 ≤ q) (n : ℕ) : (NFs p q n).card ≤ (NFs q p n).card := by
  refine Finset.card_le_card_of_injOn swap (fun v hv => ?_) (fun v hv w hw h => ?_)
  · rw [Finset.mem_coe, mem_NFs] at hv ⊢
    exact ⟨swap_V hq v hv.1, by rw [len_swap]; exact hv.2⟩
  · rw [Finset.mem_coe, mem_NFs] at hv hw
    rw [← swap_swap v hv.1, h, swap_swap w hw.1]

theorem card_NFs_swap {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (n : ℕ) :
    (NFs p q n).card = (NFs q p n).card :=
  le_antisymm (card_NFs_swap_le hq n) (card_NFs_swap_le hp n)

theorem VT_ones (n : ℕ) : ∀ {m₁ m₂ : ℕ}, 2 ≤ m₁ → 2 ≤ m₂ → VT m₁ m₂ (List.replicate n 1) := by
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro m₁ m₂ h1 h2
    rw [List.replicate_succ, VT]
    exact ⟨Nat.one_pos, h1, ih h2 h1⟩

/-- Every length carries a normal form (the alternating word with all blocks of length one). -/
theorem card_NFs_pos {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (n : ℕ) : 0 < (NFs p q n).card := by
  refine Finset.card_pos.2 ⟨((0, 0), List.replicate n 1), ?_⟩
  rw [mem_NFs, V_mk]
  exact ⟨⟨⟨by omega, by omega⟩, VT_ones n hq hp⟩, by simp [len]⟩

/-- The `(p, q, ∞)` hypotheses are met by `triM p q`. -/
theorem isTri_triM (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : IsTri (triM p q hp hq) p q :=
  ⟨hp, hq, rfl, rfl, rfl⟩

theorem card_NFs23_low (ρ : ℝ) (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ ((NFs 2 3 (n + 2)).card : ℝ) := by
  have h := (sphere23_growth (triM 2 3 le_rfl (by norm_num)).toCoxeterSystem rfl rfl rfl h1 h3 n).1
  unfold sphere at h
  rwa [sphere_eq_card _ (isTri_triM 2 3 le_rfl (by norm_num))] at h

/-- A hyperbolic pair with `p, q ≥ 2` has `p ≥ 3` or `q ≥ 3`. -/
theorem three_le_or {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : (p, q) ≠ (2, 2)) :
    3 ≤ p ∨ 3 ≤ q := by
  rcases Nat.lt_or_ge 2 p with hp3 | hp2
  · exact Or.inl hp3
  · exact Or.inr (by
      by_contra hc
      exact h (by rw [le_antisymm hp2 hp, show q = 2 by omega]))

/-- Every hyperbolic member dominates `(2, 3, ∞)` (if `p = 2`) or `(3, 2, ∞)` (if `p ≥ 3`). -/
theorem card_NFs23_le {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hne : (p, q) ≠ (2, 2)) (n : ℕ) :
    (NFs 2 3 n).card ≤ (NFs p q n).card := by
  rcases Nat.lt_or_ge 2 p with hp3 | hp2
  · rw [card_NFs_swap (by norm_num) (by norm_num) n]
    exact Finset.card_le_card (NFs_mono hp3 hq n)
  · have hq3 : 3 ≤ q := (three_le_or hp hq hne).resolve_left (by omega)
    obtain rfl : p = 2 := le_antisymm hp2 hp
    exact Finset.card_le_card (NFs_mono le_rfl hq3 n)

section Family

variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
  (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

/-- **Monotonicity**: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono {p q p' q' : ℕ} (hT : IsTri M p q) (hT' : IsTri M' p' q') (hp : p ≤ p')
    (hq : q ≤ q') (n : ℕ) : sphere cs n ≤ sphere cs' n := by
  rw [sphere, sphere, sphere_eq_card cs hT, sphere_eq_card cs' hT']
  exact Finset.card_le_card (NFs_mono hp hq n)

/-- **Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm {p q : ℕ} (hT : IsTri M p q) (hT' : IsTri M' q p) (n : ℕ) :
    sphere cs n = sphere cs' n := by
  rw [sphere, sphere, sphere_eq_card cs hT, sphere_eq_card cs' hT']
  exact card_NFs_swap (by have := hT.hp; omega) (by have := hT.hq; omega) n

/-- **Minimality of the plastic number in the family**. -/
theorem sphere_ge_plastic {p q : ℕ} (hT : IsTri M p q) (hne : (p, q) ≠ (2, 2)) {ρ : ℝ}
    (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (sphere cs (n + 2) : ℝ) := by
  rw [sphere, sphere_eq_card cs hT]
  exact le_trans (card_NFs23_low ρ h1 h3 n) (by exact_mod_cast card_NFs23_le hT.hp hT.hq hne (n + 2))

end Family

/-! ## The recursion of the sphere sizes -/

theorem coeff_numer_eq_zero (p q n : ℕ) (hn : p + q ≤ n) :
    coeff n ((1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i)) = 0 := by
  have h2 : (1 + X : ℤ⟦X⟧) = ∑ e ∈ range 2, X ^ e := by simp [add_comm]
  rw [h2]
  simp only [sum_mul, mul_sum, ← pow_add, map_sum, coeff_X_pow]
  refine sum_eq_zero fun a ha => sum_eq_zero fun b hb => sum_eq_zero fun c hc => ?_
  rw [mem_range] at ha hb hc
  rw [ite_eq_right (by omega)]

theorem coeff_denom (f : ℕ → ℤ) (p q n : ℕ) (hn : p + q ≤ n) :
    coeff n (mk f * (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i))) =
      f n - ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)) := by
  rw [mul_sub, mul_one, map_sub, coeff_mk, sum_mul_sum, mul_sum, map_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum, map_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Ico] at hi hj
  rw [← pow_add, coeff_mul_X_pow', coeff_mk, if_pos (by omega)]

/-- **The recursion**: a sequence with the `(p, q, ∞)` growth series satisfies
`f(n) = Σ_{1≤i<p} Σ_{1≤j<q} f(n − i − j)` for `n ≥ p + q`. -/
theorem rec_of_series (f : ℕ → ℕ) (p q : ℕ)
    (H : (PowerSeries.mk fun n => (f n : ℤ)) *
        (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i)) =
      (1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i))
    (n : ℕ) (hn : p + q ≤ n) : f n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)) := by
  have h := congrArg (coeff n) H
  rw [coeff_denom _ p q n hn, coeff_numer_eq_zero p q n hn] at h
  have h' : (f n : ℤ) = ((∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

/-! ## Exponential bounds from the recursion -/

theorem sum_pow_sub {p q n : ℕ} (hn : p + q ≤ n) {τ : ℝ} (hτ : τ ≠ 0)
    (heq : S p τ⁻¹ * S q τ⁻¹ = 1) :
    ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (n - (i + j)) = τ ^ n := by
  have key : ∀ i j : ℕ, i + j ≤ n → τ ^ (n - (i + j)) = τ ^ n * (τ⁻¹ ^ i * τ⁻¹ ^ j) := by
    intro i j h
    have hK : τ ^ (i + j) ≠ 0 := pow_ne_zero _ hτ
    calc τ ^ (n - (i + j)) = τ ^ (n - (i + j)) * (τ ^ (i + j) * (τ ^ (i + j))⁻¹) := by
          rw [mul_inv_cancel₀ hK, mul_one]
      _ = τ ^ n * (τ ^ (i + j))⁻¹ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      _ = τ ^ n * (τ⁻¹ ^ i * τ⁻¹ ^ j) := by simp only [inv_pow, pow_add, mul_inv]
  calc ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (n - (i + j))
      = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ n * (τ⁻¹ ^ i * τ⁻¹ ^ j) := by
        refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
        rw [mem_Ico] at hi hj
        exact key i j (by omega)
    _ = τ ^ n * (S p τ⁻¹ * S q τ⁻¹) := by
        rw [Finset.sum_mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
    _ = τ ^ n := by rw [heq, mul_one]

/-- Bounds `c τⁿ ≤ f(n) ≤ C τⁿ` for a sequence satisfying the `(p, q, ∞)` recursion. -/
theorem bounds_of_rec (f : ℕ → ℕ) {p q : ℕ} (hpos : ∀ n, 1 ≤ f n)
    (hrec : ∀ n, p + q ≤ n → f n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)))
    {τ : ℝ} (hτ : 1 < τ) (heq : (S p τ⁻¹) * (S q τ⁻¹) = 1)
    (n : ℕ) : (τ ^ (p + q))⁻¹ * τ ^ n ≤ (f n : ℝ) ∧
      (f n : ℝ) ≤ (∑ m ∈ range (p + q), (f m : ℝ)) * τ ^ n := by
  have hτ0 : 0 < τ := by linarith
  have hK : (0 : ℝ) < τ ^ (p + q) := by positivity
  have hC0 : (0 : ℝ) ≤ ∑ m ∈ range (p + q), (f m : ℝ) := sum_nonneg fun m _ => Nat.cast_nonneg _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n (p + q) with hn | hn
    · have h2 : (1 : ℝ) ≤ f n := by exact_mod_cast hpos n
      have h3 : (f n : ℝ) ≤ ∑ m ∈ range (p + q), (f m : ℝ) :=
        single_le_sum (fun m _ => Nat.cast_nonneg _) (mem_range.2 hn)
      refine ⟨?_, ?_⟩
      · have : (τ ^ (p + q))⁻¹ * τ ^ n ≤ 1 := by
          rw [inv_mul_le_iff₀ hK, mul_one]
          exact pow_le_pow_right₀ hτ.le hn.le
        linarith
      · exact h3.trans (le_mul_of_one_le_right hC0 (one_le_pow₀ hτ.le))
    · have key : ∀ i ∈ Ico 1 p, ∀ j ∈ Ico 1 q, n - (i + j) < n := by
        intro i hi j hj
        rw [mem_Ico] at hi hj
        omega
      refine ⟨?_, ?_⟩
      · rw [hrec n hn, ← sum_pow_sub hn hτ0.ne' heq, Finset.mul_sum]
        push_cast
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj => (ih _ (key i hi j hj)).1
      · rw [hrec n hn, ← sum_pow_sub hn hτ0.ne' heq, Finset.mul_sum]
        push_cast
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj => (ih _ (key i hi j hj)).2

/-! ## The rate equation -/

theorem sumIco_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S m x :=
  sum_nonneg fun i _ => pow_nonneg hx i

theorem sumIco_pos {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) : 0 < S m x := by
  have h : x ≤ S m x := by
    simpa using single_le_sum (f := fun i => x ^ i) (fun i _ => pow_nonneg hx.le i)
      (mem_Ico.2 ⟨le_rfl, hm⟩ : 1 ∈ Ico 1 m)
  exact lt_of_lt_of_le hx h

theorem sumIco_lt {m : ℕ} (hm : 2 ≤ m) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    S m x < S m y :=
  sum_lt_sum (fun i _ => pow_le_pow_left₀ hx hxy.le i)
    ⟨1, mem_Ico.2 ⟨le_rfl, hm⟩, by simpa using hxy⟩

theorem sumIco_le_of_le {m m' : ℕ} (h : m ≤ m') {x : ℝ} (hx : 0 ≤ x) :
    S m x ≤ ∑ i ∈ Ico 1 m', x ^ i :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right h) fun i _ _ => pow_nonneg hx i

theorem sumIco_lt_of_lt {m m' : ℕ} (hm : 1 ≤ m) (h : m < m') {x : ℝ} (hx : 0 < x) :
    S m x < ∑ i ∈ Ico 1 m', x ^ i :=
  sum_lt_sum_of_subset (Ico_subset_Ico_right h.le) (i := m) (mem_Ico.2 ⟨hm, h⟩)
    (by simp) (pow_pos hx m) (fun j _ _ => pow_nonneg hx.le j)

/-- `x ↦ S_p(x) S_q(x)` is strictly increasing on `[0, ∞)`. -/
theorem rateFn_lt {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    (S p x) * (S q x) <
      (S p y) * (S q y) :=
  mul_lt_mul'' (sumIco_lt hp hx hxy) (sumIco_lt hq hx hxy) (sumIco_nonneg p hx)
    (sumIco_nonneg q hx)

theorem rateFn_le {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (S p x) * (S q x) ≤
      (S p y) * (S q y) := by
  rcases hxy.lt_or_eq with h | h
  · exact (rateFn_lt hp hq hx h).le
  · rw [h]

theorem rateFn_inj {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hgx : (S p x) * (S q x) = 1)
    (hgy : (S p y) * (S q y) = 1) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := rateFn_lt hp hq hx h; linarith
  · exact h
  · have := rateFn_lt hp hq hy h; linarith

theorem sumIco_zero (m : ℕ) : S m ((0 : ℝ)) = 0 :=
  sum_eq_zero fun i hi => by rw [mem_Ico] at hi; exact zero_pow (by omega)

theorem sumIco_one (m : ℕ) : S m ((1 : ℝ)) = ((m - 1 : ℕ) : ℝ) := by simp [S]

/-- **Existence and uniqueness of the rate**: for `(p, q) ≠ (2, 2)` exactly one `τ > 1` solves
`S_p(τ⁻¹) S_q(τ⁻¹) = 1`. -/
theorem rate_exists_unique {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hne : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ (S p τ⁻¹) * (S q τ⁻¹) = 1 := by
  set F : ℝ → ℝ := fun x => (S p x) * (S q x) with hF
  have hcont : ContinuousOn F (Set.Icc 0 1) := by rw [hF]; fun_prop
  have h2 : 2 ≤ (p - 1) * (q - 1) := by
    rcases Nat.lt_or_ge 2 p with hp3 | hp2
    · calc 2 = 2 * 1 := rfl
        _ ≤ (p - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
    · have hq3 : 3 ≤ q := (three_le_or hp hq hne).resolve_left (by omega)
      obtain rfl : p = 2 := le_antisymm hp2 hp
      calc 2 = 1 * 2 := rfl
        _ ≤ (2 - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hF0 : F 0 = 0 := by
    show (S p ((0 : ℝ))) * (S q ((0 : ℝ))) = 0
    rw [sumIco_zero, zero_mul]
  have hF1 : (1 : ℝ) < F 1 := by
    show (1 : ℝ) < (S p ((1 : ℝ))) * (S q ((1 : ℝ)))
    rw [sumIco_one, sumIco_one, ← Nat.cast_mul]
    exact_mod_cast h2
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc zero_le_one hcont
    (show (1 : ℝ) ∈ Set.Icc (F 0) (F 1) by rw [hF0]; exact ⟨zero_le_one, hF1.le⟩)
  have hx0 : 0 < x := by
    rcases hx.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hF0] at hgx; exact absurd hgx zero_ne_one
  have hx1 : x < 1 := by
    rcases hx.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hgx; linarith
  refine ⟨x⁻¹, ⟨(one_lt_inv₀ hx0).2 hx1, by rw [inv_inv]; exact hgx⟩, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ := by linarith [hτ.1]
  rw [← rateFn_inj hp hq (inv_pos.2 hτ0).le hx0.le hτ.2 hgx, inv_inv]

/-! ## The growth rate of every member -/

section Rate

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

theorem sphere_rec {p q : ℕ} (hT : IsTri M p q) (n : ℕ) (hn : p + q ≤ n) :
    sphere cs n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, sphere cs (n - (i + j)) :=
  rec_of_series (sphere cs) p q (growth_series cs hT) n hn

theorem one_le_sphere {p q : ℕ} (hT : IsTri M p q) (n : ℕ) : 1 ≤ sphere cs n := by
  rw [sphere, sphere_eq_card cs hT]
  exact card_NFs_pos hT.hp hT.hq n

/-- **The growth rate of `(p, q, ∞)`**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate {p q : ℕ} (hT : IsTri M p q) {τ : ℝ} (hτ : 1 < τ)
    (heq : (S p τ⁻¹) * (S q τ⁻¹) = 1) :
    Tendsto (fun n : ℕ => (sphere cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  have hτ0 : 0 < τ := by linarith
  have hK : (0 : ℝ) < τ ^ (p + q) := by positivity
  have hC : (0 : ℝ) < ∑ m ∈ range (p + q), (sphere cs m : ℝ) :=
    lt_of_lt_of_le (show (0 : ℝ) < (sphere cs 0 : ℝ) by simp [sphere])
      (single_le_sum (fun m _ => Nat.cast_nonneg _)
        (mem_range.2 (show 0 < p + q by have := hT.hp; omega)))
  have hb := bounds_of_rec (sphere cs) (one_le_sphere cs hT) (sphere_rec cs hT) hτ heq
  exact CoxeterGrowth.root_tendsto_of_bounds (f := sphere cs) (τ := τ) (c := (τ ^ (p + q))⁻¹)
    (C := ∑ m ∈ range (p + q), (sphere cs m : ℝ)) hτ0.le (inv_pos.2 hK) hC
    (Eventually.of_forall fun n => (hb n).1) (Eventually.of_forall fun n => (hb n).2)

end Rate

/-! ## The rates as a function of `(p, q)` -/

/-- **Strict monotonicity of the rate** in `(p, q)`. -/
theorem rate_lt_rate {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) {τ τ' : ℝ} (hτ : 1 < τ) (hτ' : 1 < τ')
    (heq : (S p τ⁻¹) * (S q τ⁻¹) = 1)
    (heq' : (∑ i ∈ Ico 1 p', τ'⁻¹ ^ i) * (∑ i ∈ Ico 1 q', τ'⁻¹ ^ i) = 1) : τ < τ' := by
  have hx : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have hp' : 2 ≤ p' := le_trans hp hpp
  have hq' : 2 ≤ q' := le_trans hq hqq
  have hstep : (S p τ⁻¹) * (S q τ⁻¹) <
      (∑ i ∈ Ico 1 p', τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q', τ⁻¹ ^ i) := by
    have A0 := sumIco_pos hp hx
    have B0 := sumIco_pos hq hx
    rcases Nat.lt_or_ge p p' with h | h
    · have A' := sumIco_lt_of_lt (by omega) h hx
      have B := sumIco_le_of_le hqq hx.le
      calc _ < (∑ i ∈ Ico 1 p', τ⁻¹ ^ i) * (S q τ⁻¹) :=
            mul_lt_mul_of_pos_right A' B0
        _ ≤ _ := mul_le_mul_of_nonneg_left B (by linarith)
    · have hpe : p = p' := le_antisymm hpp h
      have hq'' : q < q' := lt_of_le_of_ne hqq (fun h' => hne (by rw [hpe, h']))
      have B' := sumIco_lt_of_lt (by omega) hq'' hx
      have A := sumIco_le_of_le hpp hx.le
      calc _ ≤ (∑ i ∈ Ico 1 p', τ⁻¹ ^ i) * (S q τ⁻¹) :=
            mul_le_mul_of_nonneg_right A B0.le
        _ < _ := mul_lt_mul_of_pos_left B' (by linarith)
  have hlt : τ'⁻¹ < τ⁻¹ := not_le.mp fun h => by
    have := rateFn_le hp' hq' hx.le h
    linarith
  exact (inv_lt_inv₀ (by linarith) (by linarith)).1 hlt

theorem sum_Ico_1_2_real (x : ℝ) : S 2 x = x := by simp [S]

theorem sum_Ico_1_3_real (x : ℝ) : S 3 x = x + x ^ 2 := by
  simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

/-- The `(2, 3)` rate equation is the plastic cubic. -/
theorem rate23_iff {τ : ℝ} (hτ : 0 < τ) :
    (S 2 τ⁻¹) * (S 3 τ⁻¹) = 1 ↔ τ ^ 3 = τ + 1 := by
  rw [sum_Ico_1_2_real, sum_Ico_1_3_real]
  have hi : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
  have key : τ⁻¹ * (τ⁻¹ + τ⁻¹ ^ 2) * τ ^ 3 = τ + 1 := by
    calc τ⁻¹ * (τ⁻¹ + τ⁻¹ ^ 2) * τ ^ 3 = (τ⁻¹ * τ) ^ 2 * τ + (τ⁻¹ * τ) ^ 3 := by ring
      _ = τ + 1 := by rw [hi]; ring
  have h3ne : τ ^ 3 ≠ 0 := pow_ne_zero _ hτ.ne'
  constructor
  · intro h
    rw [h, one_mul] at key
    exact key
  · intro h
    have h' : τ⁻¹ * (τ⁻¹ + τ⁻¹ ^ 2) * τ ^ 3 = 1 * τ ^ 3 := by rw [key, h, one_mul]
    exact mul_right_cancel₀ h3ne h'

/-- A rate `τ > 1` excludes the affine `(2, 2)`. -/
theorem ne22_of_rate {p q : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (heq : (S p τ⁻¹) * (S q τ⁻¹) = 1) : (p, q) ≠ (2, 2) := by
  intro h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  rw [sum_Ico_1_2_real] at heq
  have hx0 : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have hx1 : τ⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hτ
  nlinarith


/-- **The plastic number is the minimal rate** of the hyperbolic `(p, q, ∞)`, attained only at
`(2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {τ : ℝ} (hτ : 1 < τ)
    (heq : (S p τ⁻¹) * (S q τ⁻¹) = 1) {ρ : ℝ} (hρ : 1 < ρ)
    (hρ3 : ρ ^ 3 = ρ + 1) : ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have hne := ne22_of_rate hτ heq
  have hρ23 : (S 2 ρ⁻¹) * (S 3 ρ⁻¹) = 1 :=
    (rate23_iff (by linarith)).2 hρ3
  have hρ32 : (S 3 ρ⁻¹) * (S 2 ρ⁻¹) = 1 := by
    rw [mul_comm]; exact hρ23
  by_cases h23 : (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)
  · have hτρ : τ = ρ := by
      rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h3 := (rate23_iff (by linarith)).1 heq
        rw [plasticNumber_unique hτ h3, plasticNumber_unique hρ hρ3]
      · rw [mul_comm] at heq
        have h3 := (rate23_iff (by linarith)).1 heq
        rw [plasticNumber_unique hτ h3, plasticNumber_unique hρ hρ3]
    exact ⟨hτρ.ge, iff_of_true hτρ h23⟩
  · have hlt : ρ < τ := by
      rcases Nat.lt_or_ge 2 p with hp3 | hp2
      · refine rate_lt_rate (by norm_num) le_rfl hp3 hq ?_ hρ hτ hρ32 heq
        intro h
        exact h23 (Or.inr ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
      · obtain rfl : p = 2 := le_antisymm hp2 hp
        have hq3 : 3 ≤ q := (three_le_or hp hq hne).resolve_left (by omega)
        refine rate_lt_rate le_rfl (by norm_num) le_rfl hq3 ?_ hρ hτ hρ23 heq
        intro h
        exact h23 (Or.inl ⟨rfl, (Prod.mk.inj h).2.symm⟩)
    exact ⟨hlt.le, iff_of_false hlt.ne' h23⟩

theorem sumIco_half_lt {m : ℕ} (hm : 1 ≤ m) : S m ((2⁻¹ : ℝ)) < 1 := by
  have h := geom_sum_Ico_mul_neg (2⁻¹ : ℝ) hm
  have hpos : 0 < (2⁻¹ : ℝ) ^ m := by positivity
  rw [pow_one] at h
  linarith

/-- **Every rate is below 2.** -/
theorem rate_lt_two {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {τ : ℝ} (hτ : 1 < τ)
    (heq : (S p τ⁻¹) * (S q τ⁻¹) = 1) : τ < 2 := by
  have hy : (0 : ℝ) ≤ 2⁻¹ := by norm_num
  have hg : (S p ((2⁻¹ : ℝ))) * (S q ((2⁻¹ : ℝ))) < 1 := by
    have hB : (S q ((2⁻¹ : ℝ))) < 1 := sumIco_half_lt (by omega)
    have hA : (S p ((2⁻¹ : ℝ))) < 1 := sumIco_half_lt (by omega)
    nlinarith [sumIco_nonneg p hy, sumIco_nonneg q hy]
  have hlt : (2⁻¹ : ℝ) < τ⁻¹ := by
    by_contra hle
    rw [not_lt] at hle
    have hx : (0 : ℝ) ≤ τ⁻¹ := le_of_lt (inv_pos.2 (by linarith))
    have := rateFn_le (x := τ⁻¹) (y := 2⁻¹) hp hq hx hle
    linarith
  exact (inv_lt_inv₀ (by norm_num) (by linarith)).1 hlt

/-- **The rates tend to 2**: for every `σ < 2`, all `(p, q)` with `p, q ≥ N` have rate `> σ`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) : ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q →
    ∀ τ : ℝ, 1 < τ → (S p τ⁻¹) * (S q τ⁻¹) = 1 → σ < τ := by
  rcases le_or_gt σ 1 with h1 | h1
  · exact ⟨0, fun p q _ _ τ hτ _ => lt_of_le_of_lt h1 hτ⟩
  have hσ0 : 0 < σ := by linarith
  have hy0 : 0 < σ⁻¹ := inv_pos.2 hσ0
  have hy1 : σ⁻¹ < 1 := (inv_lt_one₀ hσ0).2 h1
  have hy2 : 0 < 2 * σ⁻¹ - 1 := by
    have : (2 : ℝ)⁻¹ < σ⁻¹ := (inv_lt_inv₀ (by norm_num) hσ0).2 hσ
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hy2 hy1
  have hS : ∀ m, max N 2 ≤ m → 1 < S m σ⁻¹ := fun m hm => by
    have hmN : N ≤ m := le_trans (le_max_left _ _) hm
    have h := geom_sum_Ico_mul_neg σ⁻¹ (show 1 ≤ m by omega)
    rw [pow_one] at h
    have hym : σ⁻¹ ^ m ≤ σ⁻¹ ^ N := pow_le_pow_of_le_one hy0.le hy1.le hmN
    by_contra hc
    rw [not_lt] at hc
    have h' := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ 1 - σ⁻¹ by linarith)
    linarith
  refine ⟨max N 2, fun p q hp hq τ hτ heq => ?_⟩
  have hp2 : 2 ≤ p := le_trans (le_max_right _ _) hp
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  by_contra hcon
  rw [not_lt] at hcon
  have h1' : σ⁻¹ ≤ τ⁻¹ := (inv_le_inv₀ hσ0 (by linarith)).2 hcon
  have h2' := rateFn_le (x := σ⁻¹) (y := τ⁻¹) hp2 hq2 hy0.le h1'
  have h3' := hS p hp
  have h4' := hS q hq
  have h5' := sumIco_nonneg p hy0.le
  nlinarith

end CoxeterGrowth.Triangle
