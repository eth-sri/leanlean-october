module
public import CoxeterGrowth.Triangle

@[expose] public section
namespace TriangleGrowth

open CoxeterGrowth.Triangle Finset Filter Topology

scoped notation:max "Rate[" p "," q "," τ "]" => (F[p,q,(τ : ℝ)⁻¹] = 1)

lemma geom_compare (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (S[m,x] - 1) * (1-x) = 2*x-1-x^m := by
  linear_combination geom_sum_Ico_mul_neg x hm

lemma rate23_iff {ρ : ℝ} (hρ : 0 < ρ) : Rate[2,3,ρ] ↔ ρ^3 = ρ+1 := by
  simp [sum_Ico_eq_sum_range, sum_range_succ]
  field_simp
  ring_nf
  exact eq_comm

section
variable {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
include hp hq

lemma labels_strict (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p,q) ≠ (p',q')) {x : ℝ} (hx : 0 < x) : F[p,q,x] < F[p',q',x] := by
  rw [← offset_sum, ← offset_sum]
  have hs : offsets p q ⊆ offsets p' q' := product_subset_product (Ico_subset_Ico_right hpp) (Ico_subset_Ico_right hqq)
  refine sum_lt_sum_of_subset hs (i := if p < p' then (p,1) else (1,q)) ?_ ?_
    (by positivity) (fun _ _ _ => by positivity)
  all_goals split <;> simp [offsets] <;> grind

lemma kernel_anti :
    StrictAntiOn (fun τ : ℝ => F[p,q,τ⁻¹]) (Set.Ici 1) := by
  intro x hx y _ hxy
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have h := inv_strictAnti₀ hx' hxy
  simp only [← offset_sum]
  refine sum_lt_sum_of_nonempty ⟨(1,1), by grind [offsets]⟩ fun _ hu => ?_
  exact pow_lt_pow_left₀ h (inv_nonneg.2 (hx'.trans hxy).le) (offset_bounds hu).1.ne'

lemma kernel_two : F[p,q,(2⁻¹ : ℝ)] < 1 := by
  have hS (m : ℕ) (hm : 1 ≤ m) : S[m,(2⁻¹ : ℝ)] < 1 := by
    have := geom_compare (2⁻¹ : ℝ) m hm
    norm_num at this
    linarith [pow_pos (show 0 < (2⁻¹ : ℝ) by norm_num) m]
  simpa using mul_lt_mul'' (hS p (by omega)) (hS q (by omega)) (by positivity) (by positivity)

/-- There is exactly one rate greater than one, and it lies in `(1,2)`. -/
theorem rate_exists_unique (hpq : (p,q) ≠ (2,2)) :
    ∃! τ : ℝ, 1 < τ ∧ Rate[p,q,τ] := by
  obtain ⟨τ,hτ,he⟩ := intermediate_value_Ioo' (f := fun τ : ℝ => F[p,q,τ⁻¹])
    (by norm_num : (1 : ℝ) ≤ 2) (by fun_prop (disch := grind))
    ⟨kernel_two hp hq, by simpa using labels_strict (p := 2) (q := 2) le_rfl le_rfl hp hq hpq.symm zero_lt_one⟩
  exact ⟨τ, ⟨hτ.1, he⟩, fun _ h => (kernel_anti hp hq).injOn h.1.le hτ.1.le (h.2.trans he.symm)⟩

/-- Increasing either finite label strictly increases the growth rate. -/
theorem rate_lt_rate (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p,q) ≠ (p',q')) (τ τ' : ℝ) (hτ : 1 < τ) (hτ' : 1 < τ')
    (he : Rate[p,q,τ]) (he' : Rate[p',q',τ']) : τ < τ' := by
  rw [← (kernel_anti (hp.trans hpp) (hq.trans hqq)).lt_iff_gt hτ'.le hτ.le, he', ← he]
  exact labels_strict hp hq hpp hqq hne (by positivity)

section
variable (τ : ℝ) (hτ : 1 < τ) (he : Rate[p,q,τ])
include hτ he

/-- The minimum occurs precisely at `(2,3)` and `(3,2)`. -/
theorem plastic_le_rate
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) : ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have hf : ¬(p = 2 ∧ q = 2) := by
    rintro ⟨rfl,rfl⟩
    have := inv_lt_one_of_one_lt₀ hτ
    have : 0 < τ⁻¹ := by positivity
    simp at he
    nlinarith
  wlog hq' : 3 ≤ q generalizing p q with H
  · have hh := H hq hp (by simpa [mul_comm] using he) (by tauto : ¬(q = 2 ∧ p = 2)) (by omega)
    simpa [and_comm, or_comm] using hh
  have h23 := (rate23_iff (show 0 < ρ by positivity)).2 hρ3
  rcases eq_or_ne (p,q) (2,3) with h | h
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    have ht := (kernel_anti (p := 2) (q := 3) le_rfl (by decide)).injOn hτ.le hρ.le (he.trans h23.symm)
    simp [ht]
  · have ht := rate_lt_rate (p := 2) (q := 3) le_rfl (by decide) hp hq' h.symm
      ρ τ hρ hτ h23 he
    grind

/-- Every finite pair has rate less than `2`. -/
theorem rate_lt_two : τ < 2 := by
  rw [← (kernel_anti hp hq).lt_iff_gt (by norm_num : (1 : ℝ) ≤ 2) hτ.le, he]
  exact kernel_two hp hq

end
end

/-- The plastic number is the rate for `(2,3,∞)`. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  exact (existsUnique_congr fun ρ => and_congr_right fun h => rate23_iff (zero_lt_one.trans h)).1
    (rate_exists_unique (p := 2) (q := 3) le_rfl (by decide) (by decide))

/-- For sufficiently large finite labels the growth rate exceeds any `σ < 2`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) :
    ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q → ∀ τ : ℝ, 1 < τ → Rate[p,q,τ] → σ < τ := by
  rcases le_or_gt σ 1 with h | h
  · exact ⟨0, fun _ _ _ _ _ hτ _ => h.trans_lt hτ⟩
  have hx' : σ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
  have hhalf : 2⁻¹ < σ⁻¹ := by gcongr
  obtain ⟨N,hN⟩ := eventually_atTop.1
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hx').eventually_lt_const
      (show 0 < 2*σ⁻¹-1 by linarith))
  have hS (m : ℕ) (hm : N+2 ≤ m) : 1 < S[m,σ⁻¹] := by
    nlinarith [geom_compare σ⁻¹ m (by omega), hN m (by omega)]
  refine ⟨N+2, fun p q hp hq τ hτ he => ?_⟩
  rw [← (kernel_anti (show 2 ≤ p by omega) (show 2 ≤ q by omega)).lt_iff_gt hτ.le h.le, he]
  simpa using mul_lt_mul'' (hS p hp) (hS q hq) zero_le_one zero_le_one

section
variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

local notation:max "a[" n "]" => sphere(cs,n)

/-- The normalized sphere sizes satisfy an averaging recurrence with positive weights. -/
theorem sphere_root_tendsto_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h01 : M 0 1 = 0)
    (h02 : M 0 2 = p) (h12 : M 1 2 = q) (τ : ℝ) (hτ : 1 < τ) (he : Rate[p,q,τ]) :
    Tendsto (fun n : ℕ => (a[n] : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  simp only [sphere_card cs ⟨hp,hq,h01,h02,h12⟩]
  let g (n : ℕ) := (nfCount p q n : ℝ) / τ^n
  let w (u : ℕ × ℕ) := τ⁻¹ ^ hl u
  have hw := (offset_sum p q τ⁻¹).trans he
  have hg (n : ℕ) (hn : p+q ≤ n) : g n = ∑ u ∈ offsets p q, w u * g (n-hl u) := by
    simp only [g, slice_rec (show 1 ≤ q by omega) hn, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun u hu => ?_
    dsimp [w]
    rw [inv_pow, inv_mul_eq_div, div_div, ← pow_add, Nat.sub_add_cancel ((offset_bounds hu).2.le.trans hn)]
  have hpos (n : ℕ) : 0 < g n := div_pos (by exact_mod_cast slice_pos hp hq n) (by positivity)
  have hb : (range (p+q)).Nonempty := nonempty_range_iff.2 (by omega)
  obtain ⟨i,_,hi⟩ := exists_min_image _ g hb
  obtain ⟨j,_,hj⟩ := exists_max_image _ g hb
  have bounds (n : ℕ) : g n ∈ Set.Icc (g i) (g j) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < p+q
      · exact ⟨hi n (mem_range.2 h), hj n (mem_range.2 h)⟩
      rw [hg n (by omega)]
      exact (convex_Icc (g i) (g j)).sum_mem (fun _ _ => by positivity) hw
        (fun u hu => ih (n-hl u) (by have := offset_bounds hu; omega))
  have hlim {c : ℝ} (hc : 0 < c) : Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat (Or.inl hc.ne')
  have hg' := tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim (hpos i)) (hlim (hpos j))
    (fun n => Real.rpow_le_rpow (hpos i).le (bounds n).1 (by positivity))
    (fun n => Real.rpow_le_rpow (hpos n).le (bounds n).2 (by positivity))
  rw [← one_mul τ]
  refine (hg'.mul_const τ).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp (disch := positivity) [g, Real.div_rpow, Real.pow_rpow_inv_natCast, div_mul_cancel₀]

end
end TriangleGrowth
