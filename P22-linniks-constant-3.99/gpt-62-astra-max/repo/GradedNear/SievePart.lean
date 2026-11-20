module

public import GradedNear.SieveCell
public import GradedNear.SieveDiagonal
public import GradedNear.SieveOffDiagonal
public import GradedNear.SieveMajorant

/-!
# The sieve part of the second Cauchy–Schwarz factor

`𝓛⁻¹ Σ_{n ≤ N} (Λ(n)/n) H(t_n) |Y_n|² ≤ Σ_j S(δ_j) a_j² + ε (Σ a)²` for all large `q`, where
`S(δ) = Σ_k h_k e^{-2δ t_k} (t_{k+1}² - t_k²)/(2 λ_k)` is the sieve part of `D(δ)`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open NearData Finset Filter

/-- Open the histogram and enlarge each truncated sum to its full cell. -/
private lemma sum_cells_le (D : NearData) (hD : D.Valid) {q : ℕ} (hq : 2 ≤ q)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, D.sieveH (tn q n) * f n ≤
      ∑ k ∈ range D.m, D.h k * ∑ n ∈ cell q (D.t k) (D.t (k+1)), f n := by
  simp_rw [NearData.sieveH, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_le_sum fun k hk => ?_
  rw [← sum_filter, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hD.h_nonneg _ (mem_range.mp hk))
  apply sum_le_sum_of_subset_of_nonneg _ fun n _ _ => hf n
  intro n hn
  obtain ⟨hi, ht, hu⟩ := mem_filter.mp hn
  have h1 := (mem_Icc.mp hi).1
  exact mem_Icc.mpr ⟨Nat.ceil_le.mpr ((le_tn_iff hq h1).mp ht), Nat.le_floor
    ((Real.logb_le_iff_le_rpow (by exact_mod_cast hq) (by exact_mod_cast h1)).mp hu.le)⟩

/-- **The sieve part of the second factor.** -/
theorem sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessPrimitive) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ {ι : Type} [Fintype ι] (E : Entries q ι) (_ : Window D E),
      ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ,
        (∑ n ∈ Finset.Icc 1 N, primeMass n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / Real.log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  have ht k (hk : k ≤ D.m) : 1/3+2*D.ε' < D.t k := by
    induction k with
    | zero => exact hD.t_zero
    | succ k ih => exact (ih (by omega)).trans (hD.t_lt k (by omega))
  have hε' := hD.ε'_pos
  let W := ∑ k ∈ range D.m, D.h k
  have hW : 0 ≤ W := sum_nonneg fun k hk => hD.h_nonneg _ (mem_range.mp hk)
  let e := ε / (2*(1+W))
  have he : 0 < e := by positivity
  have hv k (hk : k < D.m) : 0 < D.level k := by unfold level; linarith [ht k hk.le]
  have hvt k (hk : k < D.m) : D.level k < D.t k := by unfold level; linarith [ht k hk.le]
  let mass k := (D.t (k+1)^2 - D.t k^2) / (2*D.level k)
  have cells k (h : k ∈ range D.m) := (sieve_diagonal hGr (hv k (mem_range.mp h))
    (hvt k (mem_range.mp h)).le (hD.t_lt k (mem_range.mp h)).le he).and
    (sieve_offdiag hBur hε' (ht k (mem_range.mp h).le) (hD.t_lt k (mem_range.mp h)).le he)
  filter_upwards [(eventually_all_finset _).mpr cells, eventually_ge_atTop 2,
    log_level_atTop.eventually_ge_atTop (2*∑ δ ∈ D.Δ, δ), log_level_atTop.eventually_ge_atTop (ppMass/e)] with q H hq hsum hpp
  have hℓ := log_q_pos hq
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  intro ι _ E w hinj a ha N
  have hδ j := hD.Δ_nonneg _ (w.offsets j)
  let damp j k := Real.exp (-2 * E.δ j * D.t k)
  let A := (∑ j, a j)^2
  rw [div_le_iff₀ hℓ]
  conv_lhs => simp only [mul_comm (primeMass _) (D.sieveH _), mul_assoc]
  apply (sum_cells_le D hD hq _ (fun n => by positivity) N).trans
  calc _ ≤ ∑ k ∈ range D.m, D.h k * ((∑ j, damp j k * mass k * a j^2) * Real.log q + (e*Real.log q + ppMass)*A) := by
          refine sum_le_sum fun k hk => ?_
          by_cases hz : D.h k = 0
          · aesop
          obtain ⟨hd, ho⟩ := H k hk
          have hk := mem_range.mp hk
          apply mul_le_mul_of_nonneg_left _ (hD.h_nonneg k hk)
          have hV := Real.one_lt_rpow hq1 (hv k hk)
          refine cell_bound E a ha hδ hq _ hV (fun n hn => ?_) (by linarith [ht k hk.le]) (by positivity) ?_ ?_
          · have low := Nat.ceil_le.mp (mem_Icc.mp hn).1
            have hl := (Real.rpow_lt_rpow_of_exponent_lt hq1 (hvt k hk)).trans_le low
            exact ⟨hl, (le_tn_iff hq (by exact_mod_cast (hV.trans hl).le)).mpr low⟩
          · exact hd.trans_eq (add_mul ..)
          · intro j l hj
            have hb := div_nonneg (add_nonneg (hδ j) (hδ l)) hℓ.le
            have ht' : (E.δ j+E.δ l)/Real.log q ≤ 1 := (div_le_one hℓ).mpr (by
              linarith [single_le_sum hD.Δ_nonneg (w.offsets j), single_le_sum hD.Δ_nonneg (w.offsets l)])
            apply ho _ (fun h => hj (hinj ⟨k,hk,hz⟩ (mul_inv_eq_one.mp h)))
            · simp only [sievePoint, point_re, neg_div, sub_neg_eq_add]; linarith
            · apply (Complex.norm_le_abs_re_add_abs_im _).trans
              simp only [sievePoint, point_re, point_im, neg_div, sub_neg_eq_add, abs_of_nonneg (add_nonneg zero_le_one hb)]
              linarith [w.gap j l, w.cap]
       _ = (∑ j, sieveDiag D (E.δ j)*a j^2)*Real.log q + W*((e*Real.log q + ppMass)*A) := by
          simp_rw [mul_add, sum_add_distrib, ← mul_assoc, ← sum_mul, mul_sum]
          rw [sum_comm]; congr! 2 with j _ k
          simp [mass, damp, sum_mul, div_eq_mul_inv, mul_assoc]
       _ ≤ _ := by
          have hp : ppMass ≤ e*Real.log q := by simpa [mul_comm] using (div_le_iff₀ he).mp hpp
          have he' : W * (2*e) ≤ ε := by dsimp [e]; field_simp; linarith
          rw [add_mul (∑ j, _) _ (Real.log q)]; apply add_le_add (le_refl _)
          grw [hp]; change _ ≤ ε * A * Real.log q; linear_combination A * Real.log q * he'

end GradedNear
