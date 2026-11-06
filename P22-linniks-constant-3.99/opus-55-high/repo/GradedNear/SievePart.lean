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

open Complex Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open NearData

/-- The sieve part of `D(δ)`. -/
def sieveDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D.m,
    D.h k * Real.exp (-2 * δ * D.t k) * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)

lemma mem_cell {q n : ℕ} (hq : 2 ≤ q) {t t' : ℝ} :
    n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊ ↔ 1 ≤ n ∧ t ≤ tn q n ∧ tn q n < t' := by
  have hq0 : (0 : ℝ) < q := by positivity
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [(Real.rpow_pos_of_pos hq0 t).not_ge]
  have key : ∀ s, (q : ℝ) ^ s ≤ n ↔ s ≤ tn q n := fun s => by
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hq0 s) (mod_cast hn),
      Real.log_rpow hq0, tn, le_div_iff₀ (log_q_pos hq)]
  grind

/-- **The sieve part of the second factor.** -/
theorem sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessBound) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ,
        (∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / Real.log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  obtain ⟨CB, V₀, hCB, hdiagG⟩ := sieve_diagonal hGr
  obtain ⟨CC, κ, hCC, hκ, qC, hoffC⟩ := sieve_offdiag hBur (tmax := D.t D.m) hD.ε'_pos
  have hS := strictMonoOn_Iic_of_lt_succ hD.t_lt
  have ht : ∀ k ≤ D.m, 1 / 3 + 2 * D.ε' < D.t k := fun k hk =>
    hD.t_zero.trans_le (hS.monotoneOn (by simp) hk (Nat.zero_le k))
  have hlev : ∀ k < D.m, 0 < D.level k ∧ D.level k < D.t k := fun k hk => by
    have := ht k hk.le; unfold NearData.level; constructor <;> linarith [hD.ε'_pos]
  set err : ℕ → ℕ → ℝ := fun k q => CB * D.t (k + 1) ^ 2 / D.level k ^ 2 * (Real.log q)⁻¹ +
    CB / D.level k ^ 2 * (Real.log q)⁻¹ ^ 3 + CC * ((q : ℝ) ^ (-κ) * (Real.log q)⁻¹) +
    2 * D.level k * (q : ℝ) ^ (-(D.t k - D.level k)) with herr
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hL
  have hp : ∀ {c : ℝ}, 0 < c → Tendsto (fun q : ℕ => (q : ℝ) ^ (-c)) atTop (𝓝 0) := fun hc =>
    (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q => ∑ k ∈ Finset.range D.m, D.h k * err k q) atTop (𝓝 0) := by
    simpa [herr] using tendsto_finsetSum (Finset.range D.m) fun k hk =>
      ((((hinv.const_mul (CB * D.t (k + 1) ^ 2 / D.level k ^ 2)).add
        ((hinv.pow 3).const_mul (CB / D.level k ^ 2))).add (((hp hκ).mul hinv).const_mul CC)).add
        ((hp (sub_pos.2 (hlev k (Finset.mem_range.1 hk)).2)).const_mul
          (2 * D.level k))).const_mul (D.h k)
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.1 ((hlim.eventually_le_const hε).and
    (((Finset.eventually_all _).2 fun k hk => ((tendsto_rpow_atTop (hlev k
      (Finset.mem_range.1 hk)).1).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop V₀).and
    ((hL.eventually_ge_atTop (2 * ∑ δ ∈ D.Δ, δ)).and (eventually_ge_atTop (max qC 2)))))
  refine ⟨q₀, fun q hq T hT hTq ι _ E hγ hΔ hinj a ha N => ?_⟩
  obtain ⟨hqE, hqV, hqβ, hqC⟩ := hq₀ q hq
  simp only [max_le_iff, Function.comp] at hqC hqV hqβ
  have hq1 : (1 : ℝ) < q := by norm_cast; omega
  have hq0 := one_pos.trans hq1
  have hℓ := log_q_pos hqC.2
  have hδ : ∀ j, 0 ≤ E.δ j := fun j => hD.Δ_nonneg _ (hΔ j)
  rw [div_le_iff₀ hℓ]
  simp only [NearData.sieveH, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ k ∈ Finset.range D.m, Real.log q * ((D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k) *
        ∑ j, Real.exp (-2 * E.δ j * D.t k) * a j ^ 2 + err k q * (∑ j, a j) ^ 2) * D.h k :=
        Finset.sum_le_sum fun k hk => ?_
    _ = (∑ j, sieveDiag D (E.δ j) * a j ^ 2 +
        (∑ k ∈ Finset.range D.m, D.h k * err k q) * (∑ j, a j) ^ 2) * Real.log q := by
      simp only [sieveDiag, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      grind
    _ ≤ _ := by gcongr
  have hk' := Finset.mem_range.1 hk
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, ← Finset.sum_filter, mul_right_comm _ (D.h k),
    ← Finset.sum_mul]
  rcases eq_or_ne (D.h k) 0 with h0 | h0
  · simp_all
  refine mul_le_mul_of_nonneg_right ?_ (hD.h_nonneg k hk')
  obtain ⟨hl0, hlt⟩ := hlev k hk'
  have hV1 : 1 < (q : ℝ) ^ D.level k := Real.one_lt_rpow hq1 hl0
  have hVA := Real.rpow_le_rpow_of_exponent_le hq1.le hlt.le
  have hAB := Real.rpow_le_rpow_of_exponent_le hq1.le (hD.t_lt k hk').le
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_cell (t' := D.t (k + 1))
    hqC.2).2 ?_) fun n _ _ => by positivity).trans ((cell_bound E a ha hδ hqC.2 _ (D.t k) _
    (CC * (q : ℝ) ^ (-κ)) _ _ (fun n hn => ((mem_cell hqC.2).1 hn).1)
    (fun n hn => ((mem_cell hqC.2).1 hn).2.1) _
    (fun _ => ite_nonneg ArithmeticFunction.vonMangoldt_nonneg le_rfl)
    (fun n _ => vonMangoldt_le_sieve hV1 n) ((Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => ?_) fun n _ _ => mul_nonneg (by positivity) (sieveNu_nonneg ..)).trans
      (hdiagG _ _ _ (hqV k hk) hVA hAB)) (fun j j' hjj' => ?_)
    (by simpa [Finset.sum_filter, ite_div] using small_primepow_sum hV1.le (hV1.le.trans hVA))
    (by positivity)).trans ?_)
  · grind
  · simp at hn ⊢
    exact ⟨hn.1, Nat.le_floor (Nat.lt_ceil.1 hn.2).le⟩
  · simpa only [mul_assoc, NearData.level] using hoffC q hqC.1 _ (fun h => hjj' (hinj ⟨k, hk', h0⟩
      (mul_inv_eq_one.1 h))) _ _ _ _ (ht k hk'.le) (hD.t_lt k hk').le (hS.monotoneOn hk' (by simp) hk')
      (div_nonneg (add_nonneg (hδ j) (hδ j')) hℓ.le) (by rw [div_le_one hℓ]; linarith [Finset.single_le_sum hD.Δ_nonneg (hΔ j), Finset.single_le_sum hD.Δ_nonneg (hΔ j')]) (by grind)
  have hY : ∑ j, Real.exp (-2 * E.δ j * D.t k) * a j ^ 2 ≤ (∑ j, a j) ^ 2 :=
    (Finset.sum_le_sum fun j _ => mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.2
      (by nlinarith [hδ j]))).trans
      (Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => ha j)
  simp only [mul_comm (Real.exp _), mul_assoc, ← Finset.mul_sum, Real.log_rpow hq0] at hY ⊢
  calc _ = _ - CB * ((D.t (k + 1) * Real.log q) ^ 2 + 1) / (D.level k * Real.log q) ^ 2 *
      ((∑ j, a j) ^ 2 - ∑ j, a j ^ 2 * Real.exp (-2 * (E.δ j * D.t k))) := by
        simp only [herr, Real.rpow_neg hq0.le, Real.rpow_sub hq0]
        grind
    _ ≤ _ := sub_le_self _ (mul_nonneg (by positivity) (sub_nonneg.2 hY))

end GradedNear
