import GradedNear.Tactics

import GradedNear.SieveCell
import GradedNear.SieveDiagonal
import GradedNear.SieveOffDiagonal
import GradedNear.SieveMajorant
import GradedNear.SieveError

/-!
# The sieve part of the second Cauchy–Schwarz factor

`𝓛⁻¹ Σ_{n ≤ N} (Λ(n)/n) H(t_n) |Y_n|² ≤ Σ_j S(δ_j) a_j² + ε (Σ a)²` for all large `q`, where
`S(δ) = Σ_k h_k e^{-2δ t_k} (t_{k+1}² - t_k²)/(2 λ_k)` is the sieve part of `D(δ)`.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

set_option maxHeartbeats 1000000 in
/-- **The sieve part of the second factor.** -/
theorem sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessBound) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), HeightBound E T → Offsets E D →
      SieveDistinct E D →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ,
        (∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / Real.log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  obtain ⟨CB, V₀, -, hdiagG⟩ := sieve_diagonal hGr
  obtain ⟨CC, κ, hκ, qC, hoffC⟩ := sieve_offdiag hBur (tmax := D.t D.m) hD.ε'_pos
  have t_mono_le {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ D.m) :
      D.t k ≤ D.t l := (strictMonoOn_Iic_of_lt_succ hD.t_lt).monotoneOn (hkl.trans hl) hl hkl
  have ht0k : ∀ k < D.m, ⅓ + 2 * D.ε' < D.t k := fun k hk =>
    lt_of_lt_of_le hD.t_zero  (by bound)
  have hlev_pos : ∀ k < D.m, 0 < D.level k := fun k hk => by
    unfold NearData.level; linarith [ht0k k hk]
  have hlev_lt : ∀ k < D.m, D.level k < D.t k := fun k hk => by
    grind [GradedNear.NearData.level, GradedNear.NearData.Valid.ε'_pos]
  have hqE : ∀ᶠ q : ℕ in Filter.atTop,
      ∑ k ∈ Finset.range D.m, D.h k * (|CB| * D.t (k + 1) ^ 2 / (D.level k ^ 2 * Real.log q) +
        |CB| / (D.level k ^ 2 * Real.log q ^ 3) + |CC| * ↑q ^ (-κ) / Real.log q +
          2 * D.level k * ↑q ^ (D.level k - D.t k)) ≤ ε := by
    apply Filter.Tendsto.eventually_le_const hε
    rw [show (0 : ℝ) = ∑ k ∈ Finset.range D.m, D.h k * (0 + 0 + 0 + 0) by simp]
    refine tendsto_finsetSum _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    refine Filter.Tendsto.const_mul _ ?_


    convert (((tendsto_inv_log_nat.const_mul (|CB| * D.t (k + 1) ^ 2 / D.level k ^ 2)).add
      ((tendsto_inv_log_nat.pow 3).const_mul (|CB| / D.level k ^ 2))).add
      (((tendsto_rpow_neg_nat hκ).mul tendsto_inv_log_nat).const_mul |CC|)).add
      ((tendsto_rpow_neg_nat (sub_pos.2 (hlev_lt k hk'))).const_mul (2 * D.level k)) using 1 <;> (try funext q) <;> ring

  filter_upwards [Filter.eventually_atTop.2 ⟨qC, hoffC⟩,
    hqE,  by
      exact (Finset.eventually_all _).2 fun k hk =>
        ((tendsto_rpow_atTop (hlev_pos k (Finset.mem_range.1 hk))).comp
          tendsto_natCast_atTop_atTop).eventually_ge_atTop V₀
     ,
    tendsto_log_nat_atTop.eventually_ge_atTop (2 * ∑ δ ∈ D.Δ, δ),
    Filter.eventually_ge_atTop (2 : ℕ)] with q hoffq hEq hVq hlogq hq2
  intro T hT hTq ι _ E hγ hΔ hinj a ha N
  set mass2 := (∑ j, a j) ^ 2
  have hℓ := log_q_pos hq2
  have hq0 : (0 : ℝ) < q := by positivity
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq2
  have cell_mem {t t' : ℝ} {n : ℕ}
      (hn : n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊) : 1 ≤ n ∧ t ≤ tn q n := by
    rw [Finset.mem_Ico] at hn
    have h1 : 1 ≤ n := by
      grind [Nat.ceil_pos, Real.rpow_pos_of_pos]
    refine ⟨h1, ?_⟩
    exact (Real.le_logb_iff_rpow_le hqR
      (by positivity : (0 : ℝ) < n)).2 (by simp_all)
  have hδ := fun j => hD.Δ_nonneg _ (hΔ j)

  have hycomp (j : ι) (n : ℕ) :
      ‖ycomp E a j n‖ ≤ a j * Real.exp (- E.δ j * tn q n) := by
    simpa [ycomp, norm_mul, Complex.norm_exp, abs_of_nonneg (ha j), mul_assoc, -Complex.natCast_log] using
      mul_le_of_le_one_right (mul_nonneg (ha j) (Real.exp_pos (- E.δ j * tn q n)).le)
        (DirichletCharacter.norm_le_one (E.χ j) (n : ZMod q))

  have hβ : ∀ j j', (E.δ j + E.δ j') / Real.log q ≤ 1 := by
    intro j j'
    rw [div_le_one hℓ]
    have h1 := Finset.single_le_sum hD.Δ_nonneg (hΔ j)
    have h2 := Finset.single_le_sum hD.Δ_nonneg (hΔ j')
    bound
  have hτ : ∀ j j', |E.γ j - E.γ j'| ≤ Real.log q := by grind
  simp_rw [NearData.sieveH, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  set Dk : ℕ → ℝ := fun k => Real.log q * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k) +
    |CB| * (D.t (k + 1) ^ 2 * Real.log q ^ 2 + 1) / (D.level k ^ 2 * Real.log q ^ 2)
  set Pk : ℕ → ℝ := fun k => 2 * ↑q ^ D.level k * (D.level k * Real.log q) /
    ↑q ^ D.t k
  have hcell : ∀ k ∈ Finset.range D.m,
       ∑ n ∈ Finset.Icc 1 N, Λ n / n *
        (if D.t k ≤ tn q n ∧ tn q n < D.t (k + 1) then D.h k else 0) * ‖Yn E a n‖ ^ 2 ≤
      D.h k * (∑ j, Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 +
        (|CC| * ↑q ^ (-κ) + Pk k) * mass2) := by
    intro k hk
    conv_lhs =>
      simp only [mul_ite, ite_mul, mul_zero, zero_mul]
      rw [← Finset.sum_filter]
      arg 2
      ext n
      rw [mul_comm (Λ n / n) (D.h k), mul_assoc]
    rw [← Finset.mul_sum]
    have hk' := Finset.mem_range.1 hk
    by_cases hk0 : D.h k = 0
    · simp [hk0]
    have hinj' := hinj ⟨k, hk', hk0⟩
    set A : ℝ := ↑q ^ D.t k
    set B : ℝ := ↑q ^ D.t (k + 1)
    refine mul_le_mul_of_nonneg_left ?_ (hD.h_nonneg k hk')
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ico ⌈A⌉₊ ⌈B⌉₊) ?_ ?_).trans ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, -⟩, ht, ht'⟩ := hn
      rw [Finset.mem_Ico]
      have hnR : (0 : ℝ) < n := by positivity
      exact ⟨Nat.ceil_le.2 ((Real.le_logb_iff_rpow_le hqR hnR).1 ht),
        Nat.lt_ceil.2 ((Real.logb_lt_iff_lt_rpow hqR hnR).1 ht')⟩
    · bound
    ·
      dsimp only [Dk, Pk]

      have hlev := hlev_pos k hk'
      have hq1 : (1 : ℝ) ≤ q := by bound
      have htk_lt := hD.t_lt k hk'
      set V : ℝ := ↑q ^ D.level k
      have hVpos : 1 < V := Real.one_lt_rpow hqR hlev
      have hVA := Real.rpow_le_rpow_of_exponent_le hq1 (hlev_lt k hk').le
      have hAB := Real.rpow_le_rpow_of_exponent_le hq1 htk_lt.le
      have hA1 : 1 ≤ A := Real.one_le_rpow hq1 (by grind)
      have hlogV : Real.log V = D.level k * Real.log q := Real.log_rpow hq0 _
      have hlogA : Real.log A = D.t k * Real.log q := Real.log_rpow hq0 _
      have hlogB : Real.log B = D.t (k + 1) * Real.log q := Real.log_rpow hq0 _
      -- apply the cell bound
      classical
      let R := Finset.Ico ⌈A⌉₊ ⌈B⌉₊
      let pp (n : ℕ) : ℝ := if IsPrimePow n ∧ (Nat.minFac n : ℝ) ≤ V then Λ n else 0
      let O := |CC| * ↑q ^ (-κ)

      let Q (j j' : ι) := ∑ n ∈ R, Real.log n / n * sieveNu V n *
        (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re
      have hY n : ‖Yn E a n‖ ^ 2 ≤ mass2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (hycomp j n).trans ?_
        apply mul_le_of_le_one_right (ha j)
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        unfold tn
        positivity [hδ j]

      -- majorant
      have step1 : ∑ n ∈ R, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
          ∑ n ∈ R, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 +
            ∑ n ∈ R, pp n / n * ‖Yn E a n‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        gcongr 1 with n hn
        convert mul_le_mul_of_nonneg_right (vonMangoldt_le_sieve hVpos n)
          (div_nonneg (sq_nonneg ‖Yn E a n‖) (Nat.cast_nonneg n)) using 1 <;> ring

      -- small prime powers
      have step2 := by
        calc ∑ n ∈ R, pp n / n * ‖Yn E a n‖ ^ 2 ≤ ∑ n ∈ R, pp n / n * mass2 :=
              Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hY n)
                (div_nonneg (by positivity) (Nat.cast_nonneg n))
          _ = (∑ n ∈ R, pp n / n) * mass2 := by exact?
          _ ≤ Pk k * mass2 := by
            apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            have h := small_primepow_sum (V := V) (A := A) (B := B) hVpos.le hA1
            simpa [pp, Pk, Finset.sum_filter, ite_div, hlogV] using h
      -- expand the Selberg part
      have step3 : ∑ n ∈ R, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 ≤
          ∑ j, Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 + O * mass2 := by
        conv_lhs =>
          simp only [norm_Yn_sq, Finset.mul_sum]
          rw [← Finset.sum_comm_cycle]
        change ∑ j, ∑ j', Q j j' ≤ _
        calc ∑ j, ∑ j', Q j j'
            ≤ ∑ j, ∑ j', ((if j' = j then Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2
                else 0) + a j * a j' * O) := by
              gcongr with j _ j' _
              split_ifs with h
              · subst j'
                refine le_trans ?_ (le_add_of_nonneg_right (by bound))
                let W := a j ^ 2 * Real.exp (-2 * E.δ j * D.t k)
                calc Q j j
                    ≤ (∑ n ∈ R, Real.log n / n * sieveNu V n) * W := by
                      dsimp only [Q, W]
                      rw [Finset.sum_mul]
                      gcongr 1 with n hn
                      have := hδ j
                      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
                      grw [hycomp j n]
                      rw [mul_pow, ← Real.exp_nat_mul]
                      norm_num
                      gcongr _ * (_ * Real.exp ?_)
                      nlinarith [(cell_mem hn).2]
                  _ ≤ Dk k * W := by
                    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
                    dsimp only [Dk]
                    refine (Finset.sum_le_sum_of_subset_of_nonneg (show R ⊆ Finset.Icc ⌈A⌉₊ ⌊B⌋₊ from by
                      grind [Nat.le_floor, Nat.lt_ceil]) ?_).trans
                      ((hdiagG V A B (hVq k hk) hVA hAB).trans ?_)
                    · intro n _ _
                      positivity
                    · rw [hlogV, hlogA, hlogB]

                      grw [le_abs_self CB]
                      field_simp

                      rfl
                  _ = _ := by bound
              · simp only [zero_add]
                have hjj' := Ne.symm h
                have hψ := fun h => hjj' (hinj' (mul_inv_eq_one.1 h))
                have hb := hoffq _ hψ (D.t k) (D.t (k + 1)) ((E.δ j + E.δ j') / Real.log q)
                  (E.γ j - E.γ j') (ht0k k hk') htk_lt.le (t_mono_le (by omega) le_rfl)  (by bound)
                  (hβ j j') (hτ j j')
                have hV' : ↑q ^ ((D.t k - ⅓) / 2 - D.ε') = V := by rfl
                rw [hV'] at hb
                have hbO := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self CC) (by positivity))
                have key := mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans hbO)
                  (mul_nonneg (ha j) (ha j'))
                refine le_trans (le_of_eq ?_) key

                rw [Complex.re_sum, Finset.mul_sum]
                congr! 1 with n hn
                have hn1 := (cell_mem hn).1
                have hn0 : n ≠ 0 := by omega
                rw [ycomp_mul_conj,
                  show (1 + (E.δ j + E.δ j') / Real.log q : ℝ) =
                    1 - -(E.δ j + E.δ j') / Real.log q by ring,
                  natCast_cpow_anchor hn0]
                simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
                ring
          _ = _ := by
            simp only [Finset.sum_add_distrib]
            congr 1
            · simp
            · dsimp only [mass2]; sum_ring
      linarith
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum hcell) hℓ.le).trans ?_
  let e j k := Real.exp (-2 * E.δ j * D.t k)
  let err k := |CB| * D.t (k + 1) ^ 2 / (D.level k ^ 2 * Real.log q) +
      |CB| / (D.level k ^ 2 * Real.log q ^ 3)
  have he k (hk : k ∈ Finset.range D.m) : ∑ j, e j k * a j ^ 2 ≤ mass2 := by
    have htk : 0 < D.t k := by grind
    have hex j : e j k ≤ 1 := by

      rw [Real.exp_le_one_iff]
      nlinarith [hδ j]
    grw [hex]
    simpa using Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => ha j

  have herr : ∑ k ∈ Finset.range D.m, D.h k *
      (err k + (|CC| * ↑q ^ (-κ) + Pk k) / Real.log q) ≤ ε := by
    refine le_trans (le_of_eq ?_) hEq
    congr! 1 with k _

    simp only [Pk, err, Real.rpow_sub hq0]
    field_simp
    ring
  linear_combination (norm :=
    (apply le_of_eq
     dsimp only [Dk, err, e, mass2]
     simp only [div_eq_mul_inv, mul_inv]
     sum_ring_nf
     field_simp [hℓ.ne']
     simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range D.m)]
     sum_ring)) (Finset.sum_le_sum (s := Finset.range D.m) fun k hk =>
       mul_le_mul_of_nonneg_left (he k hk) (show 0 ≤ D.h k * err k from by positivity [hD.h_nonneg k (Finset.mem_range.1 hk)])
     ) + mass2 * herr

end GradedNear
