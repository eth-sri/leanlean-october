module

public import GradedNear.FirstFactor
public import GradedNear.SievePart
public import GradedNear.GramForm

/-!
# Proof of the graded near lemma

Assembly (paper §8.5): the responses as one sum over `n`, Cauchy–Schwarz with the weight
`ω = g e^{s₁ t} + H`, the first factor by `first_factor_bound`, and the second factor split into
the Gram part (`gram_part_bound`) and the sieve part (`sieve_part_bound`).
-/

@[expose] public section

open Complex Finset Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open NearData

/-- **The graded near lemma** (paper Theorem 8.4, slightly generalized). Assumes the four printed
inputs (`XylourisLemma31`, `XylourisLemma32`, `BurgessPrimitive`, `GrahamEstimate`), data `D` with
`D.Valid`, and, for the modulus `q`, the zero-free case hypothesis `SafeAnchor q D.s₁ (2T + 1)`
(not a printed result; it is provable when `s₁ ≤ 0`, and in the application it is the case
hypothesis `s₁ ≤ λ₁` together with [X, Lemma 3.3]). Then for `q ≥ q₀`, all non-principal entries
of height `≤ T ≤ (log q)/3` with offsets in `D.Δ` (distinct characters when the sieve weight is
nonzero) and all `a ≥ 0`:
`(Σ a_j R_j)_+² ≤ (1+η) I_B [Σ_j (D(δ_j) - d₁ + e_j) a_j² + (d₁+η)(Σ_j a_j)²]`. -/
theorem graded_near_lemma
    (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessPrimitive)
    (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid) {η : ℝ} (hη : 0 < η) :
    LargeModuli[q => NearFamily[D, q; ι, E =>
        ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
          (max 0 (∑ j, a j * response D E j)) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, diagNumerator D E j * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2)]] := by
  have hIB := hD.IB_pos
  have hF := FirstFactor.first_factor_bound D hD (mul_pos hη hIB)
  have hG := gram_part_bound hX31 hX32 D hD (half_pos hη)
  have hS := sieve_part_bound hGr (burgessBound_of_primitive hBur) D hD (half_pos hη)
  obtain ⟨c, hc, hω⟩ := hD.omega_lb
  apply eventually_neZero
  filter_upwards [hF, hG, hS, eventually_ge_atTop 2] with q hF hG hS hq2
  intro _ T hT hTq hsafe ι _ E _ hγ hΔ hinj a ha
  have hℓ := log_q_pos hq2
  let U := Ioc 0 ⌊(q : ℝ) ^ D.xf⌋₊
  let N := max ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊
  let w (n : ℕ) := Λ n / n * D.omega (tn q n)
  let Y := Yn E a
  have hω0 n : 0 ≤ D.omega (tn q n) := by
    unfold NearData.omega NearData.sieveH
    refine add_nonneg (mul_nonneg (hD.g_cond2.nonneg _ (tn_nonneg q n)) (Real.exp_pos _).le) ?_
    exact sum_nonneg fun k hk => by split <;> simp [hD.h_nonneg k (mem_range.mp hk)]
  have hm n : 0 ≤ Λ n / (n : ℝ) := by positivity
  have hw n : 0 ≤ w n * ‖Y n‖ ^ 2 := mul_nonneg (mul_nonneg (hm n) (hω0 n)) (sq_nonneg _)
  let A := (∑ n ∈ U, Λ n / n * FirstFactor.phi D (tn q n)) / Real.log q
  let B := (∑ n ∈ U, w n * ‖Y n‖ ^ 2) / Real.log q
  have hA : A ≤ (1 + η) * D.IB := by simpa only [A, add_mul, one_mul] using hF
  have hB0 : 0 ≤ B := div_nonneg (sum_nonneg fun n _ => hw n) hℓ.le
  have hB : B ≤ ∑ j, diagNumerator D E j * a j ^ 2 +
      (D.d₁ + η) * (∑ j, a j) ^ 2 := by
    have hsub : U ⊆ Ioc 0 N := Ioc_subset_Ioc le_rfl (le_max_left _ _)
    refine (div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => hw n)) hℓ.le).trans ?_
    dsimp only [w, Y]
    simp only [NearData.omega, mul_add, add_mul, sum_add_distrib, add_div]
    have hg := hG T hT hTq hsafe ι E hγ hΔ a ha N (le_max_right _ _)
    have hs := hS ι E (fun j => (hγ j).trans hTq) hΔ hinj a ha N
    have hd δ : D.Dδ δ = gramDiag D δ + sieveDiag D δ := rfl
    simp only [hd, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib] at hg hs ⊢
    linarith
  have hsq : (∑ j, a j * response D E j) ^ 2 ≤ A * B := by
    rw [sum_response D E a hq2 hD.f_cond.vanish, neg_div, neg_sq, div_pow]
    dsimp [A, B]
    rw [div_mul_div_comm, ← sq]
    rw [Complex.re_sum]
    refine div_le_div_of_nonneg_right (sum_sq_le_sum_mul_sum_of_sq_le_mul U (fun n _ => ?_)
      (fun n _ => hw n) (fun n _ => ?_)) (sq_nonneg _)
    · exact mul_nonneg (hm n) (div_nonneg (by positivity) (hω0 n))
    · rw [pow_two]
      refine (re_sq_le_normSq _).trans_eq ?_
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      by_cases hf : D.f (tn q n) = 0
      · simp [cWeight, FirstFactor.phi, hf]
      · have hωp := hc.trans_le (hω _ (tn_nonneg q n) hf)
        simp only [cWeight, w, FirstFactor.phi, mul_assoc, Real.exp_add, two_mul, add_mul]
        field_simp [hωp.ne']; ring

  refine le_trans ?_ (hsq.trans (mul_le_mul hA hB hB0 (by positivity)))
  rw [← sq_abs (∑ j, a j * response D E j)]
  gcongr
  exact max_le (abs_nonneg _) (le_abs_self _)

end GradedNear
