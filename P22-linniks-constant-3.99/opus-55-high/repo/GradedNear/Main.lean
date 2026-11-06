module

public import GradedNear.FirstPart
public import GradedNear.SievePart

/-!
# Proof of the graded near lemma

Assembly (paper §8.5): the responses as one sum over `n`, Cauchy–Schwarz with the weight
`ω = g e^{s₁ t} + H`, the first factor by `first_factor_bound`, and the second factor split into
the Gram part (`gram_part_eq`, `gram_form_bound`) and the sieve part (`sieve_part_bound`).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open NearData

/-- **The graded near lemma** (paper Theorem 8.4, slightly generalized). Assumes the four printed
inputs (`XylourisLemma31`, `XylourisLemma32`, `BurgessPrimitive`, `GrahamEstimate`), data `D` with
`D.Valid`, and, for the modulus `q`, the zero-free case hypothesis `SafeAnchor q D.s₁ (2T + 1)`.
Then for `q ≥ q₀`, all non-principal entries of height `≤ T ≤ (log q)/3` with offsets in `D.Δ`
(distinct characters when the sieve weight is nonzero) and all `a ≥ 0`:
`(Σ a_j R_j)_+² ≤ (1+η) I_B [Σ_j (D(δ_j) - d₁ + e_j) a_j² + (d₁+η)(Σ_j a_j)²]`. -/
theorem graded_near_lemma
    (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessPrimitive)
    (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid) {η : ℝ} (hη : 0 < η) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
          (max 0 (∑ j, a j * response D E j)) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2) := by
  have hIB := hD.IB_pos
  obtain ⟨qF, hqF⟩ := first_factor_bound D hD (ε := η * D.IB) (mul_pos hη hIB)
  obtain ⟨qG, hqG⟩ := gram_form_bound hX31 hX32 D hD (ε := η / 2) (half_pos hη)
  obtain ⟨qS, hqS⟩ := sieve_part_bound hGr (burgessBound_of_primitive hBur) D hD (ε := η / 2)
    (half_pos hη)
  obtain ⟨c, hc, hωc⟩ := hD.omega_lb
  refine ⟨max (max qF qG) (max qS 2), fun q _ hq T hT hTq hsafe ι _ E _ hγ hΔ hinj a ha => ?_⟩
  simp only [max_le_iff] at hq
  have hℓ := log_q_pos hq.2.2
  set Sf := Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊
  set w : ℕ → ℝ := fun n => Λ n / n * D.omega (tn q n) with hw
  have hw0 n : 0 ≤ w n :=
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg n.cast_nonneg)
      (add_nonneg (mul_nonneg (hD.g_cond2.nonneg _ (tn_nonneg q n hq.2.2)) (Real.exp_pos _).le)
        (Finset.sum_nonneg fun k hk => ite_nonneg (hD.h_nonneg k (Finset.mem_range.1 hk)) le_rfl))
  have hcs := weighted_cs Sf (cWeight D q) w (fun n => ‖Yn E a n‖) (fun n _ => hw0 n)
    fun n _ hne => by
      simp only [cWeight, mul_ne_zero_iff] at hne
      exact mul_pos ((div_nonneg ArithmeticFunction.vonMangoldt_nonneg n.cast_nonneg).lt_of_ne'
        hne.1.1) (hc.trans_le (hωc _ (tn_nonneg q n hq.2.2) hne.2))
  have hF1 : (∑ n ∈ Sf, cWeight D q n ^ 2 / w n) / Real.log q ≤ (1 + η) * D.IB := by
    refine le_of_eq_of_le ?_ ((hqF q hq.1.1).trans_eq (by ring))
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases eq_or_ne (Λ n) 0 with h | h
    · grind
    rcases eq_or_ne (D.omega (tn q n)) 0 with h' | h'
    · grind
    simp [cWeight, hw]
    field_simp
    rw [← Real.exp_nat_mul]; ring_nf
  have hF2 : (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q ≤
      ∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
        (D.d₁ + η) * (∑ j, a j) ^ 2 := by
    refine (div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (le_max_left _ ⌊(q : ℝ) ^ D.xg⌋₊))
      fun n _ _ => mul_nonneg (hw0 n) (sq_nonneg _)) hℓ.le).trans ?_
    have hG := hqG q hq.1.2 T hT hTq hsafe ι E hγ hΔ a ha
    rw [← gram_part_eq D E a hq.2.2 hD.g_cond1.vanish (le_max_right ⌊(q : ℝ) ^ D.xf⌋₊ _)] at hG
    have hS := hqS q hq.2.1 T hT hTq ι E hγ hΔ hinj a ha
      (max ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊)
    simp [hw, NearData.omega, NearData.Dδ, sieveDiag, mul_add, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, add_div] at *
    linarith
  have := mul_le_mul hF1 hF2 (div_nonneg (Finset.sum_nonneg fun n _ =>
    mul_nonneg (hw0 n) (sq_nonneg _)) hℓ.le) (by positivity)
  refine ((pow_le_pow_left₀ (le_max_left ..) (max_le (abs_nonneg _) (le_abs_self _)) 2).trans_eq
    (sq_abs _)).trans ?_
  rw [sum_response D E a hq.2.2 hD.f_cond.vanish, neg_div, neg_sq, div_pow]
  refine (div_le_div_of_nonneg_right (((sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _)
    ((Complex.abs_re_le_norm _).trans ((norm_sum_le ..).trans_eq (by simp [Sf]))) 2)).trans hcs)
    (sq_nonneg _)).trans ?_
  rwa [div_mul_div_comm, ← sq] at this

end GradedNear
