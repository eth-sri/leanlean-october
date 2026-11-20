module

public import GradedNear.TestFamilies
public import GradedNear.FirstPart
public import GradedNear.SievePart
public import GradedNear.GramForm

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

open NearData Finset

/-- `ω ≥ 0` on `[0, ∞)`. -/
lemma omega_nonneg (D : NearData) (hD : D.Valid) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ D.omega u := by
  refine add_nonneg (mul_nonneg (hD.g_cond2.nonneg u hu) (Real.exp_pos _).le) ?_
  refine Finset.sum_nonneg fun k hk => ?_
  split_ifs
  · exact hD.h_nonneg k (Finset.mem_range.1 hk)
  · exact le_rfl

/-- The positive real response is bounded by the two normalized weighted factors. -/
lemma response_cs {β : Type*} (S : Finset β) (p c w : β → ℝ) (Y : β → ℂ) {ℓ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hw : ∀ n, 0 ≤ w n) (hc : ∀ n, c n ≠ 0 → 0 < w n) :
    (max 0 (-(∑ n ∈ S, p n * c n * (Y n).re) / ℓ)) ^ 2 ≤
      ((∑ n ∈ S, p n * (c n^2 / w n)) / ℓ) * ((∑ n ∈ S, p n * w n * ‖Y n‖^2) / ℓ) := by
  grw [max_le (abs_nonneg _) (le_abs_self _), sq_abs, div_pow, neg_sq]
  rw [div_mul_div_comm, ← sq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  refine S.sum_sq_le_sum_mul_sum_of_sq_le_mul (fun n _ => by positivity [hp n, hw n])
    (fun n _ => by positivity [hp n, hw n]) fun n _ => ?_
  by_cases h : c n = 0
  · simp [h]
  have := hc n h
  rw [mul_pow _ (Y n).re]
  grw [sq_le_sq.mpr (by simpa using abs_re_le_norm (Y n) : |(Y n).re| ≤ |‖Y n‖|)]
  field_simp; rfl

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
    ForLargeEntries q ι E of D,
        ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
          (max 0 (∑ j, a j * response D E j)) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, (rowDiag D E j) * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2) := by
  obtain ⟨q₀, h₀⟩ := Filter.eventually_atTop.mp <| (Filter.eventually_ge_atTop 2).and <|
    (first_factor_bound D hD (mul_pos hη hD.IB_pos)).and <|
    (gram_form_bound hX31 hX32 D hD (half_pos hη)).and (sieve_part_bound hGr hBur D hD (half_pos hη))
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  refine ⟨q₀, fun q _ hq T _ hTq hsafe ι _ E _ hγ hΔ hinj a ha => ?_⟩
  obtain ⟨hq2,hF,hG,hS⟩ := h₀ q hq
  let wE : Window D E := ⟨T, hTq, hγ, hΔ⟩
  have hℓ := log_q_pos hq2
  let w n := D.omega (tn q n)
  have hw n := omega_nonneg D hD (tn_nonneg _ n hq2)
  have hn n : 0 ≤ primeMass n * w n * ‖Yn E a n‖^2 := by positivity [primeMass_nonneg n, hw n]
  rw [sum_response D E a hq2 hD]
  apply (response_cs (samples q D.horizon) primeMass (fun n => amplitude D (tn q n)) w (Yn E a) primeMass_nonneg hw (fun n h => hc.trans_le
    (hcω _ (tn_nonneg _ n hq2) (right_ne_zero_of_mul h)))).trans
    (mul_le_mul ?_ ?_ (div_nonneg (sum_nonneg fun n _ => hn n) hℓ.le) (by positivity [hD.IB_pos]))
  · simp_rw [amplitude_sq]; exact hF.trans_eq (by ring)
  · simp [w, NearData.omega, mul_add, add_mul, sum_add_distrib, add_div]
    rw [gram_part_eq D E a hq2 hD]
    grw [hG E wE hsafe a ha, hS E wE hinj a ha _]
    simp only [NearData.Dδ, sub_eq_add_neg, add_mul, sum_add_distrib]
    linarith

end GradedNear
