import GradedNear.Tactics
import GradedNear.FirstPart
import GradedNear.SievePart
import GradedNear.BurgessReduction
import GradedNear.Response
import GradedNear.Threshold
import GradedNear.Cert.Bins

set_option maxHeartbeats 2000000

/-! # The graded near lemma and its zero and row normalizations

Shared analytic hypotheses are kept in one section; the entry estimates and
separation bounds are independent of those hypotheses.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

/-- A zero of a non-principal `L(s, χ)` has multiplicity at least one. -/
lemma one_le_zmult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have ha := DirichletCharacter.differentiable_LFunction hχ
  exact_mod_cast ENat.toNat_pos ((ha.analyticAt ρ).analyticOrderAt_ne_zero.mpr hρ) (by
    rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ ha.analyticAt]
    exact fun h => DirichletCharacter.LFunction_apply_one_ne_zero hχ (congrFun h 1))

section
variable {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (hf2 : Condition2 f)
include hf hf2

/-- A zero at the entry's height has the real term `F(λ_ρ - σ)`, which is at least `F(hi - σ)`
for `λ_ρ ≤ hi`, and nonnegative. -/
lemma zeroTerm_at_height_le {q : ℕ} {σ γ hi : ℝ} {ρ : ℂ} (hγ : ρ.im = γ)
    (hhi : zeroLambda q ρ ≤ hi) :
    realLaplace f (hi - σ) ≤ zeroTerm f q σ γ ρ ∧ 0 ≤ zeroTerm f q σ γ ρ := by
  simp only [zeroTerm, hγ, sub_self, zero_mul, Complex.ofReal_zero, add_zero]
  simp_rw [Decay.laplace_eq_intervalIntegral hf]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    intervalIntegral.integral_ofReal, Complex.ofReal_re]
  refine ⟨?_, intervalIntegral.integral_nonneg hf.pos.le fun t ht =>
     by positivity [hf2.nonneg t ht.1] ⟩
  have hc (z : ℝ) : ContinuousOn (fun t => f t * Real.exp (-(z * t))) (Set.uIcc 0 x₀) := by
    rw [Set.uIcc_of_le hf.pos.le]
    exact (hf.cont.mono Set.Icc_subset_Ici_self).mul (by fun_prop)
  refine intervalIntegral.integral_mono_on hf.pos.le (hc _).intervalIntegrable
    (hc _).intervalIntegrable fun t ht => ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hf2.nonneg t ht.1)
  gcongr <;> grind

/-- **A kept zero at the entry's height.** If `Im ρ = γ` and `λ_ρ = (1 - Re ρ)𝓛 ≤ hi`, the
zero's term, with multiplicity, is at least `F(hi - σ)`. -/
lemma zeroTerm_at_height {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ γ hi : ℝ} {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (hγ : ρ.im = γ)
    (hhi : zeroLambda q ρ ≤ hi) :
    realLaplace f (hi - σ) ≤ zmult χ ρ * zeroTerm f q σ γ ρ := by
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hf hf2 hγ hhi
  exact h1.trans (le_mul_of_one_le_left h0 (one_le_zmult hχ hρ))

end

variable {q : ℕ} {ι : Type*}

section
variable [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
  (E : Entries q ι) (Sz : ι → Finset ℂ)
include hD hf2

local notation:max "anchor " j:arg => D.s - E.δ j

/-- **An entry keeping one zero at its height**, as for an ordinary character in the bin
`[lo, hi]`: `keptBound ≥ F(hi - s_j) - f(0)/6 - η`. -/
theorem keptBound_single (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : zeroLambda q ρ ≤ hi) :
    realLaplace D.f (hi - anchor j) - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  linarith [zeroTerm_at_height hD.f_cond hf2 hχ (σ := anchor j) hρ hγ hhi]

/-- **An entry keeping a zero at its height and a second zero at or left of the test point**,
as for the `rc` pair and the first family's second zero:
`keptBound ≥ F(hi - s_j) + Re F(z') - f(0)/6 - η`, where `Re F(z') ≥ 0` is the second zero's
term. -/
theorem keptBound_pair (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : zeroLambda q ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hleft : anchor j ≤ zeroLambda q ρ') :
    realLaplace D.f (hi - anchor j) +
        zeroTerm D.f q anchor j (E.γ j) ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  have h1 := zeroTerm_at_height hD.f_cond hf2 hχ (σ := anchor j) hρ hγ hhi
  have h0 : 0 ≤ zeroTerm D.f q anchor j (E.γ j) ρ' := by
    apply hf2.re_nonneg
    simpa [-Complex.natCast_log] using sub_nonneg.mpr hleft
  have hm := one_le_zmult hχ hρ'
  nlinarith

/-- **A kept multiple zero at the entry's height**, as for the first family's double zero
(`ρ' = ρ₁`, `y = 0`): with multiplicity at least `2`, the kept terms are at least `F(hi - s_j)`
plus the zero's own term. -/
theorem keptBound_double (η : ℝ) (j : ι) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : zeroLambda q ρ ≤ hi) :
    realLaplace D.f (hi - anchor j) +
        zeroTerm D.f q anchor j (E.γ j) ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := anchor j) hγ hhi
  nlinarith

/-- **An entry keeping a zero at its height and a second zero whose term may be negative**, as
for the shifted row's `rc` entry, whose conjugate zero `ρ̄₁` lies left of the anchor. Suppose the
second zero's term is at least `-C` and its multiplicity is at most the first's (for a real
character, conjugate zeros have equal multiplicity). Then the kept terms minus `f(0)/6` are at
least `F(hi - s_j) - C - f(0)/6`, unless that number is `≤ 0`, in which case the entry's feature
is `≤ 0` and it contributes nothing to (T). -/
theorem keptBound_pair_neg (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi C : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : zeroLambda q ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ zeroTerm D.f q anchor j (E.γ j) ρ') :
    realLaplace D.f (hi - anchor j) - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      realLaplace D.f (hi - anchor j) - C - D.f 0 / 6 ≤ 0 := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  obtain ⟨hA, hA0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := anchor j) hγ hhi
  have hm2 := one_le_zmult hχ hρ'
  have hf0 := hf2.nonneg 0 le_rfl
  by_cases hAB : 0 ≤ zeroTerm D.f q anchor j (E.γ j) ρ +
      zeroTerm D.f q anchor j (E.γ j) ρ'
  · left
    nlinarith
  bound

end

/-- The conjugate entry `(χ̄, -γ)` keeping the conjugate zero `ρ̄` has the same term as
`(χ, γ)` keeping `ρ`, since `Re F(z̄) = Re F(z)` for real `f`. -/
lemma zeroTerm_conj (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) :
    zeroTerm f q σ (-γ) ((starRingEnd ℂ) ρ) = zeroTerm f q σ γ ρ := by
  unfold zeroTerm
  rw [← laplace_re_conj f]

  simp [-Complex.natCast_log] <;> ring

/-- **Same-character pairs at separated heights have no pair excess.** If `g(0) > 0`, there is an
`M > 0` such that an entry `j` has `e_j = 0` whenever every other entry of the same character is
at normalized height distance `|γ_j - γ_k| log q ≥ M` from it. The reason is that
`|G(x + iY)| ≤ d₁` for `|Y| ≥ M` and `x` in the fixed range of `-σ_jk`. -/
theorem pairExcess_eq_zero (D : NearData) (hD : D.Valid) (hg0 : 0 < D.g 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ {q : ℕ} {ι : Type} [Fintype ι] (E : Entries q ι), Offsets E D →
      ∀ j, (∀ k, k ≠ j → E.χ k = E.χ j → M ≤ |E.γ j - E.γ k| * Real.log q) →
        pairExcess D E j = 0 := by
  have hd₁ : 0 < D.d₁ := by unfold NearData.d₁; linarith
  let X := |D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 X hd₁
  refine ⟨M, hM, fun {q} {ι} _ E hΔ j hsep => ?_⟩

  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k ≠ j ∧ E.χ k = E.χ j := by
    unfold sameCharOthers at hk
    simp_all


  apply max_eq_left
  exact sub_nonpos.mpr ((Complex.re_le_norm _).trans (hdec _ (by
    grind [Finset.single_le_sum, abs_nonneg]
  ) _ (by
    grind [Real.log_natCast_nonneg]
  )))

section
variable (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessPrimitive)
  (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
include hX31 hX32 hBur hGr hD

theorem graded_near_lemma
     {η : ℝ} (hη : 0 < η) :
    ForLargeNear D (q, ι, E =>
        ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
           max 0 (∑ j, a j * response D E j) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, diagNum D E j * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2)) := by
  obtain ⟨c, hc, hωc⟩ := hD.omega_lb
  conv => enter [1, q₀, q]; rw [forall_comm]
  apply Filter.eventually_atTop.1
  filter_upwards [first_factor_bound D hD (ε := η * D.IB) (mul_pos hη hD.IB_pos),
    gram_form_bound hX31 hX32 D hD (ε := η / 2) (half_pos hη),
    sieve_part_bound hGr (burgessBound_of_primitive hBur) D hD (ε := η / 2) (half_pos hη), Filter.eventually_ge_atTop (2 : ℕ)] with q hqF hqG hqS hq2
  intro _ T hT hTq hsafe ι _ E _ hγ hΔ hinj a ha
  have hℓ := log_q_pos hq2
  set Sf := Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊
  set N := max ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊
  set w : ℕ → ℝ := fun n => Λ n / n * D.omega (tn q n) with hw
  have hw0 n : 0 ≤ w n := by
    refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
    · positivity [hD.g_cond2.nonneg (tn q n) (by unfold tn; positivity)]
    · refine Finset.sum_nonneg fun k hk => ?_
      grind [GradedNear.NearData.Valid.h_nonneg]
  let cw (n : ℕ) := Λ n / n * Real.exp (D.s * tn q n) * D.f (tn q n)
  -- Step 1: the responses as one sum
  have hresp : ∑ j, a j * response D E j =
      -(∑ n ∈ Sf, ↑(cw n) * Yn E a n).re / Real.log q := by
    dsimp only [Sf]
    unfold response
    simp_rw [primeSum_eq_sum hq2 _ _ hD.f_cond.vanish _ le_rfl, prime_term, Yn, ycomp, Finset.mul_sum, Complex.re_sum,
      mul_assoc, Complex.re_ofReal_mul]
    simp only [← mul_div_assoc, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    simp only [cw, sub_mul, neg_mul, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
    sum_ring
  -- Step 2: Cauchy–Schwarz

  -- the first factor
  set A := (∑ n ∈ Sf, cw n ^ 2 / w n) / Real.log q with hA

  -- the second factor, enlarged to `Icc 1 N`
  have hsecond_mono :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n => w n * ‖Yn E a n‖ ^ 2)
      (Finset.Icc_subset_Icc (le_refl 1)
        (le_max_left ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊))
       fun n _ _ => mul_nonneg (hw0 n) (sq_nonneg _)
  have hG := hqG T hT hTq hsafe ι E hγ hΔ a ha
  have hS := hqS T hT hTq ι E hγ hΔ hinj a ha N
  set B := (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q with hB


  -- combine
  have hsq : (∑ j, a j * response D E j) ^ 2 ≤
      A * B := by
    rw [hA, hB, hresp, neg_div, neg_sq, div_pow]
    rw [div_mul_div_comm, ← sq]
    gcongr
    refine le_trans ?_ (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (r := fun n => |cw n| * ‖Yn E a n‖) Sf
      (fun n _ => div_nonneg (sq_nonneg (cw n)) (hw0 n))
      (fun n _ => mul_nonneg (hw0 n) (sq_nonneg ‖Yn E a n‖)) (by
        intro n hn
        by_cases hcw : cw n = 0
        · simp [hcw]
        have hwp : 0 < w n := by
          have hn1 := (Finset.mem_Icc.1 hn).1
          unfold cw at hcw
          have hΛ : Λ n ≠ 0 := by grind

          exact mul_pos (by positivity) (hc.trans_le (hωc (tn q n) (by unfold tn; positivity) (by grind)))
        rw [mul_pow, sq_abs]
        field_simp [hwp.ne']
        rfl)
    )
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _) _ 2
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
    simp
  calc (max 0 (∑ j, a j * response D E j)) ^ 2 ≤ (∑ j, a j * response D E j) ^ 2 := by
        grind [sq_nonneg, sq]
    _ ≤ _ := hsq
    _ ≤ (1 + η) * D.IB * (∑ j, diagNum D E j * a j ^ 2 +
          (D.d₁ + η) * (∑ j, a j) ^ 2) :=
        mul_le_mul (by
          convert hqF using 1
          · dsimp only [A]
            congr 1
            congr! 1 with n _
            unfold cw

            rw [two_mul, add_mul, Real.exp_add]
            by_cases h : Λ n / ↑n = 0
            · simp [h]
            simp only [hw, div_mul_eq_div_div, sq, mul_div_right_comm, div_self h]
            ring
          · ring
        ) (by
          refine (div_le_div_of_nonneg_right hsecond_mono hℓ.le).trans ?_
          simp only [hw, NearData.omega, mul_add, add_mul, Finset.sum_add_distrib, add_div]
          convert add_le_add hG hS using 1
          · congr 2
            simp_rw [primeSum_eq_sum (N := N) hq2 _ _ hD.g_cond1.vanish _ (le_max_right _ _),
              Complex.re_sum, norm_Yn_sq, Finset.mul_sum, ycomp_mul_conj, sjk, prime_term,
              Complex.re_ofReal_mul]
            simp only [sub_mul, add_mul, neg_mul, Real.exp_sub, Real.exp_add, Real.exp_neg, mul_inv]
            conv_rhs => rw [Finset.sum_comm_cycle]
            sum_ring
          · simp only [NearData.Dδ]
            sum_ring
        ) (div_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hw0 n) (sq_nonneg _)) hℓ.le) (by positivity [hD.IB_pos])

variable (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η)
include hf2 hη

/-- **The graded near lemma in zero form.** Fix the row data `D`, a zero count `K₀` and `η > 0`.
There are a separation `M`, a disc radius `δ < 1` and a `q₀` such that the following holds for
`q ≥ q₀`, a height `T ≤ log q / 3` and a safe anchor `s₁` at height `2T + 1`. Take entries as in
`graded_near_lemma`, and for each entry a finite set `S_j` of zeros of `L(s, χ_j)` in the disc
of radius `δ` about `1 + iγ_j`. Suppose that every other disc zero with `λ_ρ < s_j` is at
normalized height distance `≥ M` from `γ_j`, and that there are at most `K₀` of them, with
multiplicity. Then the entries satisfy the threshold form (T) with the features
`keptBound / N`, provided every diagonal numerator `D(δ_j) - d₁ + e_j` is positive, for any
normalizer `D_n > 0`. -/
theorem graded_near_threshold

     :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ForLargeNear D (q, ι, E =>
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            InDisc (E.γ j) δ ρ) →
          (∀ j, DistantZeros q (E.χ j) (D.s - E.δ j) (E.γ j) δ (Sz j) M) →
          (∀ j, ∑ᶠ ρ ∈ discardedZeros q (E.χ j) (D.s - E.δ j) (E.γ j) δ (Sz j), zmult (E.χ j) ρ ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < diagNum D E j) →
            NearThreshold ((D.d₁ + η) / Dn)
              (j => keptBound D E Sz η j / Real.sqrt ((1 + η) * D.IB * Dn), diagNum D E j / Dn)) := by
  obtain ⟨q₁, hq₁⟩ := graded_near_lemma hX31 hX32 hBur hGr D hD hη
  obtain ⟨M, hM, δ, hδ0, hδ1, q₂, hq₂⟩ :=
    response_lemma hX32 hD.f_cond hf2 (|D.s| + ∑ δ ∈ D.Δ, |δ|) K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK Dn hDn hDj
  have hq1 := le_of_max_le_left hq


  -- the kept zeros bound each response from below
  have hresp j : keptBound D E Sz η j ≤ response D E j := by


    exact hq₂ q (le_of_max_le_right hq) (E.χ j) (hχ j) (D.s - E.δ j) (E.γ j) (by
      grind [abs_sub, Finset.single_le_sum]
    ) (by grind) (Sz j) (hSz j) (hsep j) (hK j)
  -- normalization
  have hIB := hD.IB_pos
  set N := Real.sqrt ((1 + η) * D.IB * Dn)


  have hd₁ : 0 ≤ D.d₁ := div_nonneg (hD.g_cond2.nonneg 0 le_rfl) (by norm_num)
  refine threshold_of_quadratic
    (fun j => div_pos (hDj j) hDn) (div_pos (by linarith) hDn) ?_
  intro a ha


  simp_rw [← mul_div_assoc, div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
  grw [ Finset.sum_le_sum (s := Finset.univ) fun j _ => mul_le_mul_of_nonneg_left (hresp j) (ha j) ]
  rw [← zero_div N, max_div_div_right (Real.sqrt_pos.2 (by positivity)).le, div_pow,  Real.sq_sqrt (by positivity) ,
    div_le_div_iff₀ (by positivity) hDn]
  linear_combination (norm := (bound)) Dn *  hq₁ q hq1 T hT0 hTl hsafe ι E hχ hγ hΔ hinj a ha

/-- **A row whose entries each keep one zero at their own height** (paper §9.4: ordinary
characters, the first family, the reserved second family, the outside global zero and hidden
columns). Entry `j` sits at the height of a zero `ρ_j` of `L(s, χ_j)` in its disc with
`λ_{ρ_j} ≤ hi_j`. Every other disc zero with `λ_ρ < s_j` must be at normalized height distance
`≥ M`, and there are at most `K₀` of them. Then the entries satisfy the threshold form (T) with
the features `(F(hi_j - s_j) - f(0)/6 - η) / N`, which is the form the leaf builders compute. -/
theorem single_zero_threshold

     :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ForLargeNear D (q, ι, E =>
        ∀ (ρ : ι → ℂ) (hi : ι → ℝ),
          (∀ j, DirichletCharacter.LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            InDisc (E.γ j) δ (ρ j) ∧ zeroLambda q (ρ j) ≤ hi j) →
          (∀ j, ∀ ρ' : ℂ, DirichletCharacter.LFunction (E.χ j) ρ' = 0 →
            InDisc (E.γ j) δ ρ' → ρ' ≠ ρ j →
            zeroLambda q ρ' < D.s - E.δ j → M ≤ |E.γ j - ρ'.im| * Real.log q) →
          (∀ j, ∑ᶠ ρ' ∈ {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
              InDisc (E.γ j) δ ρ' ∧ ρ' ≠ ρ j ∧
              zeroLambda q ρ' < D.s - E.δ j}, zmult (E.χ j) ρ' ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < diagNum D E j) →
            NearThreshold ((D.d₁ + η) / Dn)
              (j => (realLaplace D.f (hi j - (D.s - E.δ j)) - D.f 0 / 6 - η) /
                Real.sqrt ((1 + η) * D.IB * Dn), diagNum D E j / Dn)) := by
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ := graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj ρ hi hρ hsep hK Dn hDn hDj
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj (fun j => {ρ j})
     fun j ρ' hρ' => by grind
    (fun j ρ' h1 h2 h3 h4 => hsep j ρ' h1 h2 (by bound) h4)
    (fun j => by simpa only [Finset.mem_singleton] using hK j) Dn hDn hDj
  refine ⟨τ, hτ0, hτd, (Finset.sum_le_sum fun j _ => ?_).trans hT⟩

  have hj := hDj j
  gcongr
  exact keptBound_single D hD hf2 E (fun j => {ρ j}) η j (hχ j) rfl
    (hρ j).1 (hρ j).2.1 (hρ j).2.2.2

/-- **The graded near lemma in the normalization of the leaf builders.** Fix the row data `D`, a
zero count `K₀`, the allowance `η > 0`, an upper bound `I_u ≥ I_B` and a normalizer `D_u > 0`.
There are `M`, `δ < 1` and `q₀` such that, for entries with kept zeros as in
`graded_near_threshold`, the following holds. Suppose each `r_j` is at most the entry's kept
terms minus `f(0)/6` (`keptBound … 0`), or `r_j ≤ 0`, and each `D_j⁺` is at least the entry's
diagonal numerator `D(δ_j) - d₁ + e_j > 0`. Then (T) holds with the features
`r_j / √(I_u D_u) - η`, the diagonals `(1 + η) D_j⁺ / D_u` and the radius
`(1 + η)(d₁ / D_u + η)`. -/
theorem builder_threshold

     {Iu Du : ℝ} (hIu : D.IB ≤ Iu)
    (hDu : 0 < Du) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ForLargeNear D (q, ι, E =>
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            InDisc (E.γ j) δ ρ) →
          (∀ j, DistantZeros q (E.χ j) (D.s - E.δ j) (E.γ j) δ (Sz j) M) →
          (∀ j, ∑ᶠ ρ ∈ discardedZeros q (E.χ j) (D.s - E.δ j) (E.γ j) δ (Sz j), zmult (E.χ j) ρ ≤ K₀) →
          ∀ r De : ι → ℝ, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < diagNum D E j) →
            (∀ j, diagNum D E j ≤ De j) →
            NearThreshold ((1 + η) * (D.d₁ / Du + η))
              (j => r j / Real.sqrt (Iu * Du) - η, (1 + η) * De j / Du)) := by
  have hIB := hD.IB_pos
  set N := Real.sqrt (D.IB * Du) with hN
  set η' := η * min 1 (min N Du) with hη'
  have hNpos : 0 < N := by simp_all
  have hη'pos : 0 < η' := by positivity
  have hη'η : η' ≤ η := by simp_all
  have hη'N : η' ≤ η * N := by simp_all
  have hη'D : η' ≤ η * Du := by simp_all
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ :=
    graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη'pos
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK r De hr hDj hDe
  have hDnpos : 0 < Du / (1 + η') := by positivity
  obtain ⟨τ, hτ0, hτd, hT⟩ :=
    h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj Sz hSz hsep hK (Du / (1 + η')) hDnpos hDj
  have hd₁ : 0 ≤ D.d₁ := div_nonneg (hD.g_cond2.nonneg 0 le_rfl) (by norm_num)
  have hNn : Real.sqrt ((1 + η') * D.IB * (Du / (1 + η'))) = N := by grind
  rw [hNn] at hT
  have hsq :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hIu hDu.le)
  have hdd : (D.d₁ + η') / (Du / (1 + η')) ≤ (1 + η) * (D.d₁ / Du + η) := by
    rw [div_div_eq_mul_div, mul_comm]
    field_simp
    gcongr
    nlinarith
  refine ⟨τ, hτ0, hτd.trans (Real.sqrt_le_sqrt hdd), ?_⟩
  refine (Finset.sum_le_sum fun j _ => Cert.term_le ?_ hτ0
    (div_pos (hDj j) hDnpos) ?_).trans (hT.trans ?_)
  · -- the features
    by_cases hr0 : r j ≤ 0
    · right
      have : r j / Real.sqrt (Iu * Du) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr0 (Real.sqrt_nonneg _)
      linarith
    · left
      have hrk := (hr j).resolve_right hr0
      have hk : keptBound D E Sz η' j = keptBound D E Sz 0 j - η' := by
        unfold keptBound; ring

      have h2 := (div_le_iff₀ hNpos).mpr hη'N

      rw [hk, sub_div]
      bound
  · -- the diagonals
    have hj := hDj j
    rw [div_div_eq_mul_div, mul_comm]
    bound
  · gcongr

end
end GradedNear
