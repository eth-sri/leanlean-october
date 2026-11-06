module

public import RequestProject.PlanarTypes
public import Mathlib.Tactic.FunProp

public import RequestProject.PlanarGeometry

public import RequestProject.HerglotzForm
public import RequestProject.PeriodicForm

/-!
# Transmutation of antiholomorphic polynomials (Lemmas 5.8, 5.9 on polynomials; Lemma 5.11)

For an antiholomorphic monomial `z̄^m` the normalized primitive is explicit,
`J^j z̄^m = m! z̄^{m+j} / (m+j)!`, so the transmutation series of the paper is
`𝒱_E z̄^m = ∑_j (-E/4)^j m! / (j! (m+j)!) z^j z̄^{m+j}` (`vekuaMonomial`).

Main results:
* `hasSum_herglotzWave_monoDensity`: the Herglotz wave with density `e^{-imφ}` is
  `∑_p α^p β^{p+m} / (p! (p+m)!)` with `α = -(ik/2) z`, `β = -(ik/2) z̄` (expansion of the plane
  wave as a product of two exponential series, integrated termwise);
* `vekuaMonomial_eq` (**Lemma 5.8**): for `k ≠ 0` the series converges and
  `𝒱_{k²} z̄^m = m! (-ik/2)^{-m} u_{e^{-im·}}`;
* `vekuaPoly_eq_herglotzWave`: the same for antiholomorphic polynomials `h = ∑ c_m z̄^m`, with a
  trigonometric-polynomial direction density; `herglotzVec_polyDensity_zero`: its initial vector
  at the origin is `(h(0)/√2) e₀`;
* `polynomial_transmutation_endpoint` (**Lemma 5.9 for polynomials**): if `γ(0) = 0`,
  `O_E^* 𝒥_E h = i (V_E^* - I) e₀ h(0)` and `(𝒱_E h) ∘ γ = h(0) O_E e₀ - i T_E 𝒥_E h`;
  in particular `𝒥_E h ∈ ker O_E^*` when `h(0) = 0` (`observationAdj_vekuaPolyConormal_eq_zero`);
* `periodicP_vekuaPoly` (**Lemmas 6.9–6.10 for polynomials**): with `n = (𝒱_E h) ∘ γ` (the
  Neumann-to-Dirichlet trace of `𝒥_E h` at a nonresonant energy) and `c_E ≠ 0`,
  `𝒫_E 𝒥_E h = 0` on `[0, L]` and `T_E^♯ 𝒥_E h = 0`; this discharges, for antiholomorphic
  polynomials, the hypotheses of `periodicP_radial` and `periodicP_of_observationAdj_eq_zero`;
* `kernel_cauchy_test` (**Lemma 5.11, compatibility part**): for bounded measurable `g` with
  `O_E^* g = 0`, the Cauchy data `(-i T_E g, g)` satisfy
  `∫₀^L (conj(g) h_a - conj(-i T_E g) g_a) = 0` for every Herglotz wave.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- `∫₀^{2π} e^{inφ} dφ = 2π [n = 0]` for `n ∈ ℤ`. -/
lemma integral_exp_int_mul_I (n : ℤ) :
    ∫ φ in (0 : ℝ)..circlePeriod, Complex.exp ((n : ℂ) * φ * Complex.I) =
      if n = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hn
  · subst hn; simp
  · have hc : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    simp only [show ∀ φ : ℝ, (n : ℂ) * φ * Complex.I = (n : ℂ) * Complex.I * φ from
      fun φ => by ring] at *
    rw [this]
    have h1 : Complex.exp ((n : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]; push_cast; ring
    rw [h1]; simp

/-- The plane wave as a product of two exponentials:
`e^{-ik Re(z e^{-iφ})} = exp(α e^{-iφ}) exp(β e^{iφ})` with `α = -(ik/2) z`, `β = -(ik/2) z̄`. -/
lemma planeWave_eq_exp_mul k z φ :
    planeWave k z φ = Complex.exp (-(Complex.I * k / 2) * z * Complex.exp (-(φ * Complex.I))) *
      Complex.exp (-(Complex.I * k / 2) * conj z * Complex.exp (φ * Complex.I)) := by
  unfold planeWave
  rw [← Complex.exp_add]
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj]
  simp  
  ring_nf

/-- The terms of the double expansion of `e^{-imφ} exp(α e^{-iφ}) exp(β e^{iφ})`. -/
def monoTerm α β (m : ℕ) (pq : ℕ × ℕ) (φ : ℝ)  :=
  α ^ pq.1 * β ^ pq.2 / ((pq.1.factorial : ℂ) * pq.2.factorial) *
    Complex.exp ((((pq.2 : ℤ) - pq.1 - m : ℤ) : ℂ) * φ * Complex.I)

lemma hasSum_exp_series w :
    HasSum (fun n : ℕ => w ^ n / (n.factorial : ℂ)) (Complex.exp w) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp w

lemma summable_norm_exp_series w :
    Summable (fun n : ℕ => ‖w ^ n / (n.factorial : ℂ)‖) := by
  simpa  using Real.summable_pow_div_factorial ‖w‖

lemma hasSum_exp_mul_exp u v : HasSum (fun x : ℕ × ℕ =>
      (u ^ x.1 / (x.1.factorial : ℂ)) * (v ^ x.2 / (x.2.factorial : ℂ)))
      (Complex.exp u * Complex.exp v) := by
  have hs := summable_mul_of_summable_norm (R := ℂ) (f := fun n : ℕ => u ^ n / n.factorial)
    (g := fun n : ℕ => v ^ n / n.factorial) (summable_norm_exp_series u)
    (summable_norm_exp_series v)
  have ht := tsum_mul_tsum_of_summable_norm (R := ℂ)
    (f := fun n : ℕ => u ^ n / n.factorial) (g := fun n : ℕ => v ^ n / n.factorial)
    (summable_norm_exp_series u) (summable_norm_exp_series v)
  rw [(hasSum_exp_series u).tsum_eq, (hasSum_exp_series v).tsum_eq] at ht
  rw [ht]
  exact hs.hasSum

section
variable (α β : ℂ) (m : ℕ)
include α β m

lemma hasSum_monoTerm φ :
    HasSum (fun pq => monoTerm α β m pq φ)
      (Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        (Complex.exp (α * Complex.exp (-(φ * Complex.I))) *
          Complex.exp (β * Complex.exp (φ * Complex.I)))) := by
  have h := (hasSum_exp_mul_exp (α * Complex.exp (-(φ * Complex.I)))
    (β * Complex.exp (φ * Complex.I))).mul_left (Complex.exp (-(m * φ * Complex.I)))
  convert h using 1
  funext pq
  obtain ⟨p, q⟩ := pq
  simp only [monoTerm, mul_pow, ← Complex.exp_nat_mul]
  have : Complex.exp ((((q : ℤ) - p - m : ℤ) : ℂ) * φ * Complex.I) =
      Complex.exp (-((m : ℂ) * φ * Complex.I)) * Complex.exp (p * -(φ * Complex.I)) *
        Complex.exp (q * (φ * Complex.I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; push_cast; ring
  rw [this]
  field_simp

lemma norm_monoTerm pq φ :
    ‖monoTerm α β m pq φ‖ =
      ‖α ^ pq.1 / (pq.1.factorial : ℂ)‖ * ‖β ^ pq.2 / (pq.2.factorial : ℂ)‖ := by
  rw [monoTerm, norm_mul, show (((((pq.2 : ℤ) - pq.1 - m : ℤ)) * φ * Complex.I)) =
      ((((pq.2 : ℤ) - pq.1 - m : ℤ) * φ : ℝ)) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, mul_div_mul_comm, norm_mul]

lemma integral_monoTerm pq :
    ∫ φ in (0 : ℝ)..circlePeriod, monoTerm α β m pq φ =
      if pq.2 = pq.1 + m then α ^ pq.1 * β ^ pq.2 / ((pq.1.factorial : ℂ) * pq.2.factorial) *
        ((2 * π : ℝ) : ℂ) else 0 := by
  unfold monoTerm
  rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
  grind

theorem hasSum_integral_monoTerm :
    HasSum (fun pq => ∫ φ in (0 : ℝ)..circlePeriod, monoTerm α β m pq φ)
      (∫ φ in (0 : ℝ)..circlePeriod, Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        (Complex.exp (α * Complex.exp (-(φ * Complex.I))) *
          Complex.exp (β * Complex.exp (φ * Complex.I)))) := by
  have hb  :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun n : ℕ => ‖α ^ n / n.factorial‖)
      (g := fun n : ℕ => ‖β ^ n / n.factorial‖)
      (by simpa using summable_norm_exp_series α) (by simpa using summable_norm_exp_series β)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun pq _ => ‖α ^ pq.1 / pq.1.factorial‖ * ‖β ^ pq.2 / pq.2.factorial‖)
    (fun pq => ?_) (fun pq => Eventually.of_forall fun φ _ => (norm_monoTerm α β m pq φ).le)
    (Eventually.of_forall fun φ _ => hb) intervalIntegrable_const
    (Eventually.of_forall fun φ _ => hasSum_monoTerm α β m φ)
  unfold monoTerm
  fun_prop

end


/-- The monomial direction density `φ ↦ e^{-imφ}`. -/
def monoDensity (m : ℕ) (φ : ℝ)  := Complex.exp (-((m : ℂ) * φ * Complex.I))

/-- **Herglotz wave of a monomial density.** With `α = -(ik/2) z` and `β = -(ik/2) z̄`,
`u_{e^{-im·}}(z) = ∑_{p ≥ 0} α^p β^{p+m} / (p! (p+m)!)`. -/
theorem hasSum_herglotzWave_monoDensity (k : ℝ) m z :
    HasSum (fun p : ℕ => (-(Complex.I * k / 2) * z) ^ p * (-(Complex.I * k / 2) * conj z) ^ (p + m) /
      ((p.factorial : ℂ) * (p + m).factorial)) (herglotzWave k (monoDensity m) z) := by
  set α := -(Complex.I * k / 2) * z
  set β := -(Complex.I * k / 2) * conj z
  have h := (hasSum_integral_monoTerm α β m).mul_left ((2 * π : ℝ) : ℂ)⁻¹
  have hw : herglotzWave k (monoDensity m) z = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ φ in (0 : ℝ)..circlePeriod, Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        (Complex.exp (α * Complex.exp (-(φ * Complex.I))) *
          Complex.exp (β * Complex.exp (φ * Complex.I))) := by
    grind only [herglotzWave, monoDensity, planeWave_eq_exp_mul]
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  simp only [integral_monoTerm] at h
  rw [← (show Function.Injective (fun p : ℕ => (p, p + m)) from
    fun a b hab => (Prod.mk.inj hab).1).hasSum_iff] at h
  · convert h using 1
    grind
  grind

/-- The terms `(-E/4)^j m! / (j! (m+j)!) z^j z̄^{m+j}` of the transmutation `𝒱_E z̄^m`. -/
def vekuaMonoTerm (E : ℝ) m z j  :=
  (-(E : ℂ) / 4) ^ j * m.factorial / ((j.factorial : ℂ) * (m + j).factorial) *
    z ^ j * conj z ^ (m + j)

/-- **Lemma 5.8 (transmutation of antiholomorphic monomials).** For `k ≠ 0` the series
`𝒱_{k²} z̄^m` converges and equals `m! (-ik/2)^{-m}` times the Herglotz wave with direction
density `e^{-imφ}`. -/
theorem hasSum_vekuaMonoTerm  (hk : k ≠ 0) m z :
    HasSum (vekuaMonoTerm (k ^ 2) m z)
      ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹ * herglotzWave k (monoDensity m) z) := by
  have hw : (-(Complex.I * k / 2)) ≠ 0 := by
    simp_all
  convert (hasSum_herglotzWave_monoDensity k m z).mul_left
    (m.factorial * ((-(Complex.I * k / 2)) ^ m)⁻¹) using 1
  funext j
  unfold vekuaMonoTerm
  have hsq : (-(Complex.I * k / 2)) ^ 2 = -((k ^ 2 : ℝ) : ℂ) / 4 := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [mul_pow, mul_pow, pow_add, ← hsq, ← pow_mul]
  field_simp
  ring_nf

/-- The Herglotz coefficients of a monomial density are Herglotz waves of monomial densities. -/
lemma herglotzCoeff_monoDensity k (m n : ℕ) z :
    herglotzCoeff k (monoDensity m) n z = herglotzWave k (monoDensity (m + n)) z := by
  unfold herglotzCoeff herglotzWave monoDensity
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast; ring

/-- At the origin the Herglotz wave of `e^{-imφ}` is `[m = 0]`. -/
lemma herglotzWave_monoDensity_zero k m :
    herglotzWave k (monoDensity m) 0 = if m = 0 then 1 else 0 := by
  have h := hasSum_herglotzWave_monoDensity k m 0
  refine h.unique ?_
  convert hasSum_single (f := fun p : ℕ => (-(Complex.I * k / 2) * 0) ^ p *
    (-(Complex.I * k / 2) * conj 0) ^ (p + m) /
      (p.factorial * (p + m).factorial)) 0 ?_ using 1
  · split_ifs with hm <;> simp [hm]
  · intro p hp
    simp [hp]

/-! ### Antiholomorphic polynomials -/

/-- The antiholomorphic polynomial `h(z) = ∑_{m ∈ s} c_m z̄^m`. -/
def antiPoly s (c : ComplexSeq) z  := ∑ m ∈ s, c m * conj z ^ m

/-- The direction density `∑_{m ∈ s} c_m m! (-ik/2)^{-m} e^{-imφ}` whose Herglotz wave is
`𝒱_{k²} h`. -/
def polyDensity (k : ℝ) s (c : ComplexSeq) φ  :=
  ∑ m ∈ s, c m * ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹) * monoDensity m φ

@[fun_prop]
lemma continuous_monoDensity m : Continuous (monoDensity m) := by
  unfold monoDensity; fun_prop

section
variable (k : ℝ) (s : Finset ℕ)
include k s

lemma continuous_polyDensity c :
    Continuous (polyDensity k s c) := by
  fun_prop [polyDensity]

lemma isDirDensity_polyDensity c :
    IsDirDensity (polyDensity k s c) := by
  have hc := continuous_polyDensity k s c
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun φ hφ => hC φ (Ioc_subset_Icc_self hφ)

/-- Herglotz coefficients are linear in finite combinations of monomial densities. -/
lemma herglotzCoeff_finset_sum (b : ComplexSeq) n z :
    herglotzCoeff k (fun φ => ∑ m ∈ s, b m * monoDensity m φ) n z =
      ∑ m ∈ s, b m * herglotzCoeff k (monoDensity m) n z := by
  unfold herglotzCoeff
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_assoc, mul_comm (b m), mul_assoc, ← intervalIntegral.integral_const_mul (b m),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    grind
  · intro m _
    exact (Continuous.intervalIntegrable (by
      fun_prop) _ _)

lemma polyDensity_eq c :
    polyDensity k s c = fun φ => ∑ m ∈ s,
      (c m * ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹)) * monoDensity m φ := rfl

end


/-- The initial Herglotz vector of `𝒱_{k²} h` at the origin is `(h(0)/√2) e₀`. -/
theorem herglotzVec_polyDensity_zero {k : ℝ} (s : Finset ℕ) (c : ComplexSeq) :
    herglotzVec (isDirDensity_polyDensity k s c) k 0 =
      (antiPoly s c 0 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  have hsum : ∀ n : ℕ, herglotzCoeff k (polyDensity k s c) n 0 =
      if n = 0 then antiPoly s c 0 else 0 := by
    intro n
    rw [polyDensity_eq, herglotzCoeff_finset_sum, antiPoly]
    split_ifs with hn
    · subst hn
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [herglotzCoeff_monoDensity, Nat.add_zero, herglotzWave_monoDensity_zero]
      aesop
    simp_all [herglotzCoeff_monoDensity, herglotzWave_monoDensity_zero]
  apply lp.ext
  funext n
  simp  [herglotzSeq, basisVec]
  aesop

/-! ### The Cauchy test for the kernel of `O_E^*` (Lemma 5.11, compatibility part) -/

end PolyaNeumann
