module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.FourierRectangles.DivisorBucketsCostsAndThresholds

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

lemma weighted_energy_bound (C : Context Q) (hN : 1 ≤ C.N) :
    weightedEnergy C ≤ (norm C.d / C.N) * Sieve.energy F c C.N C.lam := by
  unfold weightedEnergy weightedColumn
  classical
  have hNpos : 0 < C.N := lt_of_lt_of_le zero_lt_one hN
  have hdpos : 0 < norm C.d := by
    have hd : Ideal.absNorm C.d ≠ 0 := fun h => C.hd0 (Ideal.absNorm_eq_zero_iff.mp h)
    unfold ExplicitTerms.norm
    exact_mod_cast Nat.pos_of_ne_zero hd
  rw [Sieve.energy, Finset.mul_sum]
  apply Finset.sum_le_sum_of_injOn (fun u => C.d * u)
  · intro u hu v hv h
    exact mul_left_cancel₀ C.hd0 h
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨u, hu, rfl⟩
    exact (Finset.mem_filter.mp hu).2.1
  · intro u hu
    have hmem := (Finset.mem_filter.mp hu).2.1
    have hlow := ((Sieve.mem_paperShell F c C.N (C.d * u)).mp hmem).2.2.1
    have hmul : norm (C.d * u) = norm C.d * norm u := by
      simp only [ExplicitTerms.norm, map_mul, Nat.cast_mul]
    change C.N < norm (C.d * u) at hlow
    rw [hmul] at hlow
    have hup : 0 < norm u := by
      have hnonneg : 0 ≤ norm u := by unfold ExplicitTerms.norm; positivity
      nlinarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hup.le]
    have hinv : 1 / norm u ≤ norm C.d / C.N := by
      rw [div_le_div_iff₀ hup hNpos]
      simpa only [one_mul] using hlow.le
    calc
      ‖C.lam (C.d * u)‖ ^ 2 / norm u =
          (1 / norm u) * ‖C.lam (C.d * u)‖ ^ 2 := by ring
      _ ≤ (norm C.d / C.N) * ‖C.lam (C.d * u)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
  · intro b hb hbnot
    exact mul_nonneg (div_nonneg hdpos.le hNpos.le) (sq_nonneg _)

section

variable (T : ℝ) (f : Ideal (𝓞 F))

private lemma bucket_exists
    (hf0 : f ≠ ⊥) (hf : norm f ≤ T) :
    ∃ j ∈ Finset.range (Vendor.dyadicLength T + 1),
      f ∈ divisorBucket F T j := by
  have hfn : 1 ≤ norm f := by
    unfold ExplicitTerms.norm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hf0)
  have hcover : ∃ j : ℕ, norm f < (2 : ℝ) ^ (j + 1) := by
    refine ⟨Vendor.dyadicLength T, ?_⟩
    have hx := Vendor.dyadicLength_cover T
    rw [pow_succ]
    nlinarith
  let j := Nat.find hcover
  have hj : norm f < (2 : ℝ) ^ (j + 1) := Nat.find_spec hcover
  have hjle : j ≤ Vendor.dyadicLength T := Nat.find_min' hcover (by
    have hx := Vendor.dyadicLength_cover T
    rw [pow_succ]
    nlinarith)
  have hl : (2 : ℝ) ^ j ≤ norm f := by
    rcases hj0 : j with _ | k
    · exact hfn
    · have hh := Nat.find_min hcover (show k < j from by omega)
      change ¬ norm f < (2 : ℝ) ^ (k + 1) at hh
      exact le_of_not_gt hh
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨mem_boundedNormIdeals.mpr hf, hf0, hl, ?_⟩
  simpa [divisorScale, pow_succ, mul_comm] using hj

private lemma bucket_unique (i j : ℕ)
    (hi : f ∈ divisorBucket F T i) (hj : f ∈ divisorBucket F T j) : i = j := by
  have hi := (Finset.mem_filter.mp hi).2
  have hj := (Finset.mem_filter.mp hj).2
  have step {a b : ℕ} (hab : a < b) : 2 * divisorScale a ≤ divisorScale b := by
    dsimp [divisorScale]
    calc
      _ = (2 : ℝ) ^ (a + 1) := by rw [pow_succ'];
      _ ≤ (2 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hab
  rcases lt_trichotomy i j with h | h | h
  · have hs := step h
    linarith [hi.2.2, hj.2.1]
  · exact h
  · have hs := step h
    linarith [hj.2.2, hi.2.1]

end

section

variable (C : Context Q)

private lemma quotient_prefix (u : Ideal (𝓞 F)) (hu : u ∈ C.columns)
    (j : ℕ) (f : Ideal (𝓞 F)) (hf : f ∈ idealDivisors u)
    (hb : f ∈ divisorBucket F (2 * C.N / norm C.d) j) :
    ∃ v : Ideal (𝓞 F), v ≠ ⊥ ∧ u = f * v ∧
      v ∈ Sieve.idealAdmissibleFinset F c
        (2 * (C.N / (norm C.d * divisorScale j))) := by
  obtain ⟨hsf, hcop, hunorm⟩ := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
    (Finset.mem_filter.mp hu).1
  obtain ⟨v, hv⟩ := (mem_idealDivisors hsf.ne_zero).mp hf
  have hvdiv : v ∣ u := by rw [hv]; exact dvd_mul_left _ _
  have hdpos : 0 < norm C.d := by
    dsimp [ExplicitTerms.norm]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.hd0)
  have hprod : norm u = norm f * norm v := by simp [hv, ExplicitTerms.norm, map_mul]
  have hvnorm : norm v ≤ 2 * C.N / (norm C.d * divisorScale j) := by
    apply (le_div_iff₀ (mul_pos hdpos (by dsimp [divisorScale]; positivity))).mpr
    have hu' := (le_div_iff₀ hdpos).mp hunorm
    change norm u * norm C.d ≤ 2 * C.N at hu'
    calc
      norm v * (norm C.d * divisorScale j) =
          (divisorScale j * norm v) * norm C.d := by ring
      _ ≤ (norm f * norm v) * norm C.d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((Finset.mem_filter.mp hb).2.2.1) (Nat.cast_nonneg _)) hdpos.le
      _ ≤ 2 * C.N := by rwa [← hprod]
  refine ⟨v, ((hsf.squarefree_of_dvd hvdiv).ne_zero), hv, ?_⟩
  apply (Sieve.mem_idealAdmissibleFinset _ _ _ _).mpr
  refine ⟨hsf.squarefree_of_dvd hvdiv, ?_, ?_⟩
  · exact eq_top_iff.mpr (hcop ▸ sup_le_sup_right (Ideal.dvd_iff_le.mp hvdiv) c)
  · change norm v ≤ _
    convert hvnorm using 1 <;> ring

private lemma reflected_unit (hK : 1 ≤ C.K) :
    C.reflectedRows 1 true = squarefreeBadPool c := by
  have hunit : ReflectedSigma4.unitRows c c C.K = {⊤} := by
    have hsc : sc c (⊤ : Ideal (𝓞 F)) = 1 := by
      unfold sc primeToSquarefreeKernel
      rw [(Sieve.squarefreeKernel_eq_self (by simpa using squarefree_one)), ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
      simp
    simp [ReflectedSigma4.unitRows, hsc, hK,
      show Squarefree (⊤ : Ideal (𝓞 F)) from by simpa using squarefree_one]
  have hsf : ∀ a ∈ squarefreeBadPool c, a ≠ ⊥ ∧ Squarefree a := fun a ha => ((mem_squarefreeBadPool C.D.original_ne_bot).mp ha).imp_right (fun h => h.1)
  ext a
  simp only [Context.reflectedRows, Context.reflectedRowIndices, Context.reflectedCoreRows,
    Bool.true_eq, ↓reduceIte, hunit, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨t,r⟩, ⟨⟨ht, hr⟩, hrest⟩, he⟩
    dsimp at hr he
    subst r
    simpa only [Ideal.mul_top] using he ▸ (show t * ⊤ ∈ squarefreeBadPool c by simpa using ht)
  · intro ha
    obtain ⟨ha0, hasf⟩ := hsf a ha
    refine ⟨(a, ⊤), ⟨⟨ha, rfl⟩, ?_⟩, ?_⟩ <;> simp [hasf, ha0]

end

theorem exists_unique_divisor_bucket (C : Context Q) {u : Ideal (𝓞 F)} (hu : u ∈ C.columns)
    {f : Ideal (𝓞 F)} (hf : f ∈ idealDivisors u) :
      ∃! j : ℕ, j ∈ Finset.range (Vendor.dyadicLength (2 * C.N / norm C.d) + 1) ∧
        f ∈ divisorBucket F (2 * C.N / norm C.d) j := by
  have hunorm := ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
    (Finset.mem_filter.mp hu).1).2.2
  have hfu : norm f ≤ norm u := by
    unfold ExplicitTerms.norm
    exact_mod_cast absNorm_le_of_mem_idealDivisors hf
  have hfnorm : norm f ≤ 2 * C.N / norm C.d := hfu.trans hunorm
  obtain ⟨j, hj, hfj⟩ := bucket_exists _ f (ne_bot_of_mem_idealDivisors hf) hfnorm
  refine ⟨j, ⟨hj, hfj⟩, ?_⟩
  intro i hi
  exact bucket_unique _ f i j hi.2 hfj

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles

end
