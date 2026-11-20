module
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Coefficients.PrimitiveProductsAndSupportedPrimeProfiles

public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.DualDyadicRectangles
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.PrimitivePairPhaseSeparation
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.CoreEnergyAndPairMasks
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.ReflectedCoreRowPrefix

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem reflected_weighted_sum_le (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B)
    (g : Ideal (𝓞 F) → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∑ a ∈ C.reflectedRows B unit, Real.sqrt (B / norm a) * g a) ≤
      ∑ t ∈ squarefreeBadPool c, ∑ r ∈ C.reflectedCoreRows B unit, g (t * r) := by
  have hweight : ∀ a ∈ C.reflectedRows B unit, Real.sqrt (B / norm a) ≤ 1 := by
    intro a ha
    obtain ⟨⟨t, r⟩, htr, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hprod, hmask⟩ := Finset.mem_filter.mp htr
    have hr := (Finset.mem_product.mp hprod).2
    have htn : 1 ≤ norm t := by
      dsimp [norm]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (fun ht0 => hmask.2.2 (by simp [ht0])))
    have hrn : B ≤ norm r := by
      cases unit with
      | false =>
        exact ((Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1).2.2.1.le
      | true =>
        have heq : r = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp hr).1
        rw [heq, hunit rfl]
        simp [norm]
    have han : B ≤ norm (t * r) := by
      have hnorm : norm (t * r) = norm t * norm r := by simp [norm, map_mul]
      rw [hnorm]
      exact hrn.trans (le_mul_of_one_le_left (by dsimp [norm]; positivity) htn)
    apply Real.sqrt_le_one.mpr
    exact (div_le_one (lt_of_lt_of_le zero_lt_one (hB.trans han))).mpr han
  calc
    _ ≤ ∑ a ∈ C.reflectedRows B unit, g a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_of_le_one_left (hg a) (hweight a ha)
    _ ≤ ∑ tr ∈ C.reflectedRowIndices B unit, g (tr.1 * tr.2) :=
      Finset.sum_image_le_of_nonneg (fun a _ => hg a)
    _ ≤ ∑ tr ∈ (squarefreeBadPool c) ×ˢ C.reflectedCoreRows B unit,
        g (tr.1 * tr.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun tr _ _ => hg _)
    _ = _ := Finset.sum_product _ _ _

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

section

variable (C : Context Q)

def divisorEnergy (f : Ideal (𝓞 F)) : ℝ :=
  ∑ u ∈ C.columns,
    if f ∣ u then
      (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
        ‖C.lam (C.d * u)‖ ^ 2
    else 0

def rowDivisorBlock (e f₁ f₂ a : Ideal (𝓞 F)) : ℂ :=
  C.pairSum fun p hp =>
    if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
      C.coefficient p * C.primitive p hp e * C.primitive p hp a
    else 0

theorem chosen_primitive_on_core
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : Context.ValidPair C p)
    (r : Ideal (𝓞 F)) (hrc : r ⊔ c = ⊤) :
    C.primitive p hp r = (Q.χ p.1) r * star ((Q.χ p.2) r) := by apply @DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin.PrimitiveProductsAndSupportedPrimeProfiles.primitive_core <;> assumption

theorem chosen_primitive_phase_core :
    ∃ phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ,
      (∀ u ∈ C.columns, ∀ z, ‖phase u z‖ ≤ 1) ∧
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ z, z ≠ ⊥ → (∀ u ∈ C.columns, z ⊔ u = ⊤) →
      ∀ r, r ⊔ c = ⊤ →
        C.primitive p hp z * C.primitive p hp r =
          (phase p.1 z * (Q.χ p.1) r) *
            star (phase p.2 z * (Q.χ p.2) r) := by
  have hcols : ∀ u ∈ C.columns, Squarefree u ∧ u ⊔ c = ⊤ := by
    intro u hu
    have h := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1
    exact ⟨h.1, h.2.1⟩
  have hclass : ∀ u ∈ C.columns, ∀ v ∈ C.columns, Q.cls u = Q.cls v := by
    intro u hu v hv
    letI := Q.instGroup
    have hh := ((Finset.mem_filter.mp hu).2.2).trans ((Finset.mem_filter.mp hv).2.2).symm
    rw [Q.cls_mul C.d u C.hdc (hcols u hu).2,
      Q.cls_mul C.d v C.hdc (hcols v hv).2] at hh
    exact mul_left_cancel hh
  obtain ⟨phase, hphase, hsplit⟩ := PrimitivePhases.primitive_pair_phase_separation Q
    C.D.original_ne_bot C.columns hcols hclass
  refine ⟨phase, hphase, ?_⟩
  intro p hpairs hp z hz hzc r hrc
  have hpcols := Finset.mem_product.mp (Finset.mem_filter.mp hpairs).1
  rw [hsplit p.1 hpcols.1 p.2 hpcols.2 hp.huv (C.primitive p hp)
    (C.primitive_spec p hp).2.1 z hz hzc, chosen_primitive_on_core C p hp r hrc,
    star_mul]
  ring

theorem mobius_divisor_coprime_columns
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors) :
    e ≠ ⊥ ∧ ∀ u ∈ C.columns, e ⊔ u = ⊤ := by
  refine ⟨ne_bot_of_mem_idealDivisors he, ?_⟩
  intro u hu
  have hdcoprime : C.d ⊔ u = ⊤ := by
    rw [← Ideal.gcd_eq_sup]
    exact Ideal.isUnit_iff.mp (gcd_isUnit_iff_isRelPrime.mpr ((squarefree_mul_iff.mp (((Sieve.mem_paperShell _ _ _ _).mp (Finset.mem_filter.mp hu).2.1).1)).1))
  have hcu : c ⊔ u = ⊤ := by simpa only [sup_comm] using ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1).2.1
  have hmult : c * C.d ⊔ u = ⊤ :=
    ((Ideal.isCoprime_iff_sup_eq.mpr hcu).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr hdcoprime)).sup_eq
  apply top_unique
  rw [← hmult]
  refine sup_le_sup_right (Ideal.dvd_iff_le.mp ?_) u
  exact Ideal.dvd_iff_le.mpr (le_trans Ideal.le_radical
  (Ideal.dvd_iff_le.mp ((mem_idealDivisors (fun hh => (mul_ne_zero C.D.original_ne_bot C.hd0) (bot_unique (hh ▸ Ideal.le_radical)))).mp he)))

end

alias finite_coprime_sum_bound := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows.CoreEnergyAndPairMasks.finite_coprime_sum_bound

section

variable (C : Context Q)

theorem supported_factor_coprime_columns
    (t : Ideal (𝓞 F)) (ht : t ∈ squarefreeBadPool c) :
    t ≠ ⊥ ∧ ∀ u ∈ C.columns, t ⊔ u = ⊤ := by
  obtain ⟨ht0, -, hsupp⟩ := (mem_squarefreeBadPool C.D.original_ne_bot).mp ht
  refine ⟨ht0, ?_⟩
  intro u hu
  by_contra hne
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (t ⊔ u) hne
  have hpt := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
  exact hp.ne_top (top_unique ((((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
    (Finset.mem_filter.mp hu).1).2.1) ▸ sup_le
    (le_trans le_sup_right hle) (Ideal.dvd_iff_le.mp (hsupp p (Ideal.prime_of_isPrime (fun heq => ht0 (eq_bot_iff.mpr (heq ▸ Ideal.dvd_iff_le.mp hpt))) hp.isPrime) hpt))))

theorem supported_primitive_phase_core :
    ∃ phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ,
      (∀ u ∈ C.columns, ∀ z, ‖phase u z‖ ≤ 1) ∧
      ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ r, r ⊔ c = ⊤ →
        C.primitive p hp e * C.primitive p hp (t * r) =
          (phase p.1 (e * t) * (Q.χ p.1) r) *
            star (phase p.2 (e * t) * (Q.χ p.2) r) := by
  obtain ⟨phase, hphase, hsplit⟩ := chosen_primitive_phase_core C
  refine ⟨phase, hphase, ?_⟩
  intro e he t ht p hpairs hp r hrc
  obtain ⟨he0, hecols⟩ := mobius_divisor_coprime_columns C e he
  obtain ⟨ht0, htcols⟩ := supported_factor_coprime_columns C t ht
  have hetcols : ∀ u ∈ C.columns, e * t ⊔ u = ⊤ := fun u hu => ((Ideal.isCoprime_iff_sup_eq.mpr (hecols u hu)).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr (htcols u hu))).sup_eq
  have hh := hsplit p hpairs hp (e * t) (mul_ne_zero he0 ht0) hetcols r hrc
  rw [(C.primitive p hp).map_mul' e t] at hh
  rw [(C.primitive p hp).map_mul' t r]
  simpa only [mul_assoc] using hh

theorem rowDivisorBlock_eq_phase_sum
    (phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hphase : ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ r, r ⊔ c = ⊤ → C.primitive p hp e * C.primitive p hp (t*r) =
        (phase p.1 (e*t) * (Q.χ p.1) r) * star (phase p.2 (e*t) * (Q.χ p.2) r))
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (t : Ideal (𝓞 F)) (ht : t ∈ squarefreeBadPool c)
    (f₁ f₂ r : Ideal (𝓞 F)) (hrc : r ⊔ c = ⊤) :
    rowDivisorBlock C e f₁ f₂ (t*r) =
      ∑ p ∈ C.pairs, if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
        (C.lam (C.d*p.1) * phase p.1 (e*t)) *
          star (C.lam (C.d*p.2) * phase p.2 (e*t)) *
          (Q.χ p.1) r * star ((Q.χ p.2) r)
      else 0 := by
  unfold rowDivisorBlock Context.pairSum
  apply Finset.sum_congr rfl
  intro p hp
  have hpvalid := (Finset.mem_filter.mp hp).2
  rw [dif_pos hpvalid]
  dsimp only
  split_ifs with h
  · rw [mul_assoc, hphase e he t ht p hp hpvalid r hrc]
    simp only [Context.coefficient, star_mul]
    ring
  · rfl

end

theorem supported_divisible_pair_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∃ H : ℝ, 0 < H ∧
      ∀ (C : Context Q), C.D = D →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
      ∀ e ∈ C.mobiusDivisors,
      ∀ (P : ℝ × ℝ), P ∈ admissibleRectangles C B →
      ∀ f₁ f₂ : Ideal (𝓞 F),
        ErrorRectangles.InBin P.1 f₁ → ErrorRectangles.InBin P.2 f₂ →
        (∑ a ∈ C.reflectedRows B unit,
            Real.sqrt (B / norm a) * ‖rowDivisorBlock C e f₁ f₂ a‖) ≤
          H * Real.sqrt
            (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
             ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
            Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
  obtain ⟨A, hA, hcore⟩ := SupportedRows.core_divisible_pair_bound D
  let n : ℝ := (squarefreeBadPool c).card
  refine ⟨(n + 1) * A, mul_pos (by dsimp [n]; positivity) hA, ?_⟩
  intro C hCD B unit hunit hM hN hB hBK hKM hn hnN e he P hP f₁ f₂ hf₁ hf₂
  obtain ⟨phase, hphase, hsplit⟩ := supported_primitive_phase_core C
  have hends := ErrorRectangles.rectangle_endpoints C P (Finset.mem_filter.mp hP).1
  have hPf₁ : P.1 ≤ norm f₁ := by
    have hh := hf₁.2.1
    split_ifs at hh with hp
    · simpa only [hp] using hh
    · exact hh.le
  have hPf₂ : P.2 ≤ norm f₂ := by
    have hh := hf₂.2.1
    split_ifs at hh with hp
    · simpa only [hp] using hh
    · exact hh.le
  have hrows := SupportedRows.reflected_core_rows_subset C B unit hunit hB
  let sqrt₀ := Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) * ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))
  have hlocal : ∀ t ∈ squarefreeBadPool c,
      (∑ r ∈ C.reflectedCoreRows B unit, ‖rowDivisorBlock C e f₁ f₂ (t * r)‖) ≤
        A * sqrt₀ *
          Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
    intro t ht
    let x : Ideal (𝓞 F) → ℂ := fun u => C.lam (C.d * u) * phase u (e * t)
    have hx : ∀ u ∈ C.columns, ‖x u‖ ≤ ‖C.lam (C.d * u)‖ := by
      intro u hu
      dsimp [x]
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hphase u hu (e * t))
    have hh := hcore C hCD hN B P.1 P.2 hB hends.1 hends.2.1 f₁ f₂
      hf₁.1 hf₂.1 hPf₁ hPf₂ (C.reflectedCoreRows B unit) hrows x x hx hx
    have heq : ∀ r ∈ C.reflectedCoreRows B unit,
        rowDivisorBlock C e f₁ f₂ (t * r) =
          SupportedRows.coreBlock C f₁ f₂ x x r := by
      intro r hr
      have hrc := ((Sieve.mem_idealAdmissibleFinset F c (2 * B) r).mp (hrows hr)).2.1
      simpa only [SupportedRows.coreBlock, x] using
        rowDivisorBlock_eq_phase_sum C phase hsplit e he t ht f₁ f₂ r hrc
    calc
      _ = ∑ r ∈ C.reflectedCoreRows B unit,
          ‖SupportedRows.coreBlock C f₁ f₂ x x r‖ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [heq r hr]
      _ ≤ _ := by simpa only [SupportedRows.energy, divisorEnergy] using hh
  calc
    _ ≤ ∑ t ∈ squarefreeBadPool c, ∑ r ∈ C.reflectedCoreRows B unit,
        ‖rowDivisorBlock C e f₁ f₂ (t * r)‖ :=
      SupportedRows.reflected_weighted_sum_le C B unit hunit hB
        (fun a => ‖rowDivisorBlock C e f₁ f₂ a‖) (fun a => norm_nonneg _)
    _ ≤ ∑ t ∈ squarefreeBadPool c,
        A * sqrt₀ *
          Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) :=
      Finset.sum_le_sum hlocal
    _ = n * A * sqrt₀ *
          Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      dsimp [n]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith : n ≤ n + 1) hA.le

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

end

end
