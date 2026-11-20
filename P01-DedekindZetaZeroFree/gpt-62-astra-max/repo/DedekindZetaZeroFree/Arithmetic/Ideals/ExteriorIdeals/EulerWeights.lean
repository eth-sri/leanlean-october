module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]

local notation "IntegerIdeal" => Ideal (𝓞 F)

def idealNorm (I : IntegerIdeal) : ℝ := (Ideal.absNorm I : ℝ)

def NonzeroIdeal (F : Type) [Field F] [NumberField F] :=
  { I : Ideal (𝓞 F) // I ≠ ⊥ }

def ExteriorIdeal (cS : IntegerIdeal) :=
  { I : IntegerIdeal // I ≠ ⊥ ∧ I ⊔ cS = ⊤ }

def ExteriorSquarefreeIdeal (cS : IntegerIdeal) :=
  { I : ExteriorIdeal cS // Squarefree I.val }

def idealPrimeSupport (I : IntegerIdeal) : Finset IntegerIdeal :=
  (normalizedFactors I).toFinset

def idealPrimeExponent (p I : IntegerIdeal) : ℕ :=
  (normalizedFactors I).count p

def Powerful (h : IntegerIdeal) : Prop :=
  ∀ p : IntegerIdeal, Prime p →
    idealPrimeExponent p h = 0 ∨ 2 ≤ idealPrimeExponent p h

def idealRadical (h : IntegerIdeal) : IntegerIdeal :=
  ∏ p ∈ idealPrimeSupport h, p

def IdealSupportedOn (a f : IntegerIdeal) : Prop :=
  idealPrimeSupport a ⊆ idealPrimeSupport f

def betaLocal (Q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then Real.rpow Q (-(e / 3 : ℕ) : ℝ)
  else if e % 3 = 0 then Real.rpow Q ((1 / 2 : ℝ) - (e / 3 : ℕ))
  else 0

def betaIdeal {cS : IntegerIdeal} (f : ExteriorSquarefreeIdeal cS)
    (a : IntegerIdeal) : ℝ :=
  if a ≠ ⊥ ∧ a ⊔ cS = ⊤ ∧ IdealSupportedOn a f.val.val then
    ∏ p ∈ idealPrimeSupport f.val.val, betaLocal (idealNorm p) (idealPrimeExponent p a)
  else 0

def eulerLocal (Q σ : ℝ) : ℝ :=
  1 + (Real.rpow Q (-σ) + Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ)) /
    (1 - Real.rpow Q (-1 - 3 * σ))

def eulerIdeal {cS : IntegerIdeal} (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) : ℝ :=
  ∏ p ∈ idealPrimeSupport f.val.val, eulerLocal (idealNorm p) σ

def rowNorm {cS : IntegerIdeal} (a c n : ExteriorIdeal cS) : ℝ :=
  idealNorm a.val * idealNorm c.val * idealNorm n.val ^ 3

theorem idealNorm_ge_one (I : IntegerIdeal) (hI : I ≠ ⊥) : 1 ≤ idealNorm I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hI))

theorem idealNorm_prime_ge_two (p : IntegerIdeal) (hp : Prime p) :
    2 ≤ idealNorm p := by
  have hn0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have hn1 : Ideal.absNorm p ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr
    (fun ht => hp.not_isUnit (by simpa [ht] using (isUnit_one : IsUnit (1 : IntegerIdeal))))
  have hn : 2 ≤ Ideal.absNorm p := by omega
  change (2 : ℝ) ≤ (Ideal.absNorm p : ℝ)
  exact_mod_cast hn

section

variable (h : Ideal (𝓞 F))

private theorem radical_factors :
    normalizedFactors (idealRadical h) = (idealPrimeSupport h).val := by
  unfold idealRadical
  simp only [Finset.prod_eq_multiset_prod, Multiset.map_id']
  apply normalizedFactors_prod_of_prime
  intro p hp
  exact prime_of_normalized_factor p (by simpa only [idealPrimeSupport, Finset.mem_val, Multiset.mem_toFinset] using hp)

theorem idealPrimeExponent_radical (hh : h ≠ ⊥)
    (p : Ideal (𝓞 F)) (hp : Prime p) :
    idealPrimeExponent p (idealRadical h) =
      if p ∈ idealPrimeSupport h then 1 else 0 := by
  unfold idealPrimeExponent
  rw [radical_factors]
  exact Multiset.count_eq_of_nodup (idealPrimeSupport h).nodup

theorem idealRadical_squarefree_nonzero (hh : h ≠ ⊥) :
    Squarefree (idealRadical h) ∧ idealRadical h ≠ ⊥ := by
  have hn : idealRadical h ≠ 0 := by
    unfold idealRadical
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (prime_of_normalized_factor p (by
      simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)).ne_zero
  refine ⟨?_, hn⟩
  rw [squarefree_iff_nodup_normalizedFactors hn, radical_factors]
  exact (idealPrimeSupport h).nodup

end

theorem betaLocal_zero (Q : ℝ) : betaLocal Q 0 = 1 := by
  simp [betaLocal]

section

variable (Q : ℝ) (hQ : 2 ≤ Q)

include hQ in
theorem betaLocal_one_add_three_mul (k : ℕ) :
    betaLocal Q (1 + 3 * k) = Real.rpow Q (-(k : ℝ)) := by
  have h0 : 1 + 3 * k ≠ 0 := by omega
  have hm : (1 + 3 * k) % 3 = 1 := by omega
  have hd : (1 + 3 * k) / 3 = k := by omega
  simp [betaLocal, h0, hm, hd]

include hQ in
theorem betaLocal_three_mul (k : ℕ) (hk : 1 ≤ k) :
    betaLocal Q (3 * k) = Real.rpow Q ((1 / 2 : ℝ) - k) := by
  have h0 : 3 * k ≠ 0 := by omega
  have hm : (3 * k) % 3 = 0 := by omega
  have hd : (3 * k) / 3 = k := by omega
  simp [betaLocal, h0, hm, hd]

include hQ in
theorem betaLocal_two_add_three_mul (k : ℕ) :
    betaLocal Q (2 + 3 * k) = 0 := by
  have h0 : 2 + 3 * k ≠ 0 := by omega
  have hm : (2 + 3 * k) % 3 = 2 := by omega
  simp [betaLocal, h0, hm]

include hQ in
theorem betaLocal_nonneg (e : ℕ) :
    0 ≤ betaLocal Q e := by
  unfold betaLocal
  split_ifs <;> first | positivity | exact Real.rpow_nonneg (by linarith) _

end

def exteriorSquarefreeTop (cS : Ideal (𝓞 F)) : ExteriorSquarefreeIdeal cS :=
  ⟨⟨⊤, by simp⟩, by simpa using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))⟩

end

end DedekindZetaZeroFree
