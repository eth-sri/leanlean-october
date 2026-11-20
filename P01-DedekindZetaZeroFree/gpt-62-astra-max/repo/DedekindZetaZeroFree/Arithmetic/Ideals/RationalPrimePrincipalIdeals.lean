module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable def rationalPrincipalIdeal (F : Type) [Field F] [NumberField F]
    (p : ℕ) : Ideal (𝓞 F) :=
  Ideal.span ({(p : 𝓞 F)} : Set (𝓞 F))

variable (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)

include hp in
theorem rationalPrincipalIdeal_ne_bot : rationalPrincipalIdeal F p ≠ ⊥ := fun h => Nat.cast_ne_zero.mpr hp.ne_zero ((Ideal.span_singleton_eq_bot).mp h)

include hp in
theorem rationalPrincipalIdeal_absNorm :
    Ideal.absNorm (rationalPrincipalIdeal F p) = p ^ Module.finrank ℚ F := by
  rw [rationalPrincipalIdeal, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]

include hp in
theorem rationalPrincipalIdeal_squarefree (hunramified : ¬ (p : ℤ) ∣ NumberField.discr F) :
    Squarefree (rationalPrincipalIdeal F p) := by
  have hpZ := Nat.prime_iff_prime_int.mp hp
  rw [squarefree_iff_no_irreducibles (rationalPrincipalIdeal_ne_bot F hp)]
  intro Q hirr hdvd
  have hQprime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  have hle := Ideal.dvd_iff_le.mp hdvd
  have hpQnat :=
    (SetLike.le_def.mp (le_trans hle Ideal.mul_le_right)) (Ideal.mem_span_singleton_self _)
  have hpQ : ((p : ℤ) : 𝓞 F) ∈ Q := by simpa using hpQnat
  have hlies :=
    (Ideal.liesOver_span_iff hQprime.ne_top hpZ).mpr hpQ
  haveI := hlies
  haveI := hQprime
  haveI := ((NumberField.not_dvd_discr_iff_forall_mem F (𝓞 F) hpZ).mp hunramified Q hQprime hpQ)
  have h1 : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q
      (Ideal.span_singleton_eq_bot.not.mpr hpZ.ne_zero)]
    exact Ideal.ramificationIdx_eq_one Q ℤ
  have hmap_eq : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) =
      rationalPrincipalIdeal F p := by
    rw [Ideal.map_span, Set.image_singleton, rationalPrincipalIdeal]
    simp
  have hmap_le : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≤ Q := by
    rw [hlies.over]
    exact Ideal.map_comap_le
  exact (Ideal.ramificationIdx'_ne_one_iff hmap_le).mpr
    (by rw [hmap_eq, pow_two]; exact hle) h1

include hp in
theorem rationalPrincipalIdeal_sup_eq_top (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (havoid : ¬ p ∣ Ideal.absNorm I) :
    rationalPrincipalIdeal F p ⊔ I = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPprime := hPmax.isPrime
  have hpP :=
    (SetLike.le_def.mp hle) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hlies : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Ideal.liesOver_span_iff hPprime.ne_top (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa using hpP)
  haveI := hlies
  haveI := hPprime
  have hk : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos (q := P) (R := ℤ)
  have hpP' : p ∣ Ideal.absNorm P := by
    rw [((Ideal.pow_inertiaDeg p P).symm)]
    simpa using pow_dvd_pow p hk
  exact havoid (dvd_trans hpP' (Ideal.absNorm_dvd_absNorm_of_le (le_trans le_sup_right hle)))

include hp in
theorem rationalPrincipalIdeal_squarefree_coprime (q : Ideal (𝓞 F)) (hq : q ≠ ⊥)
    (hlarge : max (NumberField.discr F).natAbs (Ideal.absNorm q) < p) :
    Squarefree (rationalPrincipalIdeal F p) ∧
      rationalPrincipalIdeal F p ⊔ q = ⊤ := by
  have hdiscr : ¬ (p : ℤ) ∣ NumberField.discr F := by
    intro h
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)) (by
      have := Int.natAbs_dvd_natAbs.mpr h
      exact this)
    have h3 := le_max_left (NumberField.discr F).natAbs (Ideal.absNorm q)
    omega
  have havoid : ¬ p ∣ Ideal.absNorm q := by
    intro h
    have h2 := Nat.le_of_dvd (by
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
      exact hq) h
    have h3 := le_max_right (NumberField.discr F).natAbs (Ideal.absNorm q)
    omega
  exact ⟨rationalPrincipalIdeal_squarefree F hp hdiscr,
    rationalPrincipalIdeal_sup_eq_top F hp q hq havoid⟩

end DedekindZetaZeroFree.LargeSieve.Sieve
