module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.GoodPrimeEstimates
public import DedekindZetaZeroFree.Moments.Principal.Corrections.BadPrimeEstimates
public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeNormSummability

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem exterior_not_mem (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have he := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
  simp only [sup_idem] at he
  exact p.val.isPrime.ne_top he

theorem exterior_norm_majorant_summable (M a : ℝ) (ha : 1 < a) :
    Summable (fun p : ExteriorPrime A => M * (Q p) ^ (-a)) := by
  let i : ExteriorPrime A → {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} :=
    fun p => ⟨p.val, exterior_not_mem p⟩
  have hi : Function.Injective i := fun _ _ h =>
    Subtype.ext (congrArg (fun q : {q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // q ∉ A.Sf} => q.val) h)
  have hs := (summable_exterior_prime_norm_rpow F A.Sf a ha).comp_injective hi
  simpa only [Function.comp_def, i, Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
    using hs.mul_left M


theorem hasProdUniformlyOn_localFactor
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (K : Set Coordinates) (hK : IsCompact K) (hKO : K ⊆ Omega) :
    HasProdUniformlyOn
      (fun (p : ExteriorPrime A) (x : Coordinates) =>
        localFactor C U p x.1 x.2.1 x.2.2)
      (fun x : Coordinates =>
        ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) K := by
  obtain ⟨M, hM, hbound⟩ := good_correction_uniform_bound
  have hgood : ∀ᶠ p : ExteriorPrime A in Filter.cofinite, (U.j p).val = 0 :=
    U.toRaw.eventually_j_eq_zero
  have hb : ∀ᶠ p : ExteriorPrime A in Filter.cofinite, ∀ x ∈ K,
      ‖localFactor C U p x.1 x.2.1 x.2.2 - 1‖ ≤
        M * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) := by
    filter_upwards [hgood] with p hp
    intro x hx
    simpa [localFactor, hp] using
      hbound F A σ η hS C p U.u (U.toRaw.isUnit_of_j_eq_zero C p hp) x (hKO hx)
  have hcts : ∀ p : ExteriorPrime A,
      ContinuousOn (fun x : Coordinates => localFactor C U p x.1 x.2.1 x.2.2 - 1) K := by
    intro p
    have hc : ContinuousOn (fun x : Coordinates => localFactor C U p x.1 x.2.1 x.2.2) Omega := by
      by_cases hp : (U.j p).val = 0
      · simpa [localFactor, hp] using
          (good_correction_holomorphic C p U.u (U.toRaw.isUnit_of_j_eq_zero C p hp)).continuousOn
      · simpa [localFactor, hp] using
          (bad_factor_holomorphic C p (U.j p) hp (U.theta p)).continuousOn
    exact (hc.mono hKO).sub continuousOn_const
  simpa only [add_sub_cancel] using
    (exterior_norm_majorant_summable (A := A) M (1 + 1 / 4000) (by norm_num)).hasProdUniformlyOn_one_add hK hb hcts

theorem multipliable_localFactor
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (x : Coordinates) (hx : x ∈ Omega) :
    Multipliable (fun p : ExteriorPrime A =>
      localFactor C U p x.1 x.2.1 x.2.2) := by
  exact ((hasProdUniformlyOn_localFactor C U {x}
    isCompact_singleton (Set.singleton_subset_iff.mpr hx)).hasProd (Set.mem_singleton x)).multipliable

end DedekindZetaZeroFree.CorrectionFactors

end
