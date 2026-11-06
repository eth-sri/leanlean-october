module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorBoundsAndDampedTails
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.Detector

noncomputable def idealMoebius (F : Type) [Field F] [NumberField F]
    (d : Ideal (𝓞 F)) : ℤ :=
  UniqueFactorizationMonoid.moebius d

noncomputable def truncatedIdealMoebius (F : Type) [Field F] [NumberField F]
    (U : ℝ) (n : Ideal (𝓞 F)) : ℝ := by
  classical
  exact ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ) then
      (idealMoebius F d : ℝ) else 0

noncomputable def idealLSeries (F : Type) [Field F] [NumberField F]
    {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (s : ℂ) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ then ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0

theorem truncatedIdealMoebius_top (F : Type) [Field F] [NumberField F]
    (U : ℝ) (hU : 2 ≤ U) : truncatedIdealMoebius F U ⊤ = 1 := by
  classical
  unfold truncatedIdealMoebius
  rw [finsum_eq_single _ ⊤]
  · have h : (1 : ℝ) ≤ U ^ 2 := by nlinarith
    have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
    simp only [ne_eq, htop, not_false_eq_true, dvd_refl, Ideal.absNorm_top,
      Nat.cast_one, h, and_self, if_true]
    norm_cast
    simpa only [idealMoebius, Ideal.one_eq_top] using
      UniqueFactorizationMonoid.moebius_one (α := Ideal (𝓞 F))
  · intro d hd
    have hnot : ¬d ∣ (⊤ : Ideal (𝓞 F)) := by
      simpa [Ideal.dvd_iff_le] using hd
    simp [hnot]

open UniqueFactorizationMonoid

theorem squarefree_prod_subset (F : Type) [Field F] [NumberField F]
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) (t : Finset (Ideal (𝓞 F)))
    (ht : t ⊆ (normalizedFactors n).toFinset) :
    (∏ p ∈ t, p) ≠ ⊥ ∧ (∏ p ∈ t, p) ∣ n ∧ Squarefree (∏ p ∈ t, p) ∧
      idealMoebius F (∏ p ∈ t, p) = (-1) ^ t.card := by
  have hp : ∀ p ∈ t, Prime p := by
    intro p hp
    exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp (ht hp))
  have hprod : (∏ p ∈ t, p) ≠ (0 : Ideal (𝓞 F)) :=
    Finset.prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  have hfactor : normalizedFactors (∏ p ∈ t, p) = t.val := by
    simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using normalizedFactors_prod_of_prime hp
  have hsq : Squarefree (∏ p ∈ t, p) := by
    rw [squarefree_iff_nodup_normalizedFactors hprod, hfactor]
    exact t.nodup
  refine ⟨hprod, ?_, hsq, ?_⟩
  · rw [dvd_iff_normalizedFactors_le_normalizedFactors hprod hn, hfactor]
    apply (Multiset.le_iff_subset t.nodup).mpr
    intro p hp
    exact Multiset.mem_toFinset.mp (ht hp)
  · rw [idealMoebius, hsq.moebius_eq, factors_eq_normalizedFactors, hfactor]
    rfl
theorem mobius_sum_zero (F : Type) [Field F] [NumberField F]
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) (hnt : n ≠ ⊤) :
    (∑ d ∈ (ideal_divisors_finite F n hn).toFinset, (idealMoebius F d : ℝ)) = 0 := by
  classical
  let D := (ideal_divisors_finite F n hn).toFinset
  let P := (normalizedFactors n).toFinset
  have hD (d : Ideal (𝓞 F)) : d ∈ D ↔ d ≠ ⊥ ∧ d ∣ n := Set.Finite.mem_toFinset _
  have hsum : (∑ d ∈ D, (idealMoebius F d : ℝ)) =
      ∑ d ∈ D.filter Squarefree, (idealMoebius F d : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hd'
    have : ¬ Squarefree d := by simpa [hd] using hd'
    simp [idealMoebius, UniqueFactorizationMonoid.moebius_of_not_squarefree this]
  rw [hsum]
  have hbij : (∑ d ∈ D.filter Squarefree, (idealMoebius F d : ℝ)) =
      ∑ t ∈ P.powerset, (-1 : ℝ) ^ t.card := by
    symm
    apply Finset.sum_bij (fun t _ => ∏ p ∈ t, p)
    · intro t ht
      have h := squarefree_prod_subset F n hn t (Finset.mem_powerset.mp ht)
      simp_all
    · intro t ht u hu heq
      have htf : normalizedFactors (∏ p ∈ t, p) = t.val := by
        simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
          normalizedFactors_prod_of_prime (fun p hp => prime_of_normalized_factor p
            (Multiset.mem_toFinset.mp (Finset.mem_powerset.mp ht hp)))
      have huf : normalizedFactors (∏ p ∈ u, p) = u.val := by
        simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
          normalizedFactors_prod_of_prime (fun p hp => prime_of_normalized_factor p
            (Multiset.mem_toFinset.mp (Finset.mem_powerset.mp hu hp)))
      simp_all
    · intro d hd
      obtain ⟨hdD, hsq⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd0, hdn⟩ := (hD d).mp hdD
      refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
      · apply Finset.mem_powerset.mpr
        intro p hp
        apply Multiset.mem_toFinset.mpr
        exact Multiset.mem_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn).mp hdn)
          (Multiset.mem_toFinset.mp hp)
      · simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hd0).mp hsq)] using
          associated_iff_eq.mp (prod_normalizedFactors hd0)
    · intro t ht
      rw [(squarefree_prod_subset F n hn t (Finset.mem_powerset.mp ht)).2.2.2]
      simp
  rw [hbij]
  have hP : P.Nonempty := by
    by_contra h
    have hnf : normalizedFactors n = 0 := by
      simpa only [P, Finset.not_nonempty_iff_eq_empty, Multiset.toFinset_eq_empty] using h
    have hunit := (normalizedFactors_eq_zero_iff hn).mp hnf
    exact hnt (Ideal.isUnit_iff.mp hunit)
  have := Finset.prod_add_one (R := ℝ) (f := fun _ : Ideal (𝓞 F) => -1) P
  simpa [Finset.prod_const, zero_pow hP.card_ne_zero] using this.symm

theorem truncatedIdealMoebius_eq_zero (F : Type) [Field F] [NumberField F]
    (U : ℝ) (hU : 2 ≤ U) (n : Ideal (𝓞 F))
    (hn : n ≠ ⊥) (hNorm : 1 < (Ideal.absNorm n : ℝ))
    (hCutoff : (Ideal.absNorm n : ℝ) ≤ U ^ (2 : ℕ)) :
    truncatedIdealMoebius F U n = 0 := by
  classical
  have hnt : n ≠ ⊤ := by
    intro h
    simp [h] at hNorm
  let D := (ideal_divisors_finite F n hn).toFinset
  have hD (d : Ideal (𝓞 F)) : d ∈ D ↔ d ≠ ⊥ ∧ d ∣ n := Set.Finite.mem_toFinset _
  have hcut (d : Ideal (𝓞 F)) (hd : d ∈ D) : (Ideal.absNorm d : ℝ) ≤ U ^ 2 := by
    have hdiv := (hD d).mp hd
    have hle : Ideal.absNorm d ≤ Ideal.absNorm n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hn))
        (map_dvd Ideal.absNorm hdiv.2)
    exact (Nat.cast_le.mpr hle).trans hCutoff
  unfold truncatedIdealMoebius
  rw [finsum_eq_sum_of_support_subset _ (s := D)]
  · have heq : (∑ d ∈ D, if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ 2 then
      (idealMoebius F d : ℝ) else 0) = ∑ d ∈ D, (idealMoebius F d : ℝ) := by
      apply Finset.sum_congr rfl
      simp_all
    rw [heq]
    exact mobius_sum_zero F n hn hnt
  · intro d hd
    apply (hD d).mpr
    by_contra hd'
    simp only [Function.mem_support] at hd
    simp_all

theorem idealLSeries_summable (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ω : RayClassCharacter F m)
    (hω : ω.IsPrimitive) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0) := by
  classical
  have h := (heckeDirichlet_right_edge F s.re hs m hm ω s le_rfl).1
  exact h.congr fun n => by
    by_cases hn : n ≠ ⊥
    · simp [hn]
    · have hz : ω n = 0 := (ω.eq_zero_iff' n).mpr (Or.inl (not_ne_iff.mp hn))
      simp [hn, hz]
