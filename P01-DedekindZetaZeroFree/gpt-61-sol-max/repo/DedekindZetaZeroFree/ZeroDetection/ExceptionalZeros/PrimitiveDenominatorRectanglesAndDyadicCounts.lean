module

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.BlockEnergyCounts
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.ZeroFreeDiskReciprocalBounds
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.TwistedDeletedCoefficientInduction

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem freqOrbit_injective (R : PrincipalMellin.ActualRecipe S η) :
    Function.Injective (fun u : Frequency R =>
      ProbeOrbitNormSum.orbitMk R.A u.val) := by
  intro u v huv
  have h := Quotient.exact huv
  obtain ⟨γ, heq⟩ := MulAction.orbitRel_apply.mp h
  obtain ⟨δ, hδ⟩ := γ.property
  let I : R.A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  let r := R.probe.coefficients.generator I
  have hr := (R.probe.coefficients.generates I).1
  let m : ThetaReflectionData.Row R.A :=
    ⟨u.val.val * r ^ 6, mul_ne_zero u.val.property (pow_ne_zero _ hr)⟩
  obtain ⟨x, hx, hxuniq⟩ := R.probe.frequencies.factorization m
  have hg : R.probe.allowed.generator I = ThetaReflectionData.rowUnit R.A ⟨r, hr⟩ := by
    apply Units.ext
    exact R.probe.sameGenerator I
  have hu : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A m =
      ThetaReflectionData.rowUnit R.A u.val * R.probe.allowed.generator I ^ 6 *
        γ.val ^ 6 := by
    refine ⟨1, ?_⟩
    rw [hg]
    apply Units.ext
    simp [m, r, ThetaReflectionData.rowUnit]
  have hv : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A m =
      ThetaReflectionData.rowUnit R.A v.val * R.probe.allowed.generator I ^ 6 *
        γ.val ^ 6 := by
    refine ⟨δ, ?_⟩
    rw [hg]
    have huu := congrArg (fun x : ThetaReflectionData.Row R.A => (x.val : F)) heq
    have hδF := congrArg (fun x : R.A.U => (x.val : F)) hδ
    apply Units.ext
    simp only [m, ThetaReflectionData.rowUnit, Units.val_mk0, map_mul, map_pow]
    change (u.val.val : F) * (r : F) ^ 6 = (v.val.val : F) * (r : F) ^ 6 * (δ.val : F) ^ 6
    change ((R.A.unitEquiv γ.val : R.A.R) : F) * (v.val.val : F) = (u.val.val : F) at huu
    have hcoe : ((R.A.unitEquiv γ.val : R.A.R) : F) = (γ.val.val : F) := by
      simp [SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
    rw [hcoe, ← hδF] at huu
    change (δ.val : F) ^ 6 * (v.val.val : F) = (u.val.val : F) at huu
    rw [← huu]
    ring
  have he : (u, I) = (v, I) := (hxuniq _ hu).trans (hxuniq _ hv).symm
  exact congrArg Prod.fst he

private lemma freqOrbit_norm (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) :
    frequencyNorm R u =
      ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) := by
  unfold frequencyNorm FiniteTransform.exteriorNorm ProbeOrbitNormSum.orbitNorm
  rw [ProbeOrbitNormSum.orbitIdeal_mk]
  change (Nat.card (R.A.R ⧸ Ideal.span {u.val.val}) : ℝ) =
    R.A.exteriorNorm (ProbeOrbitNormSum.principalExterior R.A u.val)
  rw [(ProbeOrbitNormSum.principalExterior_generates R.A u.val).2, R.A.exteriorResidue_card]
  rfl

private lemma one_le_frequencyNorm (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) : 1 ≤ frequencyNorm R u := by
  rw [freqOrbit_norm R u]
  exact idealNorm_ge_one _
    (ProbeOrbitNormSum.orbitIdeal R.A (ProbeOrbitNormSum.orbitMk R.A u.val)).property.1

private lemma freq_count_linear (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency R | frequencyNorm R u ≤ X}.Finite ∧
      (Set.ncard {u : Frequency R | frequencyNorm R u ≤ X} : ℝ) ≤ K * X := by
  obtain ⟨C, hC0, hCcount⟩ := ProbeExteriorIdealCount.ideal_count_linear (F := F) R.A.cS
  refine ⟨(Nat.card R.A.UnitQuotient : ℝ) * C + 1, by positivity, ?_⟩
  intro X hX
  obtain ⟨hBfin, hBcard⟩ := hCcount X hX
  have hBfin' : {I : R.A.Exterior | R.A.exteriorNorm I ≤ X}.Finite := hBfin
  have hfiber : ∀ I : R.A.Exterior,
      {o : ProbeOrbitNormSum.Orbit R.A | ProbeOrbitNormSum.orbitIdeal R.A o = I}.Finite ∧
      Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
        ProbeOrbitNormSum.orbitIdeal R.A o = I} ≤ Nat.card R.A.UnitQuotient := by
    intro I
    refine ⟨ProbeOrbitNormSum.idealFiber_finite R.A I, ?_⟩
    rw [ProbeOrbitNormSum.idealFiber_card R.A R.classKilled I]
  obtain ⟨hprefin, hprecard⟩ := ProbeExteriorPrincipalIdealFibers.finite_preimage_card_bound
    (ProbeOrbitNormSum.orbitIdeal R.A) (Nat.card R.A.UnitQuotient) hfiber
    {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} hBfin'
  have ht : {o : ProbeOrbitNormSum.Orbit R.A |
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X}.Finite := hprefin
  have hprecard' : Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X} ≤
      Nat.card R.A.UnitQuotient * Set.ncard {I : R.A.Exterior |
        R.A.exteriorNorm I ≤ X} := hprecard
  have hpfin : ((fun u : Frequency R => ProbeOrbitNormSum.orbitMk R.A u.val) ⁻¹'
      {o : ProbeOrbitNormSum.Orbit R.A | ProbeOrbitNormSum.orbitNorm R.A o ≤ X}).Finite :=
    ht.preimage (fun a _ b _ hab => freqOrbit_injective R hab)
  have hfin : {u : Frequency R | frequencyNorm R u ≤ X}.Finite := by
    refine hpfin.subset ?_
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    show ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) ≤ X
    rw [← freqOrbit_norm R u]
    exact hu
  refine ⟨hfin, ?_⟩
  have hinj := Set.ncard_le_ncard_of_injOn
    (fun u : Frequency R => ProbeOrbitNormSum.orbitMk R.A u.val)
    (fun u hu => by
      show ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) ≤ X
      rw [← freqOrbit_norm R u]
      exact hu)
    (fun a _ b _ h => freqOrbit_injective R h) ht
  have hnat : Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X} =
      Set.ncard {o : ProbeOrbitNormSum.Orbit R.A |
        ProbeOrbitNormSum.orbitNorm R.A o ≤ X} := Nat.card_coe_set_eq _
  have hBcard' : (Set.ncard {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} : ℝ) ≤ C * X := by
    rw [← Nat.card_coe_set_eq]
    exact hBcard
  rw [hnat] at hprecard'
  calc
    (Set.ncard {u : Frequency R | frequencyNorm R u ≤ X} : ℝ)
        ≤ (Set.ncard {o : ProbeOrbitNormSum.Orbit R.A |
            ProbeOrbitNormSum.orbitNorm R.A o ≤ X} : ℝ) := by
          exact_mod_cast hinj
    _ ≤ (Nat.card R.A.UnitQuotient : ℝ) *
          (Set.ncard {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} : ℝ) := by
          exact_mod_cast hprecard'
    _ ≤ (Nat.card R.A.UnitQuotient : ℝ) * (C * X) :=
          mul_le_mul_of_nonneg_left hBcard' (Nat.cast_nonneg _)
    _ ≤ ((Nat.card R.A.UnitQuotient : ℝ) * C + 1) * X := by
          nlinarith [hC0, Nat.cast_nonneg (α := ℝ) (Nat.card R.A.UnitQuotient), hX]

theorem actual_complete_frequency_dyads
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (K : ℝ) (D : ℕ → Finset (Frequency R)),
      0 < K ∧
      (∀ j : ℕ, comparisonFrequencyDyad (frequencyNorm R) (principalFrequency R) K
        ((2 : ℝ) ^ j) (D j)) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R → ∃ j : ℕ, u ∈ D j) := by
  obtain ⟨K₀, hK₀, hcount⟩ := freq_count_linear R
  have hpow : ∀ j : ℕ, 1 ≤ (2 : ℝ) ^ (j + 1) := fun j => one_le_pow₀ (by norm_num)
  have hfin : ∀ j : ℕ, {u : Frequency R | frequencyNorm R u < (2 : ℝ) ^ (j + 1)}.Finite :=
    fun j => ((hcount _ (hpow j)).1).subset (fun _ hu => le_of_lt (Set.mem_setOf_eq.mp hu))
  let D : ℕ → Finset (Frequency R) := fun j =>
    (hfin j).toFinset.filter
      (fun u => u ≠ principalFrequency R ∧ (2 : ℝ) ^ j ≤ frequencyNorm R u)
  have hmem : ∀ (j : ℕ) (u : Frequency R), u ∈ D j ↔
      frequencyNorm R u < (2 : ℝ) ^ (j + 1) ∧ u ≠ principalFrequency R ∧
        (2 : ℝ) ^ j ≤ frequencyNorm R u := by
    intro j u
    simp only [D, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hDcard : ∀ j : ℕ, ((D j).card : ℝ) ≤ (2 * K₀) * (2 : ℝ) ^ j := by
    intro j
    have hpow_eq : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
    have hcard_le : (D j).card ≤ (hfin j).toFinset.card := Finset.card_filter_le _ _
    have hto : ((hfin j).toFinset.card : ℝ) =
        (Set.ncard {u : Frequency R | frequencyNorm R u < (2 : ℝ) ^ (j + 1)} : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ (hfin j)]
    have hsub : {u : Frequency R | frequencyNorm R u < (2 : ℝ) ^ (j + 1)} ⊆
        {u : Frequency R | frequencyNorm R u ≤ (2 : ℝ) ^ (j + 1)} :=
      fun _ hu => le_of_lt (Set.mem_setOf_eq.mp hu)
    have hle : (Set.ncard {u : Frequency R |
        frequencyNorm R u < (2 : ℝ) ^ (j + 1)} : ℝ) ≤ K₀ * (2 : ℝ) ^ (j + 1) :=
      (Nat.cast_le.mpr (Set.ncard_le_ncard hsub (hcount _ (hpow j)).1)).trans
        (hcount _ (hpow j)).2
    calc ((D j).card : ℝ) ≤ ((hfin j).toFinset.card : ℝ) := by exact_mod_cast hcard_le
      _ = (Set.ncard {u : Frequency R |
            frequencyNorm R u < (2 : ℝ) ^ (j + 1)} : ℝ) := hto
      _ ≤ K₀ * (2 : ℝ) ^ (j + 1) := hle
      _ = (2 * K₀) * (2 : ℝ) ^ j := by rw [hpow_eq]; ring
  refine ⟨2 * K₀, D, by positivity, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · intro u hu
      have hu' := (hmem j u).mp hu
      refine ⟨hu'.2.1, hu'.2.2, ?_⟩
      have hpow_eq : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
      rw [← hpow_eq]
      exact hu'.1
    · exact hDcard j
  · intro u hu
    have hq1 : 1 ≤ frequencyNorm R u := one_le_frequencyNorm R u
    have hex : ∃ n : ℕ, frequencyNorm R u < (2 : ℝ) ^ n :=
      ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually
        (Filter.eventually_gt_atTop (frequencyNorm R u))).exists
    let n := Nat.find hex
    have hn : frequencyNorm R u < (2 : ℝ) ^ n := Nat.find_spec hex
    have hnmin : ∀ m < n, ¬ frequencyNorm R u < (2 : ℝ) ^ m :=
      fun m hm => Nat.find_min hex hm
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hn
        simp only [pow_zero] at hn
        linarith
      · exact h
    have hle : (2 : ℝ) ^ (n - 1) ≤ frequencyNorm R u := by
      exact not_lt.mp (hnmin (n - 1) (Nat.sub_lt hnpos (by norm_num)))
    refine ⟨n - 1, (hmem (n - 1) u).mpr ⟨?_, hu, hle⟩⟩
    rw [Nat.sub_add_cancel hnpos]
    exact hn

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle

end

section
namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary

end

section
namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary
open scoped Classical

end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} 

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
