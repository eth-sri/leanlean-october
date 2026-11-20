module

public import DedekindZetaZeroFree.Arithmetic.Kummer.SexticFrequencyCharacters
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.MaskedHeckeMeromorphic
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors FrequencyCharacterMasks

variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS}

inductive Row where
  | principal
  | plus
  | minus
  deriving DecidableEq

section

variable (U : Frequency C)

def primitive (P : PrimitiveInducers U) :
    Row → Detector.PrimitiveFrequencyCharacter F
  | .principal => Detector.FrequencyPrincipal.principalPrimitive (F := F)
  | .plus => P.plus
  | .minus => P.minus

def deletionSet : Row → Set (HeightOneSpectrum (𝓞 F))
  | .principal => (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
  | .plus => frequencyMask U
  | .minus => frequencyMask U

def coefficient : Row → Ideal (𝓞 F) → ℂ
  | .principal => principalCoefficient A
  | .plus => plusCoefficient U
  | .minus => minusCoefficient U

def incompleteL (i : Row) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 F), coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s)

end

def poleIndicator (ν : Detector.PrimitiveFrequencyCharacter F) : ℕ :=
  if ν.character.IsPrincipal then 1 else 0

section

variable (U : Frequency C) (P : PrimitiveInducers U) (i : Row)

def deletionProduct (s : ℂ) : ℂ :=
  Detector.finiteEulerDeletionMask F (deletionSet U i)
    (fun p => (primitive U P i).character p.asIdeal) s

def quotientRepresentative (J : ℂ → ℂ) (s : ℂ) : ℂ :=
  J s * deletionProduct U P i s / (s - 1) ^ poleIndicator (primitive U P i)

end

structure RowContinuation (U : Frequency C) (P : PrimitiveInducers U) (i : Row) where
  J : ℂ → ℂ
  J_holomorphic : AnalyticOnNhd ℂ J {s : ℂ | 0 < s.re}
  B_holomorphic : AnalyticOnNhd ℂ (deletionProduct U P i) {s : ℂ | 0 < s.re}
  regular_equality : ∀ s : ℂ, 1 < s.re →
    incompleteL U i s = quotientRepresentative U P i J s

private lemma positive_open : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma primitive_series_ne_zero (ν : Detector.PrimitiveFrequencyCharacter F)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' I : Ideal (𝓞 F), ν.character I * (Ideal.absNorm I : ℂ) ^ (-s)) ≠ 0 := by
  have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
      ν.character I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
    intro I hI
    refine ⟨?_, by simp⟩
    intro hzero
    exact hI (by simp [((ν.character.eq_zero_iff' I).mpr (Or.inl hzero))])
  rw [← (tsum_subtype_eq_of_support_subset hsupp)]
  change (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 F)),
    ν.character I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) ≠ 0
  simpa only [ExteriorIdealEuler.summand, ExteriorIdealEuler.zeroMaskedRayCoefficient,
    sup_top_eq, if_true] using ((ExteriorIdealEuler.exterior_ideal_euler _ (ExteriorIdealEuler.zeroMaskedRay_isCoefficient
      ν.conductor ν.conductor_ne_zero ν.character ⊤) s hs).2.2.1)

private lemma primitive_regularizer
    (hF : NumberField.IsTotallyComplex F) (ν : Detector.PrimitiveFrequencyCharacter F) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J {s : ℂ | 0 < s.re} ∧
      (∃ s : ℂ, 0 < s.re ∧ J s ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → HasSum
        (fun I : Ideal (𝓞 F) => ν.character I * (Ideal.absNorm I : ℂ) ^ (-s))
        (J s / (s - 1) ^ poleIndicator ν) := by
  by_cases hp : ν.character.IsPrincipal
  · let H := principalRayHeckeData F hF ν.conductor ν.conductor_ne_zero
      ν.character ν.primitive hp
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    have hne : (2 : ℂ) ≠ 1 := by norm_num
    have hR : H.R 2 ≠ 0 := by
      rw [H.regularized 2 (by norm_num) hne]
      exact mul_ne_zero (sub_ne_zero.mpr hne)
        (by rw [← (H.series 2 h2).tsum_eq]; exact primitive_series_ne_zero ν 2 h2)
    refine ⟨H.R, H.R_holo.analyticOnNhd positive_open, ⟨2, by norm_num, hR⟩, ?_⟩
    intro s hs
    have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hs
    have he : H.R s / (s - 1) ^ poleIndicator ν = H.L s := by
      rw [poleIndicator, if_pos hp, pow_one, H.regularized s (lt_trans (by norm_num) hs) hs1]
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)
    rw [he]
    exact H.series s hs
  · let H := nonprincipalRayHeckeData F hF ν.conductor ν.conductor_ne_zero
      ν.character ν.primitive hp
    refine ⟨H.L, H.L_holo.analyticOnNhd positive_open, ⟨2, by norm_num, ?_⟩, ?_⟩
    · rw [← (H.series 2 (by norm_num)).tsum_eq]
      exact primitive_series_ne_zero ν 2 (by norm_num)
    · intro s hs
      simpa [poleIndicator, hp] using H.series s hs

private lemma row_deletion_finite (U : Frequency C) (i : Row) :
    (deletionSet U i).Finite := by
  have hf : (frequencyMask U).Finite := by
    rw [frequencyMask_eq_principal_support]
    exact A.Sf.finite_toSet.union
      (Detector.exterior_frequency_support_finite_norm_pos F _ A.Sf.finite_toSet
        U.u U.generates.1).1
  cases i
  · exact A.Sf.finite_toSet
  · exact hf
  · exact hf

private lemma row_coefficient_eq (U : Frequency C) (P : PrimitiveInducers U) (i : Row) :
    coefficient U i = Detector.deletedPrimitiveIdealCoefficient F
      (primitive U P i) (deletionSet U i) := by
  funext I
  cases i
  · exact (principal_mask_exactly_S A) I
  · exact P.plus_mask I
  · exact P.minus_mask I

theorem masked_hecke_meromorphic
     (U : Frequency C) :
    ∃ P : PrimitiveInducers U, ∀ i : Row, Nonempty (RowContinuation U P i) := by
  obtain ⟨P⟩ := primitiveInducers_exists U
  refine ⟨P, fun i => ?_⟩
  let ν := primitive U P i
  have hD := row_deletion_finite U i
  obtain ⟨J, hJ, hJne, hseries⟩ := primitive_regularizer
    (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12) ν
  have hm : MeromorphicOn (fun s : ℂ => J s / (s - 1) ^ poleIndicator ν)
      {s : ℂ | 0 < s.re} := by
    exact hJ.meromorphicOn.div
      ((analyticOnNhd_id.sub analyticOnNhd_const).pow (poleIndicator ν)).meromorphicOn
  obtain ⟨hBdiff, hBmero, hBs⟩ := Detector.deleted_primitive_L_continuation F ν
    (deletionSet U i) hD {s : ℂ | 0 < s.re}
    (fun s : ℂ => J s / (s - 1) ^ poleIndicator ν) hm hseries
  have hB : AnalyticOnNhd ℂ (deletionProduct U P i) {s : ℂ | 0 < s.re} :=
    hBdiff.differentiableOn.analyticOnNhd positive_open
  have hregular : ∀ s : ℂ, 1 < s.re → HasSum
      (fun I : Ideal (𝓞 F) => coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s))
      (quotientRepresentative U P i J s) := by
    intro s hs
    rw [row_coefficient_eq U P i]
    simpa only [quotientRepresentative, deletionProduct, ν, div_mul_eq_mul_div]
      using hBs s hs
  refine ⟨{
    J := J
    J_holomorphic := hJ
    B_holomorphic := hB
    regular_equality := fun s hs => (hregular s hs).tsum_eq
  }⟩

end DedekindZetaZeroFree.MaskedHeckeMeromorphic

end
