module

public import DedekindZetaZeroFree.Eisenstein.Induction.TorusEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusCovariance
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 theorem rpow_factor (x : ℝ) (hx : 0 < x) :
    (Real.rpow x (1/2 : ℝ) : ℂ) * (Real.rpow x (1/6 : ℝ) : ℂ) =
      (Real.rpow x (2/3 : ℝ) : ℂ) := by
  simp only [Real.rpow_eq_pow]
  rw [← Complex.ofReal_mul, ← Real.rpow_add hx]
  norm_num

 theorem localNorm_pos (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (v : KPHilbert.Place F) :
    0 < TorusNorms.localNorm F ζ hζ P C t a d v := by
  cases v with
  | inr q => exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) _
  | inl w => exact pow_pos (norm_pos_iff.mpr (div_ne_zero (a w).ne_zero (d w).ne_zero)) 2

















 theorem multiplier (u : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    (∏ w, (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d (Sum.inl w)) (2/3 : ℝ) : ℂ)) *
      ∏ᶠ q, (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d (Sum.inr q)) (2/3 : ℝ) : ℂ) =
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) := by
  obtain ⟨hs, hn⟩ := TorusNorms.given_raw_norm F ζ hζ P C u t a d b e ht hp he
  have hroot : Function.HasFiniteMulSupport (fun v =>
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (1/6 : ℝ) : ℂ)) :=
    hs.comp (g := fun x : ℝ => (Real.rpow x (1/6 : ℝ) : ℂ)) (by norm_num)
  have hweight : Function.HasFiniteMulSupport (fun v =>
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (2/3 : ℝ) : ℂ)) :=
    hs.comp (g := fun x : ℝ => (Real.rpow x (2/3 : ℝ) : ℂ)) (by norm_num)
  rw [← RawSource.finprod_places F hweight]
  have hw (v : KPHilbert.Place F) :
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (2/3 : ℝ) : ℂ) =
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (1/6 : ℝ) : ℂ) ^ (4 : ℕ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (le_of_lt (localNorm_pos F ζ hζ P C t a d v))]
    norm_num
  simp_rw [hw]
  rw [← finprod_pow hroot 4]
  have hnC : ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) =
      ∏ᶠ v, (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (1/6 : ℝ) : ℂ) := by
    rw [show ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) =
      ((((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℝ)) : ℂ) from rfl, hn]
    exact MonoidHom.map_finprod Complex.ofRealHom.toMonoidHom
      (hs.comp (g := fun x : ℝ => Real.rpow x (1/6 : ℝ)) (by norm_num))
  rw [← hnC]
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ e =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) ^ (3 : ℕ) := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    rw [Real.sqrt_eq_rpow]
    have hν : (((KPGlobalTorusFunctionData.delta F ζ hζ e : ℝ≥0) : ℝ)) =
        (((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℝ)) ^ (6 : ℕ) := by
      simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
        KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map,
        NNReal.rpowMonoidHom_apply, NNReal.coe_rpow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hν, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hhalf]
  ring










































































end DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusCovariance

end
