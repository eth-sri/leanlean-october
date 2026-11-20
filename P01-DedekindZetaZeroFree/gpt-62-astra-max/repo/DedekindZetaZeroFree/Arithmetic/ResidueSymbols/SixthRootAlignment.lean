module

public import DedekindZetaZeroFree.Moments.Reflected.DyadicMomentSource
public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalCoverAlgebra

@[expose] public section

noncomputable section
open scoped NumberField Classical
open Polynomial NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.MomentSources
variable {F : Type} [Field F] [NumberField F]

theorem aligned_embedding_exists (S : SArithmeticData F) :
    ∃ σ : F →+* ℂ, ∀ z : rootsOfUnity 6 F,
      σ ((z : Fˣ) : F) =
        (KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 z : ℂ) := by
  let w := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12)
  have hw2 : w ^ 2 = (KPLocalCover.complexSixthGenerator : ℂ) := by
    calc _
        = Complex.exp ((2:ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 12)) := by
          rw [Complex.exp_nat_mul]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6) := by congr 1; ring
  have hroot : aeval w (minpoly ℚ S.zeta12) = 0 := by
    rw [((cyclotomic_eq_minpoly_rat S.primitive_zeta12 (by norm_num)).symm), aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact (Complex.isPrimitiveRoot_exp 12 (by norm_num))
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_adjoin_splits_of_aeval

    (fun s _ => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    (IntermediateField.adjoin_univ ℚ F) hroot
  refine ⟨φ.toRingHom, fun z => ?_⟩
  have hz : (S.zeta12 ^ 2) ^ KPLocalCover.sixthExponent F S.zeta12 S.primitive_zeta12 z =
      ((z : Fˣ) : F) :=
    (Classical.choose_spec (KPLocalCover.exists_sixthExponent F S.zeta12 S.primitive_zeta12 z)).2
  have hval : φ.toRingHom ((z : Fˣ) : F) =
      (KPLocalCover.complexSixthGenerator : ℂ) ^
        KPLocalCover.sixthExponent F S.zeta12 S.primitive_zeta12 z := by
    rw [← hz, map_pow]
    have : φ.toRingHom (S.zeta12 ^ 2) = (KPLocalCover.complexSixthGenerator : ℂ) := by
      rw [map_pow, show φ.toRingHom S.zeta12 = w from hφ, hw2]
    rw [this]
  have hcoe : (KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 z : ℂ) =
      (KPLocalCover.complexSixthGenerator : ℂ) ^
        KPLocalCover.sixthExponent F S.zeta12 S.primitive_zeta12 z := by
    show ((KPLocalCover.complexSixthGenerator ^
      KPLocalCover.sixthExponent F S.zeta12 S.primitive_zeta12 z : ℂˣ) : ℂ) = _
    rw [Units.val_pow_eq_pow_val]
  rw [hval, hcoe]

theorem aligned_recipe_exists
     (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η,
      ∀ z : rootsOfUnity 6 F, R.σ ((z : Fˣ) : F) =
        (KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 z : ℂ) := by
  obtain ⟨σ, hσ⟩ := aligned_embedding_exists S
  obtain ⟨A, hsub, hroot, hmod, hS, hdiff, C, hprincipal⟩ :=
    PrincipalProbeConstruction.exists_enlarged_principal_context S σ η hη
  have hηA : (hmod.symm ▸ η).IsPrincipal := by
    generalize hm : S.modulus = m at η hη hmod ⊢
    cases hmod
    exact hη
  obtain ⟨probe, _, _, N, _, _⟩ :=
    PrincipalProbeConstruction.exists_shared_principal_probe A σ (hmod.symm ▸ η) hS C
      hηA hprincipal hdiff
  have transport : ∀ (m n : Ideal (𝓞 F)) (e : m = n)
      (χ : RayClassCharacter F n), PrincipalRayHeckeData F n χ →
        PrincipalRayHeckeData F m (e.symm ▸ χ) := by
    intro m n e
    subst n
    exact fun _ p => p
  exact ⟨{
    A := A
    containsOriginal := hsub
    sameModulus := hmod
    sameRoot := hroot
    classKilled := C.classGroup_trivial
    σ := σ
    traceBad := hS
    probe := probe
    normalization := N
    continuation := transport _ _ hmod η P }, hσ⟩

def RootAligned {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) : Prop :=
  ∀ z : rootsOfUnity 6 F, R.σ ((z : Fˣ) : F) =
    (KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 z : ℂ)

namespace Characters
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

section

variable (p : ThetaBranch.ExteriorPrime R.A)

def psi : AddChar (DHCubic.Residue F p.val) ℂ :=
  (PrincipalMellinSource.exists_primitive_source_characters R).choose p

theorem primitive : (psi R p).IsPrimitive :=
  (PrincipalMellinSource.exists_primitive_source_characters R).choose_spec.1 p

theorem psi_apply (t : 𝓞 F) :
    psi R p (Ideal.Quotient.mk p.val.asIdeal t) = R.probe.coefficients.additiveCharacter
      ((t : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) :=
  (PrincipalMellinSource.exists_primitive_source_characters R).choose_spec.2 p t

end

def L : R.A.UnitQuotient → Fˣ →* ℂ :=
  (PrincipalMellinSource.exists_rational_source_characters R).choose

theorem norm_one (v : R.A.UnitQuotient) (x : Fˣ) : ‖L R v x‖ = 1 :=
  (PrincipalMellinSource.exists_rational_source_characters R).choose_spec.1 v x

theorem compatible : PrincipalMellinSource.SourceCharacterCompatibility R (psi R) (L R) :=
  ⟨psi_apply R, (PrincipalMellinSource.exists_rational_source_characters R).choose_spec.2⟩
end Characters
end DedekindZetaZeroFree.MomentSources

end
