module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
public import GaloisCohomology.Topology.TotallyDisconnectedQuotients

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The identity component of the idele class group

This module packages the connected component of the identity in the idele
class group as a closed normal subgroup and names the corresponding quotient.
-/

open scoped NNReal NumberField Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The connected component of the identity in the idele class group. -/
def ideleClassIdentityComponent : Subgroup (IdeleClassGroup K) :=
  Subgroup.connectedComponentOfOne (IdeleClassGroup K)

@[simp]
theorem coe_ideleClassIdentityComponent :
    (ideleClassIdentityComponent K : Set (IdeleClassGroup K)) =
      connectedComponent (1 : IdeleClassGroup K) :=
  rfl

instance ideleClassIdentityComponent_normal :
    (ideleClassIdentityComponent K).Normal := by
  change (Subgroup.connectedComponentOfOne (IdeleClassGroup K)).Normal
  exact
    QuotientGroup.Subgroup.Normal.connectedComponentOfOne
      (IdeleClassGroup K)

/-- The positive archimedean norm section, passed to the idele class group. -/
def ideleClassPositiveArchimedeanSection :
    ℝ≥0ˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)).comp
    (IdeleGroup.positiveArchimedeanSection K)

/-- The positive archimedean section of the idele class group, with its
natural continuity. -/
def ideleClassPositiveArchimedeanSectionContinuous :
    ℝ≥0ˣ →ₜ* IdeleClassGroup K where
  __ := ideleClassPositiveArchimedeanSection K
  continuous_toFun :=
    QuotientGroup.continuous_mk.comp
      (IdeleGroup.positiveArchimedeanSectionContinuous K).continuous_toFun

@[simp]
theorem ideleClassPositiveArchimedeanSectionContinuous_apply
    (r : ℝ≥0ˣ) :
    ideleClassPositiveArchimedeanSectionContinuous K r =
      ideleClassPositiveArchimedeanSection K r :=
  rfl

@[simp]
theorem ideleClassPositiveArchimedeanSection_absoluteNorm
    (r : ℝ≥0ˣ) :
    IdeleClassGroup.absoluteNorm
        (ideleClassPositiveArchimedeanSection K r) =
      r⁻¹ := by
  rw [ideleClassPositiveArchimedeanSection, MonoidHom.comp_apply,
    IdeleClassGroup.absoluteNorm_mk,
    IdeleGroup.positiveArchimedeanSection_absoluteNorm]

/-- The norm-one factor of an idele-class representative after removing its
positive archimedean norm component. -/
def ideleClassNormOneCorrection
    (a : IdeleGroup K) :
    IdeleClassGroup.normOneSubgroup (K := K) :=
  let correction : IdeleGroup.normOneSubgroup (K := K) :=
    IdeleGroup.positiveArchimedeanNormOneCorrection K a
  ⟨QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (correction : IdeleGroup K),
    (IdeleClassGroup.mk_mem_normOneSubgroup_iff
      (K := K) (correction : IdeleGroup K)).2 correction.property⟩

@[simp]
theorem coe_ideleClassNormOneCorrection (a : IdeleGroup K) :
    (ideleClassNormOneCorrection K a : IdeleClassGroup K) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
        (IdeleGroup.positiveArchimedeanNormOneCorrection K a) :=
  rfl

/-- Every idele class is the product of a norm-one class and the inverse of
its positive archimedean norm section. -/
theorem ideleClass_mk_eq_normOneCorrection_mul_positiveSection_inv
    (a : IdeleGroup K) :
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a =
      (ideleClassNormOneCorrection K a : IdeleClassGroup K) *
        (ideleClassPositiveArchimedeanSection K
          (IdeleGroup.absoluteNorm a))⁻¹ := by
  rw [coe_ideleClassNormOneCorrection,
    ideleClassPositiveArchimedeanSection, MonoidHom.comp_apply]
  simp
