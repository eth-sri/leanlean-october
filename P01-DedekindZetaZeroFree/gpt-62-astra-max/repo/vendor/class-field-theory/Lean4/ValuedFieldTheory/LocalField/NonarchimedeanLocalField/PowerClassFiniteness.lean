module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Finiteness of local power-class groups

The multiplicative power-class group `Kˣ / Kˣⁿ` of a nonarchimedean local
field is finite whenever `n` is nonzero in `K`.  This is the finiteness input
for maximal Kummer extensions and the characteristic-zero local existence
theorem.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open LocalFieldTheory.DiscreteValuationField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The local power-class group is finite whenever the exponent is nonzero
in the field. -/
theorem finite_nthPowerQuotient_of_natCast_ne_zero
    (n : ℕ) (hnK : (n : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  have hn : n ≠ 0 := by
    intro hn
    apply hnK
    simp [hn]
  let : NeZero n := ⟨hn⟩
  let v := localIntegerValuation K
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation v
  rcases CharP.exists' K with hcharZero | ⟨p, hp, hcharP⟩
  · let := hcharZero
    let :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext v
    obtain ⟨a, e⟩ :=
      LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
        v (localIntegerValuation_surjective K)
    let U1 :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF 1
    let A :=
      ZMod (F.residueCharacteristic ^ a) ×
        (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) → ℤ_[F.residueCharacteristic])
    let : Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) := by
      infer_instance
    let emul : U1 ≃* Multiplicative A := by
      letI valuedK := Valued.mk' v
      letI : TopologicalSpace K := valuedK.toTopologicalSpace
      exact e.symm.toMulEquiv
    let :=
      LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv U1 (Multiplicative A) n
        emul
    let hex := F.toCompleteDVF.exists_uniformizer
    exact
      LocalFieldTheory.DiscreteValuationField.finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
        F.toCompleteDVF (Classical.choose_spec hex) n
  · let := hcharP
    let : CharP K F.residueCharacteristic := by
      rw [(F.residueCharacteristic_eq_of_charP p hp.out.ne_zero)]
      infer_instance
    have hpn : ¬ F.residueCharacteristic ∣ n := by
      intro hdiv
      apply hnK
      exact (CharP.cast_eq_zero_iff K F.residueCharacteristic n).2 hdiv
    let : Fact (Nat.Coprime n F.residueCharacteristic) :=
      ⟨(F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr hpn).symm⟩
    let U1 :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF 1
    let A := ℕ → ℤ_[F.residueCharacteristic]
    let : Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) := by
      infer_instance
    let emul : U1 ≃* Multiplicative A := by
      letI : TopologicalSpace K := (Valued.mk' v).toTopologicalSpace
      exact (LocalFieldTheory.DiscreteValuationField.LocalField.chosenFirstPrincipalUnitStructure_equalCharacteristic
        v).symm.toMulEquiv
    let :=
      LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv U1 (Multiplicative A) n
        emul
    let hex := F.toCompleteDVF.exists_uniformizer
    exact
      LocalFieldTheory.DiscreteValuationField.finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
        F.toCompleteDVF (Classical.choose_spec hex) n

end LocalFieldTheory

end
