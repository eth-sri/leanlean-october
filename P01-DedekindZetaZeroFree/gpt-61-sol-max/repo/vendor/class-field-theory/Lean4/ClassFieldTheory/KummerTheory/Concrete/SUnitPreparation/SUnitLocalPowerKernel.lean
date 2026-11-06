module

public import Mathlib

public import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The local-power kernel of S-units

The localization map on `S`-units, its kernel, its quotient by global powers, and the associated Kummer radical.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

section
variable (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
include n S T
/-- The diagonal localization map
`Kˢ → ∏ v ∈ T, K_vˣ / K_vˣⁿ`. -/
noncomputable def sUnitLocalPowerMap
      :
    SUnitGroup (K := K) S →*
      ∀ v : T,
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range :=
  (IdeleGroup.principalLocalQuotientMap
      (K := K) T
      (fun v =>
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletion K)ˣ →*
            (v.1.adicCompletion K)ˣ).range)).comp
    (SUnitGroup (K := K) S).subtype

/-- The subgroup `Δ` of `S`-units which are local `n`-th powers at every
place in `T`. -/
def sUnitLocalPowerKernel
      :
    Subgroup (SUnitGroup (K := K) S) :=
  MonoidHom.ker (sUnitLocalPowerMap (K := K) n S T)

/-- Elementwise description of the local-power kernel `Δ`. -/
theorem mem_sUnitLocalPowerKernel_iff
     
    (x : SUnitGroup (K := K) S) :
    x ∈ sUnitLocalPowerKernel (K := K) n S T ↔
      ∀ v : T,
        Units.map
            (algebraMap K
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)).toMonoidHom
            (x : Kˣ) ∈
          (powMonoidHom (n : ℕ) :
            ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range := by
  rw [sUnitLocalPowerKernel, MonoidHom.mem_ker]
  constructor
  · intro hx v
    have hv := congrFun hx v
    rw [Pi.one_apply] at hv
    exact (QuotientGroup.eq_one_iff _).mp hv
  · intro hx
    funext v
    exact (QuotientGroup.eq_one_iff _).mpr (hx v)

/-- Global `n`-th powers are local `n`-th powers at every place. -/
theorem nthPowerSubgroup_le_sUnitLocalPowerKernel
      :
    (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range ≤
      sUnitLocalPowerKernel (K := K) n S T := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) S)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [sUnitLocalPowerKernel, MonoidHom.mem_ker, map_pow]
  change (sUnitLocalPowerMap (K := K) n S T y) ^ (n : ℕ) = 1
  funext v
  exact (QuotientGroup.eq_one_iff _).mpr
    ((MonoidHom.mem_range
      (G :=
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)).mpr
      ⟨_, rfl⟩)

/-- The copy of `Kˢⁿ` inside the local-power kernel `Δ`. -/
def sUnitLocalPowerKernelNthPowers
       :=
  ((powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) S →*
        SUnitGroup (K := K) S).range).comap
    (sUnitLocalPowerKernel (K := K) n S T).subtype
end





























































































end KummerTheory

end
