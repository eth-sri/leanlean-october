module

public import GaloisCohomology.Kummer.Concrete.SimpleExtension
public import GaloisCohomology.Kummer.Concrete.FiniteGeneration

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Divisibility of simple Kummer extensions

If `m ∣ n` and the base contains `μₘ`, an `m`-th root of `a` differs from
the `(n/m)`-th power of an `n`-th root by a base-field root of unity. Thus
the chosen simple extensions form an actual tower in the separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory.Kummer

/-- A simple `m`-Kummer extension is contained in the corresponding
`n`-Kummer extension when `m ∣ n`. -/
theorem chosenSimpleKummerExtension_le_of_dvd
    (K : Type) [Field K]
    (m n : ℕ+) (hmK : ((m : ℕ) : K) ≠ 0)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmn : (m : ℕ) ∣ (n : ℕ)) (a : Kˣ) :
    KummerTheory.chosenSimpleKummerExtension K m hmK a ≤
      KummerTheory.chosenSimpleKummerExtension K n hnK a := by
  obtain ⟨q, hq⟩ := hmn
  let Ω := SeparableClosure K
  let αm : Ω := KummerTheory.chosenSimpleKummerRoot K m hmK a
  let αn : Ω := KummerTheory.chosenSimpleKummerRoot K n hnK a
  let Em := KummerTheory.chosenSimpleKummerExtension K m hmK a
  let En := KummerTheory.chosenSimpleKummerExtension K n hnK a
  have hαm : αm ^ (m : ℕ) = algebraMap K Ω (a : K) :=
    KummerTheory.chosenSimpleKummerRoot_pow K m hmK a
  have hαn : αn ^ (n : ℕ) = algebraMap K Ω (a : K) :=
    KummerTheory.chosenSimpleKummerRoot_pow K n hnK a
  have hαmne : αm ≠ 0 := by
    intro hz
    rw [hz, zero_pow m.pos.ne'] at hαm
    exact ((map_ne_zero (algebraMap K Ω)).2 (Units.ne_zero a)) hαm.symm
  have hαnne : αn ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.pos.ne'] at hαn
    exact ((map_ne_zero (algebraMap K Ω)).2 (Units.ne_zero a)) hαn.symm
  let um := Units.mk0 αm hαmne
  let un := Units.mk0 αn hαnne
  let ι := Units.map (algebraMap K Ω).toMonoidHom
  have humpow : um ^ (m : ℕ) = ι a := by
    apply Units.ext
    exact hαm
  have hunpow : un ^ (n : ℕ) = ι a := by
    apply Units.ext
    exact hαn
  have hqm : q * (m : ℕ) = (n : ℕ) := by
    rw [mul_comm, ← hq]
  let u := un ^ q / um
  have hu : u ^ (m : ℕ) = 1 := by
    change (un ^ q / um) ^ (m : ℕ) = 1
    rw [div_pow, ← pow_mul, hqm, hunpow, humpow, div_self']
  obtain ⟨ζ, hζ⟩ :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
        m hmuM u hu
  have hζmul : ι ζ * um = un ^ q := by
    rw [hζ]
    exact div_mul_cancel (un ^ q) um
  have hum : um = (ι ζ)⁻¹ * un ^ q := by
    calc
      um = (ι ζ)⁻¹ * (ι ζ * um) := by
        simp
      _ = (ι ζ)⁻¹ * un ^ q := by rw [hζmul]
  have hαmval : αm = (algebraMap K Ω (ζ : K))⁻¹ * αn ^ q := by
    have h := congrArg Units.val hum
    dsimp only [um, un, ι] at h
    simpa using h
  have hαmmem : αm ∈ En := by
    rw [hαmval]
    exact mul_mem (inv_mem (En.algebraMap_mem (ζ : K))) (pow_mem (IntermediateField.subset_adjoin K {αn} (Set.mem_singleton αn)) q)
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [(Set.mem_singleton_iff.mp hx)]
  exact hαmmem

end LocalClassFieldTheory.Kummer

end
