module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Cyclotomic degree bounds for inertia

An inertia group is bounded by the degree of its Galois extension.  An
embedding into a concrete cyclotomic field therefore bounds its cardinality
by Euler's totient.
-/

noncomputable section

namespace HilbertRamification

open Polynomial



/-- Over a characteristic-zero field, the concrete cyclotomic field of
order `m` has degree at most `φ(m)`. -/
theorem cyclotomicField_finrank_le_totient
    (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 0 < m) :
    Module.finrank K (CyclotomicField m K) ≤ Nat.totient m := by
  let : NeZero m := ⟨hm.ne'⟩
  let C := CyclotomicField m K
  let : IsCyclotomicExtension {m} K C :=
    CyclotomicField.isCyclotomicExtension m K
  let : FiniteDimensional K C :=
    IsCyclotomicExtension.finiteDimensional {m} K C
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension m K).exists_isPrimitiveRoot
      (Set.mem_singleton m) hm.ne'
  have hgen : Algebra.adjoin K ({ζ} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop : IntermediateField.adjoin K ({ζ} : Set C) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K ({ζ} : Set C) hgen
  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic m K) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hm
  have hdegree :
      (minpoly K ζ).natDegree ≤ (Polynomial.cyclotomic m K).natDegree :=
    Polynomial.natDegree_le_natDegree
      (minpoly.min K ζ (Polynomial.cyclotomic.monic m K) hroot)
  calc
    Module.finrank K (CyclotomicField m K) = Module.finrank K C := rfl
    _ = Module.finrank K (IntermediateField.adjoin K ({ζ} : Set C)) := by
      rw [htop]
      simp
    _ = (minpoly K ζ).natDegree :=
      IntermediateField.adjoin.finrank (IsIntegral.of_finite K ζ)
    _ ≤ (Polynomial.cyclotomic m K).natDegree := hdegree
    _ = Nat.totient m := Polynomial.natDegree_cyclotomic m K



end HilbertRamification

end
