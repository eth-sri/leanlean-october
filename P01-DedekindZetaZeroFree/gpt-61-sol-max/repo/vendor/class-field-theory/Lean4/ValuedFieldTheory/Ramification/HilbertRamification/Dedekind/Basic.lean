module

public import Mathlib

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Hilbert ramification theory: Dedekind-domain layer

This file manages the Dedekind-domain part of Hilbert ramification theory in
prime-decomposition theory.

The implementation uses mathlib's ramification/inertia theorems where those
are already the source proof, but the decomposition/inertia/residue-action
interface is proved here: membership criteria, residue-action formula,
normality of inertia in the decomposition group, exactness, and quotient form.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

section
variable (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B]
include P G
/-- The decomposition and inertia definition:
the decomposition group of a prime ideal. -/
abbrev decompositionGroup
       :=
  MulAction.stabilizer G P









/-- The inertia-field definition:
the inertia group of a prime ideal. -/
abbrev inertiaGroup
       :=
  P.toAddSubgroup.inertia G
end


/-- Membership in the inertia group is trivial action on the residue ring. -/
@[simp]
theorem mem_inertiaGroup_iff
    {P : Ideal B} {G : Type*} [Group G] [MulSemiringAction G B] {σ : G} :
    σ ∈ inertiaGroup P G ↔ ∀ x : B, σ • x - x ∈ P :=
  Iff.rfl

/-- prime-decomposition theory:
the residue-field action of the decomposition group. -/
abbrev residueStabilizerHom
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]  :=
  Ideal.Quotient.stabilizerHom P p G




























section
variable (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
include p P Q G
/-- The valuation-conjugacy theorem:
the Galois group acts transitively on primes over a fixed prime. -/
def exists_smul_eq_of_isGaloisGroup
       := Ideal.exists_smul_eq_of_isGaloisGroup p P Q G

/-- prime-decomposition theory: in the Galois case the ramification index is
independent of the prime above `p`. -/
def dedekindRamification_ramificationIdx_eq
       := Ideal.ramificationIdx_eq_of_isGaloisGroup p P Q G
end



































































/-- prime-decomposition theory:
the kernel of the residue action is the inertia group. -/
def dedekindRamification_residueAction_ker
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]  := Ideal.Quotient.ker_stabilizerHom P p G












section
variable (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
include p P G
/-- prime-decomposition theory:
for a finite invariant Galois action, the residue action is surjective. -/
def dedekindRamification_residueAction_surjective
       := Ideal.Quotient.stabilizerHom_surjective G p P





















































/-- The localization and decomposition comparison gives:
the quotient of the decomposition group by inertia is the residue Galois group.
-/
def dedekindRamification_decompositionQuotientInertiaEquivResidueGalois
       :=
  (QuotientGroup.quotientMulEquivOfEq
      (dedekindRamification_residueAction_ker p P G).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (residueStabilizerHom p P G)
      (dedekindRamification_residueAction_surjective p P G))
end



















































































/-- prime-decomposition theory, Galois fundamental identity:
`r * e * f = |G|`, with `e` and `f` independent of the chosen prime above `p`.
-/
def dedekindRamification_galois_fundamental_identity
    [IsDedekindDomain A] (p : Ideal A) [p.IsMaximal] (_hpb : p ≠ ⊥)
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]  := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G










































/-- The prime-decomposition tower identity:
orbit-stabilizer for the action on primes above `p`,
`r * #G_P = #G`. -/
theorem dedekindRamification_ncard_primesOver_mul_decomposition_card
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    (p.primesOver B).ncard * Nat.card (decompositionGroup P G) =
      Nat.card G := by
  rw [← IsInvariant.orbit_eq_primesOver A B G p P]
  simpa [decompositionGroup] using
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The prime-decomposition tower identity:
the decomposition group has cardinality `e * f`. -/
theorem dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B := by
  have hdec :=
    dedekindRamification_ncard_primesOver_mul_decomposition_card
      (A := A) (B := B) p P G
  have hfund :=
    dedekindRamification_galois_fundamental_identity
      (A := A) p hp B G
  exact
    Nat.mul_left_cancel
      (Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero p B))
      (hdec.trans hfund.symm)



section
variable (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
include p P G
/-- Prime-decomposition statement:
the quotient of the decomposition group by inertia has cardinality equal to
the inertia degree. -/
theorem dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
      :
  Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
      P.inertiaDeg A := by
  have h  :=
    isGalois_iff.mpr ⟨inferInstance, Ideal.Quotient.normal (A := A) G p P⟩
  let  := Ideal.Quotient.finite_of_isInvariant G p P
  let : FiniteDimensional (A ⧸ p) (B ⧸ P) := IsGalois.finiteDimensional_of_finite
    (F := A ⧸ p) (E := B ⧸ P)
  calc
    Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
        Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P) := Nat.card_congr
          (dedekindRamification_decompositionQuotientInertiaEquivResidueGalois
            (A := A) (B := B) p P G).toEquiv
    _ = Module.finrank (A ⧸ p) (B ⧸ P) := by
      apply IsGalois.card_aut_eq_finrank
    _ = P.inertiaDeg A := by
      rw [Ideal.inertiaDeg_eq_of_isMaximal p P]

/-- Prime-decomposition statement:
the quotient cardinality is the Galois-invariant inertia degree `f`. -/
theorem dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDegIn
      :
    Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
      Ideal.inertiaDegIn p B := by
  rw [dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
    (A := A) (B := B) p P G]
  exact (Ideal.inertiaDegIn_eq_inertiaDeg p P G).symm
end


/-- Prime-decomposition statement:
`#G_P = #(G_P/I_P) * #I_P` for the exact residue sequence. -/
theorem dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Nat.card (decompositionGroup P G) =
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) *
        Nat.card (inertiaGroup P G) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((inertiaGroup P G).subgroupOf (decompositionGroup P G))]
  congr 1
  exact
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv

/-- Prime-decomposition statement:
`#G_P = #I_P * f`, with `f` the Galois-invariant inertia degree. -/
theorem dedekindRamification_decomposition_card_eq_inertia_card_mul_inertiaDegIn
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      Nat.card (inertiaGroup P G) * Ideal.inertiaDegIn p B := by
  rw [dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
    (B := B) P G,
    dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDegIn
      (A := A) (B := B) p P G,
    mul_comm]


/-- prime-decomposition theory: the inertia subgroup has cardinality equal to the
Galois ramification index. -/
theorem dedekindRamification_inertia_card_eq_ramificationIdxIn
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (P.toAddSubgroup.inertia G) = Ideal.ramificationIdxIn p B := by
  let  := Algebra.IsIntegral.of_finite A B
  let  := Ideal.IsMaximal.of_isMaximal_liesOver P p
  have hdecomp_inertia :=
    dedekindRamification_decomposition_card_eq_inertia_card_mul_inertiaDegIn
      (A := A) (B := B) p P G
  have hdecomp_ramification :=
    dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
      (A := A) (B := B) p hp P G
  have hinertiaDeg_pos : 0 < Ideal.inertiaDegIn p B := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p P G]
    exact P.inertiaDeg_pos A
  apply Nat.mul_left_cancel hinertiaDeg_pos
  calc
    Ideal.inertiaDegIn p B * Nat.card (P.toAddSubgroup.inertia G) =
        Nat.card (P.toAddSubgroup.inertia G) * Ideal.inertiaDegIn p B := by
      rw [mul_comm]
    _ = Nat.card (decompositionGroup P G) := hdecomp_inertia.symm
    _ = Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B :=
      hdecomp_ramification
    _ = Ideal.inertiaDegIn p B * Ideal.ramificationIdxIn p B := by
      rw [mul_comm]

end Dedekind
end HilbertRamification

end
