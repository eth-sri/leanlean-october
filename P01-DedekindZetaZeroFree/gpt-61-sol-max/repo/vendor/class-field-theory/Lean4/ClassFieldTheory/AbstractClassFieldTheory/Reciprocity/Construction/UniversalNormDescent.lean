module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm
public import Mathlib.Dynamics.BirkhoffSum.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Universal norm descent

This module contains the representation-theoretic lifting and correction
calculation used by the abstract reciprocity construction, together with
the norm, action, and iterate identities it requires.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators








































section
variable {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
include R
/-- Transport the ordinary conjugation action back to a field stabilized
by that conjugation. -/
noncomputable def conjugateStableAction
      [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : ambientFixedAddSubgroup B F :=
  hF ▸ conjugateFixedElement B F s a

private theorem transport_fixed_coe
     
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl

private theorem relativeNorm_transport_coe
     
    (B : Rep ℤ R)
    (F' E' F E : ClosedSubgroup R)
    (hF : F' = F) (hE : E' = E)
    (hE'F' : E'.toSubgroup ≤ F'.toSubgroup)
    (hEF : E.toSubgroup ≤ F.toSubgroup)
    [Finite (F'.toSubgroup ⧸ extensionSubgroup F' E' hE'F')]
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (a : ambientFixedAddSubgroup B E') :
    ((relativeNorm B F E hEF (hE ▸ a) : ambientFixedAddSubgroup B F) : B.V) =
      ((relativeNorm B F' E' hE'F' a : ambientFixedAddSubgroup B F') : B.V) := by
  cases hF
  cases hE
  rfl

/-- The conjugation-stable action agrees with its ambient action after coercion. -/
@[simp]
theorem conjugateStableAction_coe
      [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
      B.ρ s⁻¹ a.1 := transport_fixed_coe B _ F hF _

/-- Relative norm is equivariant for a conjugation stabilizing both
fields in the tower. -/
theorem relativeNorm_conjugateStableAction
      [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a) := by
  let hConj := conjugateClosedSubgroup_mono hEF s
  let : Finite ((conjugateClosedSubgroup F s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup F s)
        (conjugateClosedSubgroup E s) hConj) :=
    finite_conjugateExtension F E hEF s
  have hs := congrArg Subtype.val
    (relativeNorm_conjugate_apply B F E hEF s a)
  apply Subtype.ext
  calc
    ((relativeNorm B F E hEF (conjugateStableAction B E s hE a)) : B.V) =
        ((relativeNorm B (conjugateClosedSubgroup F s)
          (conjugateClosedSubgroup E s) hConj
          (conjugateFixedElement B E s a)) : B.V) := by
      apply relativeNorm_transport_coe <;> assumption
    _ = ((conjugateFixedElement B F s (relativeNorm B F E hEF a)) : B.V) := hs
    _ = ((conjugateStableAction B F s hF (relativeNorm B F E hEF a)) : B.V) :=
      (transport_fixed_coe B _ F hF _).symm
end





































































section
variable {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n)
include Q B g hg n hcard in
/-- Enumerate the norm of a finite cyclic representation by the first
n powers of a specified generator. -/
theorem rep_norm_eq_generatorPowerSum
      (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x := by
  classical
  have horder : orderOf g = n := by
    calc
      orderOf g = Nat.card Q :=
        orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Fintype.card Q := Nat.card_eq_fintype_card
      _ = n := hcard
  let e : Fin n ≃ Q := Equiv.ofBijective (fun i => g ^ i.1) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hmod : i.1 ≡ j.1 [MOD orderOf g] :=
        (pow_eq_pow_iff_modEq).mp hij
      rw [horder] at hmod
      exact hmod.eq_of_lt_of_lt i.2 j.2
    · intro q
      have himage :
          Finset.image (fun i => g ^ i) (Finset.range n) = Finset.univ := by
        rw [← horder]
        exact IsCyclic.image_range_orderOf hg
      have hq : q ∈ Finset.image (fun i => g ^ i) (Finset.range n) := by
        rw [himage]
        simp
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hq
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hiq⟩)
  have hsum : (∑ q : Q, B.ρ q x) =
      ∑ i : Fin n, B.ρ (g ^ i.1) x :=
    (e.sum_comp (fun q : Q => B.ρ q x)).symm
  simpa [Rep.norm, Representation.norm] using hsum

/-- Powers in a representation are the iterates of the corresponding
action map. -/
theorem rep_action_pow_eq_iterate {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) :
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x := by
  let  := B.hV2
  rw [map_pow, Module.End.coe_pow]

include Q B g hg n hcard in
/-- Replace the generator action in the preceding norm formula by a
pointwise equal endomorphism and enumerate its iterates. -/
theorem rep_norm_eq_generatorIterateSum
     
    (f : B.V → B.V) (hf : ∀ z, B.ρ g z = f z) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x := by
  rw [rep_norm_eq_generatorPowerSum B g hg n hcard x]
  apply Finset.sum_congr rfl
  intro i _
  rw [rep_action_pow_eq_iterate]
  exact congrFun (congrArg (fun h : B.V → B.V => h^[i.1]) (funext hf)) x
end


/-- Every nonnegative power fixes an element fixed by the original group
element. -/
theorem rep_action_pow_fixed {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) :
    B.ρ (g ^ n) x = x := by
  rw [rep_action_pow_eq_iterate]
  exact Function.IsFixedPt.iterate hx n

end

end ClassFormation
