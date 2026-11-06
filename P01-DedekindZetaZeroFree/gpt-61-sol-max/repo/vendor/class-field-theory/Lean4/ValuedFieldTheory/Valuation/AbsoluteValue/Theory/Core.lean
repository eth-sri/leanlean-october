module

public import Mathlib

public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations




































































/-- The graded piece `π^n𝒪 / π^{n+1}𝒪` as an additive quotient. -/
def uniformizerGradedPiece {O : Type*} [CommRing O] (π : O) (n : ℕ) : Type _ :=
  (uniformizerPowerIdeal π n) ⧸
    (Submodule.comap (uniformizerPowerIdeal π n).subtype
      (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
        Submodule O (uniformizerPowerIdeal π n))

/-- A uniformizer graded piece inherits an additive commutative group structure. -/
instance uniformizerGradedPieceAddCommGroup
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    AddCommGroup (uniformizerGradedPiece π n) := by
  change AddCommGroup
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  infer_instance

/-- A uniformizer graded piece is a module over the valuation subring. -/
instance uniformizerGradedPieceModule
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Module O (uniformizerGradedPiece π n) := by
  change Module O
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  infer_instance

section
variable {O : Type*} [CommRing O] (π : O) (n : ℕ)
include O π n
/-- Explicit access to the submodule quotient implementing a uniformizer
graded piece. -/
def uniformizerGradedPieceConcreteLinearEquiv
      :
    uniformizerGradedPiece π n ≃ₗ[O]
      ((uniformizerPowerIdeal π n) ⧸
        (Submodule.comap (uniformizerPowerIdeal π n).subtype
          (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
            Submodule O (uniformizerPowerIdeal π n))) := by
  change
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n))) ≃ₗ[O]
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  exact LinearEquiv.refl O _

/-- The canonical class map into `π^n𝒪 / π^(n+1)𝒪`. -/
def uniformizerGradedPieceMk
      :
    uniformizerPowerIdeal π n →ₗ[O] uniformizerGradedPiece π n := by
  change uniformizerPowerIdeal π n →ₗ[O]
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  exact Submodule.mkQ _

/-- The concrete graded-piece equivalence sends a quotient representative to the same coset. -/
@[simp] theorem uniformizerGradedPieceConcreteLinearEquiv_mk
     
    (a : uniformizerPowerIdeal π n) :
    uniformizerGradedPieceConcreteLinearEquiv π n
        (uniformizerGradedPieceMk π n a) =
      Submodule.Quotient.mk a :=
  rfl
end








/-- Eliminate a uniformizer graded-piece class through its canonical
representatives. -/
protected theorem uniformizerGradedPiece.inductionOn
    {O : Type*} [CommRing O] (π : O) (n : ℕ)
    {motive : uniformizerGradedPiece π n → Prop}
    (q : uniformizerGradedPiece π n)
    (h : ∀ a : uniformizerPowerIdeal π n,
      motive (uniformizerGradedPieceMk π n a)) :
    motive q := by
  change motive
    (show
      (uniformizerPowerIdeal π n) ⧸
        (Submodule.comap (uniformizerPowerIdeal π n).subtype
          (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
            Submodule O (uniformizerPowerIdeal π n)) from q)
  refine Quotient.inductionOn q ?_
  intro a
  exact h a

section
variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (π : O) (n : ℕ)
    (f : uniformizerPowerIdeal π n →ₗ[O] M)
    (h :
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)) ≤ f.ker)
include O M π n f h
/-- Descend a linear map that vanishes on `π^(n+1)𝒪` inside `π^n𝒪`. -/
def uniformizerGradedPieceLinearLift
      :
    uniformizerGradedPiece π n →ₗ[O] M := by
  change
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n))) →ₗ[O] M
  exact
    (Submodule.comap (uniformizerPowerIdeal π n).subtype
      (uniformizerPowerIdeal π (n + 1) : Submodule O O)).liftQ f h

/-- A linear lift from the graded piece evaluates on representatives by the supplied map. -/
@[simp] theorem uniformizerGradedPieceLinearLift_mk
     
    (a : uniformizerPowerIdeal π n) :
    uniformizerGradedPieceLinearLift π n f h
        (uniformizerGradedPieceMk π n a) = f a :=
  rfl
end























section
variable {O : Type*} [CommRing O] (π : O) (n : ℕ)
include O π n
/-- The higher-unit condition `u ∈ 1 + π^n𝒪`. -/
def HigherUnit   (u : Oˣ)  :=
  ∃ a : O, (u : O) = 1 + π ^ n * a

/-- The higher-unit condition is equivalently `u - 1 ∈ π^n𝒪`. -/
theorem higherUnit_iff_sub_one_mem_powerIdeal   (u : Oˣ) :
    HigherUnit π n u ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
  constructor
  · rintro ⟨a, ha⟩
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
    refine ⟨a, ?_⟩
    rw [ha]
    ring
  · intro hu
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton'] at hu
    rcases hu with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + a * π ^ n := by rw [← ha]
      _ = 1 + π ^ n * a := by ring

/-- The higher unit group `U⁽ⁿ⁾ = 1 + π^n𝒪`, as an actual subgroup of `Oˣ`. -/
def higherUnitSubgroup   : Subgroup Oˣ where
  carrier := {u | HigherUnit π n u}
  one_mem' := by
    use 0
    simp
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    use a + b + π ^ n * a * b
    calc
      ((u * v : Oˣ) : O) = (u : O) * (v : O) := rfl
      _ = (1 + π ^ n * a) * (1 + π ^ n * b) := by rw [ha, hb]
      _ = 1 + π ^ n * (a + b + π ^ n * a * b) := by ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    use -((u⁻¹ : Oˣ) : O) * a
    have hmul : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := by
      simp
    calc
      ((u⁻¹ : Oˣ) : O) =
          ((u⁻¹ : Oˣ) : O) * (u : O) -
            ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        ring
      _ = 1 - ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        rw [hmul]
      _ = 1 + π ^ n * (-((u⁻¹ : Oˣ) : O) * a) := by
        rw [ha]
        ring
end


section
variable {O : Type*} [CommRing O]
include O
/-- Membership in a higher-unit subgroup is characterized by proximity to one at the given level. -/
@[simp]
theorem mem_higherUnitSubgroup  
    {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ HigherUnit π n u :=
  Iff.rfl

/-- Membership in the higher-unit subgroup is equivalently `u - 1 ∈ π^n𝒪`. -/
def mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
      {π : O} {n : ℕ} {u : Oˣ}  := Iff.trans mem_higherUnitSubgroup
    (higherUnit_iff_sub_one_mem_powerIdeal π n u)








































































/-- The higher-unit filtration is decreasing for arbitrary comparable indices. -/
theorem higherUnitSubgroup_le_of_le  
    (π : O) {m n : ℕ} (hmn : m ≤ n) :
    higherUnitSubgroup π n ≤ higherUnitSubgroup π m := by
  rintro u ⟨a, ha⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  use π ^ k * a
  calc
    (u : O) = 1 + π ^ (m + k) * a := ha
    _ = 1 + π ^ m * (π ^ k * a) := by
      rw [pow_add]
      ring













/-- Reduction of units modulo an ideal. -/
def unitReduction   (I : Ideal O) : Oˣ →* (O ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

/-- Unit reduction is the residue of the underlying valuation-ring unit. -/
@[simp]
theorem unitReduction_apply   (I : Ideal O) (u : Oˣ) :
    (unitReduction I u : O ⧸ I) = Ideal.Quotient.mk I (u : O) :=
  rfl

/-- The kernel of reduction modulo `π^n𝒪` is the higher unit group `1 + π^n𝒪`. -/
theorem unitReduction_ker_powerIdeal  
    (π : O) (n : ℕ) :
    (unitReduction (uniformizerPowerIdeal π n)).ker = higherUnitSubgroup π n := by
  ext u
  constructor
  · intro hu
    have hval :
        Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1 := congrArg Units.val hu
    have hmem : (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp [map_sub, hval]
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + π ^ n * a := by rw [ha]
  · rintro ⟨a, ha⟩
    rw [MonoidHom.mem_ker]
    ext
    change Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1
    rw [ha]
    rw [← (Ideal.Quotient.mk (uniformizerPowerIdeal π n)).map_one]
    apply Ideal.Quotient.eq.mpr
    have hπ : π ^ n ∈ uniformizerPowerIdeal π n :=
      Ideal.subset_span (rfl)
    simpa using (uniformizerPowerIdeal π n).mul_mem_right a hπ













/-- A local quotient map induces a surjection on unit groups. -/
def unitReduction_surjective_of_isLocalHom  
    (I : Ideal O) [IsLocalHom (Ideal.Quotient.mk I)]  := IsLocalRing.surjective_units_map_of_local_ringHom
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective inferInstance






















/-- The first-isomorphism-theorem form of the unit quotient modulo `π^n𝒪`. -/
noncomputable def unitsModPowerIdealEquivOfSurjective  
    (π : O) (n : ℕ)
    (hsurj : Function.Surjective (unitReduction (uniformizerPowerIdeal π n)))  :=
  (QuotientGroup.quotientMulEquivOfEq
      (unitReduction_ker_powerIdeal π n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (unitReduction (uniformizerPowerIdeal π n)) hsurj)

















































/-- For `n ≥ 1`, the ideal `π^n𝒪` is contained in `(π)`. -/
theorem uniformizerPowerIdeal_le_span_singleton  
    {π : O} {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.span ({π} : Set O) := by
  simp_all [LubinTate.Valuations.uniformizerPowerIdeal, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton] <;> aesop
end


section
variable {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n)
include O π hπ n hn
/-- In a DVR, `π^n𝒪` lies in the Jacobson radical for `n ≥ 1` and `π` irreducible. -/
theorem uniformizerPowerIdeal_le_jacobson_bot   :
    uniformizerPowerIdeal π n ≤ Ideal.jacobson (⊥ : Ideal O) := by
  have hmax : (Ideal.span ({π} : Set O)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hπ
  have hspan  :=
    IsLocalRing.eq_maximalIdeal hmax
  exact (uniformizerPowerIdeal_le_span_singleton (π := π) hn).trans
    (by rw [hspan]; apply IsLocalRing.maximalIdeal_le_jacobson)

/-- The quotient map modulo `π^n𝒪` is local in a DVR, for `n ≥ 1`. -/
def unitReduction_isLocalHom_of_dvr    :=
  isLocalHom_of_le_jacobson_bot (uniformizerPowerIdeal π n)
    (uniformizerPowerIdeal_le_jacobson_bot hπ hn)






















































































































































































































/-- The unit-reduction and graded-piece equivalences, surjectivity part for the reduction map on unit groups. -/
theorem units_reduction_surjective
      :
    Function.Surjective (unitReduction (uniformizerPowerIdeal π n)) := by
  let  :=
    unitReduction_isLocalHom_of_dvr hπ hn
  apply unitReduction_surjective_of_isLocalHom

/-- The unit-reduction and graded-piece equivalences, the named first-isomorphism-theorem equivalence
`Oˣ/U⁽ⁿ⁾ ≃ (O/π^nO)ˣ`. -/
noncomputable def units_quotient_equiv
       := unitsModPowerIdealEquivOfSurjective π n
    (units_reduction_surjective hπ hn)

/-- The unit-quotient equivalence of the unit-reduction and graded-piece equivalences is induced by
reduction modulo `πⁿO`. -/
@[simp]
theorem units_quotient_equiv_mk
      (u : Oˣ) :
    units_quotient_equiv hπ hn (QuotientGroup.mk u) =
      unitReduction (uniformizerPowerIdeal π n) u := by
  rfl
end

































end Valuations
end LubinTate

end
