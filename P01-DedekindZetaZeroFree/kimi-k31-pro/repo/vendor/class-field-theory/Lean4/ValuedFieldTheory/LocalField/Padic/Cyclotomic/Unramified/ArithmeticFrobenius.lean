module

public import ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import ValuedFieldTheory.Valuation.LocalRingEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Arithmetic Frobenius on the unramified cyclotomic extension

Let `K` be a complete discretely valued field with finite residue field
`k = F_q`, let `ζ` be a primitive `n`-th root of unity, and suppose that `n`
is prime to the residue characteristic.  the unramified cyclotomic theorem states that
`K(ζ) / K` is unramified of degree the order of `q` modulo `n`, identifies
its Galois group with the residue Galois group and arithmetic Frobenius, and
proves `O_{K(ζ)} = O_K[ζ]`.

The proof follows the arithmetic construction directly and uses no comparison certificate:

* the exact least-positive-exponent characterization of the order of `q`
  modulo `n`;
* the cyclotomic polynomial as the primitive separable integral model in the
  the unramified base-change theorem Hensel core, giving unramifiedness and the degree formula;
* the canonical reduction homomorphism from field automorphisms to residue
  automorphisms, with injectivity from uniqueness of simple Hensel lifts and
  surjectivity from the genuine Galois cardinalities;
* arithmetic Frobenius, its formula `ζ ↦ ζ^q`, and generation of the Galois
  group;
* the reverse integral-ring inclusion by residue generation, ramification
  index one, and Nakayama, yielding `O_{K(ζ)} = O_K[ζ]`.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial ZMod


/-- The integer `f` in the unramified cyclotomic theorem: the multiplicative order of the
residue cardinality `q` modulo `n`. -/
def padicCyclotomicUnramifiedResidueDegree (n q : ℕ) (hqn : q.Coprime n) : ℕ :=
  orderOf (ZMod.unitOfCoprime q hqn)

theorem padicCyclotomicUnramifiedResidueDegree_pos
    (n q : ℕ) (hqn : q.Coprime n) :
    0 < padicCyclotomicUnramifiedResidueDegree n q hqn := by
  exact orderOf_pos _

/-- The defining exponent satisfies `q^f = 1 mod n`. -/
theorem padicCyclotomicUnramifiedResidueDegree_modEq_one
    (n q : ℕ) (hqn : q.Coprime n) :
    q ^ padicCyclotomicUnramifiedResidueDegree n q hqn ≡ 1 [MOD n] := by
  have hpow := pow_orderOf_eq_one (ZMod.unitOfCoprime q hqn)
  have hval := congrArg Units.val hpow
  rw [Units.val_pow_eq_pow_val, coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hval
  exact hval

/-- Minimality of the exponent in the unramified cyclotomic theorem. -/
theorem padicCyclotomicUnramifiedResidueDegree_le_of_modEq_one
    (n q : ℕ) (hqn : q.Coprime n) {m : ℕ}
    (hm : 0 < m) (hqm : q ^ m ≡ 1 [MOD n]) :
    padicCyclotomicUnramifiedResidueDegree n q hqn ≤ m := by
  apply orderOf_le_of_pow_eq_one hm
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  exact hqm




/-- A root of unity is integral over any coefficient ring acting on its
ambient field.  This is the element-level source for the unramified cyclotomic theorem(iii). -/
theorem padicCyclotomicUnramified_primitiveRoot_isIntegral
    {R : Type u} {L : Type v} [CommRing R] [Field L] [Algebra R L]
    {n : ℕ} {ζ : L} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    IsIntegral R ζ := by
  apply IsIntegral.of_pow hn
  rw [hζ.pow_eq_one]
  exact isIntegral_one

/-- Turn a literal equality with the integral closure into the standard
`IsIntegralClosure` instance. -/
 theorem padicCyclotomicUnramified_isIntegralClosure_of_subring_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : Subring K) (W : Subring L) [Algebra V L]
    (h : W = (integralClosure V L).toSubring) :
    IsIntegralClosure W V L := by
  refine
    { algebraMap_injective := W.subtype_injective
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hxW : x ∈ W := by
      rw [h]
      exact hx
    exact ⟨⟨x, hxW⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    change (y : L) ∈ (integralClosure V L).toSubring
    rw [← h]
    exact y.property

/-- Two simple roots over a local domain which have the same residue class
are equal.  This is the uniqueness half of Hensel's lemma, in the small
generality needed for the residue-action comparisons below and in the
generic unramified support lemma for the unramified cyclotomic theorem. -/
theorem padicCyclotomicUnramified_eq_of_roots_of_residue_eq_of_derivative_isUnit
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : R[X]} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : IsLocalRing.residue R b = IsLocalRing.residue R a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : R[X] := f /ₘ (X - C a)
  have hfactor : (X - C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hqEval : q.eval a = f.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval f a
  have hqUnit : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hqResidue :
      IsLocalRing.residue R (q.eval b) =
        IsLocalRing.residue R (q.eval a) := by
    calc
      IsLocalRing.residue R (q.eval b) =
          (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R b) := by
        exact (Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) b).symm
      _ = (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R a) := by rw [hres]
      _ = IsLocalRing.residue R (q.eval a) := by
        exact Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) a
  have hqResidueNe : IsLocalRing.residue R (q.eval b) ≠ 0 := by
    rw [hqResidue]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (q.eval a)).2 hqUnit
  have hqNe : q.eval b ≠ 0 := by
    intro hzero
    exact hqResidueNe (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hbEval : ((X - C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hbEval
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hqNe)

section CanonicalResidueAction

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- Restriction of a `K`-automorphism to the target valuation ring.  The
target ring is the integral closure of the Henselian base valuation ring, so
this restriction is canonical. -/
noncomputable def padicCyclotomicUnramified_galIntegerRingEquiv
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) :
    LubinTate.Valuations.exponentialValuationSubring vL ≃+*
      LubinTate.Valuations.exponentialValuationSubring vL := by
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  letI : Algebra V L := algVL
  letI : SMul V L := algVL.toSMul
  letI : Module V L := algVL.toModule
  letI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  letI : IsIntegralClosure W V L :=
    padicCyclotomicUnramified_isIntegralClosure_of_subring_eq V W hclosure
  have hmem (τ : Gal(L/K)) (x : W) : τ (x : L) ∈ W := by
    have hx : IsIntegral V (x : L) :=
      (IsIntegralClosure.isIntegral_iff
        (A := W) (R := V) (B := L)).2 ⟨x, rfl⟩
    have hτ : IsIntegral V (τ (x : L)) :=
      IsIntegral.map τ.toAlgHom hx
    rcases (IsIntegralClosure.isIntegral_iff
      (A := W) (R := V) (B := L)).1 hτ with ⟨y, hy⟩
    exact hy ▸ y.property
  exact
    { toFun := fun x ↦ ⟨σ (x : L), hmem σ x⟩
      invFun := fun x ↦ ⟨σ.symm (x : L), hmem σ.symm x⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp
      map_mul' := by intro x y; ext; simp
      map_add' := by intro x y; ext; simp }

@[simp]
theorem padicCyclotomicUnramified_galIntegerRingEquiv_apply
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) (x : LubinTate.Valuations.exponentialValuationSubring vL) :
    ((padicCyclotomicUnramified_galIntegerRingEquiv
      vK vL hExt hhens σ x : LubinTate.Valuations.exponentialValuationSubring vL) : L) =
      σ (x : L) :=
  rfl

/-- The residue field attached to an exponential valuation. -/
abbrev padicCyclotomicUnramifiedResidueField {F : Type*} [Field F]
    (vF : LubinTate.Valuations.ExponentialValuation F) :=
  IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring vF)

/-- The canonical residue-field algebra structure of a valuation extension. -/
@[reducible] noncomputable def padicCyclotomicUnramifiedResidueAlgebra
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x) :
    Algebra (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) := by
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  exact (IsLocalRing.ResidueField.map i).toAlgebra

/-- Finite-dimensionality of the residue extension, transported to the
module structure induced by `padicCyclotomicUnramifiedResidueAlgebra`. -/
theorem padicCyclotomicUnramified_residueFiniteDimensional
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    FiniteDimensional (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hfinite :
      @FiniteDimensional k ell _ _ residueModule :=
    residueExtension_finiteDimensional_of_finiteDimensional
      vK vL hExt
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  change @FiniteDimensional k ell _ _ algebraModule
  rw [← hmodule]
  exact hfinite

omit [FiniteDimensional K L] in
/-- The residue degree uses the quotient-induced module structure;
this identifies it with the finrank for `padicCyclotomicUnramifiedResidueAlgebra`. -/
theorem padicCyclotomicUnramified_exponentialResidueDegree_eq_finrank
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    exponentialResidueDegree vK vL hExt =
      Module.finrank (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := exponentialValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  change @Module.finrank k ell _ _ residueModule =
    @Module.finrank k ell _ _ algebraModule
  rw [hmodule]

/-- A ring equivalence of a local extension which fixes the base ring induces
an algebra equivalence of residue fields. -/
 theorem padicCyclotomicUnramified_residueMapEquiv_commutes
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (i : R →+* S) [IsLocalHom i] (e : S ≃+* S)
    (hfix : ∀ x : R, e (i x) = i x) :
    letI : Algebra (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) :=
      (IsLocalRing.ResidueField.map i).toAlgebra
    ∀ x : IsLocalRing.ResidueField R,
      IsLocalRing.ResidueField.mapEquiv e (algebraMap
          (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) x) =
        algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) x := by
  let : Algebra (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.ResidueField.mapEquiv e
      (IsLocalRing.ResidueField.map i (IsLocalRing.residue R y)) =
    IsLocalRing.ResidueField.map i (IsLocalRing.residue R y)
  rw [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue S) (hfix y)

/-- The canonical action of `Gal(L/K)` on the residue extension. -/
noncomputable def padicCyclotomicUnramified_galResidueAlgEquiv
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    padicCyclotomicUnramifiedResidueField vL ≃ₐ[padicCyclotomicUnramifiedResidueField vK]
      padicCyclotomicUnramifiedResidueField vL := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  letI : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let eW := padicCyclotomicUnramified_galIntegerRingEquiv vK vL hExt hhens σ
  let eell : ell ≃+* ell := IsLocalRing.ResidueField.mapEquiv eW
  apply AlgEquiv.ofRingEquiv
  apply padicCyclotomicUnramified_residueMapEquiv_commutes i eW
  intro y
  apply Subtype.ext
  change σ (algebraMap K L (y : K)) = algebraMap K L (y : K)
  exact σ.commutes (y : K)

@[simp]
theorem padicCyclotomicUnramified_galResidueAlgEquiv_residue
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) (x : LubinTate.Valuations.exponentialValuationSubring vL) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens σ
        (IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring vL) x) =
      IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring vL)
        (padicCyclotomicUnramified_galIntegerRingEquiv vK vL hExt hhens σ x) := by
  simp only [padicCyclotomicUnramified_galResidueAlgEquiv,
    AlgEquiv.ofRingEquiv_apply,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rfl

/-- The canonical residue action as a group homomorphism. -/
noncomputable def padicCyclotomicUnramified_galToResidueGal
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Gal(L/K) →*
      Gal(padicCyclotomicUnramifiedResidueField vL / padicCyclotomicUnramifiedResidueField vK) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  letI : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  refine
    { toFun := padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens
      map_one' := ?_
      map_mul' := ?_ }
  · ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens 1
        (IsLocalRing.residue W y) = IsLocalRing.residue W y
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue]
    change IsLocalRing.residue W
        (padicCyclotomicUnramified_galIntegerRingEquiv vK vL hExt hhens 1 y) =
      IsLocalRing.residue W y
    apply congrArg (IsLocalRing.residue W)
    apply Subtype.ext
    change (1 : Gal(L/K)) (y : L) = (y : L)
    rfl
  · intro σ τ
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens (σ * τ)
        (IsLocalRing.residue W y) =
      padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens σ
        (padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens τ
          (IsLocalRing.residue W y))
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue]
    change IsLocalRing.residue W
        (padicCyclotomicUnramified_galIntegerRingEquiv vK vL hExt hhens (σ * τ) y) = _
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue,
      padicCyclotomicUnramified_galResidueAlgEquiv_residue]
    apply congrArg (IsLocalRing.residue W)
    apply Subtype.ext
    change (σ * τ) (y : L) = σ (τ (y : L))
    rfl

end CanonicalResidueAction

/-- A field generated by a primitive root of unity is normal; together with
separability this gives the Galois input used in the unramified cyclotomic theorem(ii). -/
theorem padicCyclotomicUnramified_isGalois_of_primitiveRoot_adjoin_eq_top
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L]
    {n : ℕ} {ζ : L} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    IsGalois K L := by
  let P : K[X] := X ^ n - C 1
  let : P.IsSplittingField K L :=
    { splits' := by
        simpa [P] using Polynomial.X_pow_sub_one_splits hζ
      adjoin_rootSet' := by
        apply top_unique
        rw [← hζgen]
        apply Algebra.adjoin_mono
        intro x hx
        have hxζ : x = ζ := by simpa using hx
        subst x
        rw [Polynomial.mem_rootSet]
        constructor
        · exact (Polynomial.monic_X_pow_sub_C (1 : K) hn.ne').ne_zero
        · rw [Polynomial.aeval_def, Polynomial.eval₂_sub,
            Polynomial.eval₂_pow, Polynomial.eval₂_X,
            Polynomial.eval₂_C]
          simp [hζ.pow_eq_one] }
  let : Normal K L := Normal.of_isSplittingField P
  exact IsGalois.mk

section FiniteResidueCyclotomic

variable {k : Type u} {Ω : Type v}
variable [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
variable {p r n : ℕ} [hp : Fact p.Prime]

theorem padicCyclotomicUnramified_order_pos (hpn : p.Coprime n) : 0 < n := by
  apply Nat.pos_of_ne_zero
  intro hn
  have hnot : ¬p ∣ n := hp.out.coprime_iff_not_dvd.mp hpn
  exact hnot (hn ▸ dvd_zero p)







end FiniteResidueCyclotomic

section LocalCyclotomicUnramified

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- the unramified cyclotomic theorem(i), local Hensel step.

For a Henselian exponential valuation with finite residue field of cardinality
`p^r`, adjoining a primitive `n`-th root of unity, with `p` prime to `n`, is a
finite unramified extension in the literal sense of the finite unramified-extension definition.  The
primitive integral model used here is the cyclotomic polynomial itself; its
reduction is separable because `n` is nonzero in the residue field. -/
theorem padicCyclotomicUnramified_finiteUnramifiedExtension
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring vK))]
    (hk : Fintype.card (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring vK)) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    FiniteUnramifiedExtension vK vL hExt := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let k := IsLocalRing.ResidueField V
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let algVW : Algebra V W := i.toAlgebra
  let : Algebra V W := algVW
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  have hζIntegral : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζmem : ζ ∈ W := by
    rw [hclosure]
    exact hζIntegral
  let a : W := ⟨ζ, hζmem⟩
  let F : V[X] := cyclotomic n V
  have hFmonic : F.Monic := by
    exact Polynomial.cyclotomic.monic n V
  have hFroot :
      (F.map ((algebraMap K L).comp V.subtype)).eval (a : L) = 0 := by
    change Polynomial.eval ζ
      ((cyclotomic n V).map ((algebraMap K L).comp V.subtype)) = 0
    rw [map_cyclotomic]
    exact hζ.isRoot_cyclotomic hn
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  have hFreduction :
      (F.map (IsLocalRing.residue V)).Separable := by
    simpa [F, k] using Polynomial.separable_cyclotomic n k
  exact
    finiteUnramifiedExtension_of_primitive_separable_integral_model
      vK vL hExt hhens a F hFmonic hFroot hFreduction hζgen

/-- the unramified cyclotomic theorem(i), degree calculation upstairs.

The integral minimal polynomial of `ζ` has irreducible reduction by the
Hensel step of the factor-lifting criterion.  That reduction is an irreducible factor of
the `n`-th cyclotomic polynomial over the finite residue field, so all of its
irreducible factors have degree `ord_n(p^r)`. -/
theorem padicCyclotomicUnramified_finrank_eq_residueDegree
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring vK))]
    (hk : Fintype.card (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring vK)) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    Module.finrank K L =
      padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let k := IsLocalRing.ResidueField V
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : Module V L := algVL.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : IsFractionRing V K := by
    change IsFractionRing Vv K
    have hfr : IsFractionRing Vv.valuation.valuationSubring K :=
      (Valuation.valuationSubring.integers
        (v := Vv.valuation)).isFractionRing
    rw [Vv.valuationSubring_valuation] at hfr
    exact hfr
  let : IsIntegrallyClosed V := by
    change IsIntegrallyClosed Vv
    infer_instance
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζIntegralV : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζIntegralK : IsIntegral K ζ :=
    Algebra.IsIntegral.isIntegral (R := K) ζ
  let G : V[X] := minpoly V ζ
  let qbar : k[X] := G.map (IsLocalRing.residue V)
  have hGmonic : G.Monic := minpoly.monic hζIntegralV
  have hGfield : G.map (algebraMap V K) = minpoly K ζ := by
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' K hζIntegralV).symm
  have hGirreducible : Irreducible (G.map (algebraMap V K)) := by
    rw [hGfield]
    exact minpoly.irreducible hζIntegralK
  have hGdvd : G ∣ cyclotomic n V := by
    apply minpoly.isIntegrallyClosed_dvd hζIntegralV
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change
      ((cyclotomic n V).map ((algebraMap K L).comp V.subtype)).eval ζ = 0
    rw [map_cyclotomic]
    exact hζ.isRoot_cyclotomic hn
  have hqDvd : qbar ∣ cyclotomic n k := by
    rcases hGdvd with ⟨H, hH⟩
    refine ⟨H.map (IsLocalRing.residue V), ?_⟩
    rw [← map_cyclotomic n (IsLocalRing.residue V), hH,
      Polynomial.map_mul]
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  have hqSep : qbar.Separable :=
    (Polynomial.separable_cyclotomic n k).of_dvd hqDvd
  have hhensV : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty Vv := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      Vv.valuation.valuationSubring at hhens
    rw [Vv.valuationSubring_valuation] at hhens
    exact hhens
  have hqIrreducible : Irreducible qbar :=
    irreducible_residue_of_irreducible_of_separable_of_henselian
      Vv hhensV hGmonic hGirreducible hqSep
  have hfieldDegree :
      Module.finrank K L = (minpoly K ζ).natDegree := by
    have hAdjoin :
        IntermediateField.adjoin K ({ζ} : Set L) =
          (⊤ : IntermediateField K L) :=
      (IntermediateField.adjoin_eq_top_iff).2 hζgen
    calc
      Module.finrank K L = Module.finrank K
          (IntermediateField.adjoin K ({ζ} : Set L)) := by
        rw [hAdjoin]
        simp
      _ = (minpoly K ζ).natDegree :=
        IntermediateField.adjoin.finrank hζIntegralK
  have hqDegree : qbar.natDegree = Module.finrank K L := by
    calc
      qbar.natDegree = G.natDegree :=
        hGmonic.natDegree_map (IsLocalRing.residue V)
      _ = (G.map (algebraMap V K)).natDegree := by
        rw [Polynomial.natDegree_map_eq_of_injective
          (show Function.Injective (algebraMap V K) from
            IsFractionRing.injective V K)]
      _ = (minpoly K ζ).natDegree := by rw [hGfield]
      _ = Module.finrank K L := hfieldDegree.symm
  rw [← hqDegree]
  exact
    Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible
      (p := p) (f := r) hk hpn hqDvd hqIrreducible

/-- The canonical reduction homomorphism on Galois groups is injective for
the prime-to-residue-characteristic cyclotomic extension.  If two
automorphisms have the same residue action, their images of `ζ` are simple
roots of the cyclotomic polynomial with the same residue, hence are equal by
Hensel uniqueness; `ζ` generates the field. -/
theorem padicCyclotomicUnramified_galToResidueGal_injective
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Function.Injective (padicCyclotomicUnramified_galToResidueGal vK vL hExt hhens) := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : Module V L := algVL.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζIntegral : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζmem : ζ ∈ W := by
    rw [hclosure]
    exact hζIntegral
  let a : W := ⟨ζ, hζmem⟩
  let F : W[X] := cyclotomic n W
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  let : NeZero (n : ell) := by
    refine ⟨?_⟩
    intro hzero
    apply hnCast
    apply (algebraMap k ell).injective
    calc
      algebraMap k ell (n : k) = (n : ell) := map_natCast _ n
      _ = 0 := hzero
      _ = algebraMap k ell 0 := (map_zero _).symm
  intro σ τ hστ
  let bσ : W :=
    padicCyclotomicUnramified_galIntegerRingEquiv vK vL hExt hhens σ a
  let bτ : W :=
    padicCyclotomicUnramified_galIntegerRingEquiv vK vL hExt hhens τ a
  have hresEq : IsLocalRing.residue W bσ = IsLocalRing.residue W bτ := by
    have happ := congrArg
      (fun g : Gal(ell/k) ↦ g (IsLocalRing.residue W a)) hστ
    change padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens σ
        (IsLocalRing.residue W a) =
      padicCyclotomicUnramified_galResidueAlgEquiv vK vL hExt hhens τ
        (IsLocalRing.residue W a) at happ
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue,
      padicCyclotomicUnramified_galResidueAlgEquiv_residue] at happ
    exact happ
  have hσPrimitive : IsPrimitiveRoot (σ ζ) n :=
    hζ.map_of_injective σ.injective
  have hτPrimitive : IsPrimitiveRoot (τ ζ) n :=
    hζ.map_of_injective τ.injective
  have hσRoot : F.IsRoot bσ := by
    apply W.subtype_injective
    change W.subtype (F.eval bσ) = W.subtype 0
    rw [← Polynomial.eval_map_apply]
    simpa [F, bσ] using hσPrimitive.isRoot_cyclotomic hn
  have hτRoot : F.IsRoot bτ := by
    apply W.subtype_injective
    change W.subtype (F.eval bτ) = W.subtype 0
    rw [← Polynomial.eval_map_apply]
    simpa [F, bτ] using hτPrimitive.isRoot_cyclotomic hn
  have hτResidueRoot :
      (cyclotomic n ell).IsRoot (IsLocalRing.residue W bτ) := by
    have hmap := hτRoot.map (f := IsLocalRing.residue W)
    simpa [F] using hmap
  have hderivResidueNe :
      IsLocalRing.residue W (F.derivative.eval bτ) ≠ 0 := by
    have hsep := Polynomial.separable_cyclotomic n ell
    have hne :
        (cyclotomic n ell).derivative.eval
            (IsLocalRing.residue W bτ) ≠ 0 := by
      simpa [Polynomial.IsRoot.def] using
        hsep.eval₂_derivative_ne_zero (RingHom.id ell)
          (Polynomial.IsRoot.def.mp hτResidueRoot)
    have hcompat :
        IsLocalRing.residue W (F.derivative.eval bτ) =
          (cyclotomic n ell).derivative.eval
            (IsLocalRing.residue W bτ) := by
      calc
        IsLocalRing.residue W (F.derivative.eval bτ) =
            (F.derivative.map (IsLocalRing.residue W)).eval
              (IsLocalRing.residue W bτ) := by
          exact (Polynomial.eval_map_apply
            (f := IsLocalRing.residue W) (p := F.derivative) bτ).symm
        _ = (cyclotomic n ell).derivative.eval
              (IsLocalRing.residue W bτ) := by
          rw [← Polynomial.derivative_map, show
            F.map (IsLocalRing.residue W) =
              cyclotomic n (IsLocalRing.ResidueField W) by simp [F]]
    rw [hcompat]
    exact hne
  have hderivUnit : IsUnit (F.derivative.eval bτ) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hderivResidueNe
  have hbEq : bσ = bτ :=
    padicCyclotomicUnramified_eq_of_roots_of_residue_eq_of_derivative_isUnit
      hτRoot hσRoot hresEq hderivUnit
  have hζEq : σ ζ = τ ζ := by
    have hval := congrArg Subtype.val hbEq
    simpa [bσ, bτ] using hval
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ Algebra.adjoin K ({ζ} : Set L) := by
    rw [hζgen]
    trivial
  exact Algebra.adjoin_induction
    (R := K) (A := L) (s := ({ζ} : Set L))
    (p := fun x _ ↦ σ x = τ x)
    (fun y hy ↦ by
      have hyζ : y = ζ := by simpa using hy
      subst y
      exact hζEq)
    (fun y ↦ by
      change σ (algebraMap K L y) = τ (algebraMap K L y)
      rw [σ.commutes, τ.commutes])
    (fun x y _ _ hx hy ↦ by
      rw [map_add, map_add, hx, hy])
    (fun x y _ _ hx hy ↦ by
      rw [map_mul, map_mul, hx, hy]) hx

/-- the unramified cyclotomic theorem(ii), canonical Galois comparison: the reduction
homomorphism is bijective.  Injectivity is the Hensel-uniqueness argument
above; surjectivity follows by comparing the two genuine Galois group
cardinalities with the equal field and residue degrees from part (i). -/
theorem padicCyclotomicUnramified_galToResidueGal_bijective
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Function.Bijective
      (padicCyclotomicUnramified_galToResidueGal vK vL hExt hhens) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let : FiniteDimensional k ell :=
    padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
  let : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  let : Finite ell := Module.finite_of_finite k
  have hUnramified : FiniteUnramifiedExtension vK vL hExt :=
    padicCyclotomicUnramified_finiteUnramifiedExtension
      vK vL hExt hhens hk hpn hζ hζgen
  let : Algebra.IsSeparable K L :=
    finiteUnramifiedExtension_isSeparable_of_henselian
      vK vL hExt hhens hUnramified
  let : IsGalois K L :=
    padicCyclotomicUnramified_isGalois_of_primitiveRoot_adjoin_eq_top
      (padicCyclotomicUnramified_order_pos hpn) hζ hζgen
  let : IsGalois k ell := inferInstance
  let : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let : Fintype Gal(ell/k) := Fintype.ofFinite Gal(ell/k)
  apply (Fintype.bijective_iff_injective_and_card
    (padicCyclotomicUnramified_galToResidueGal vK vL hExt hhens)).2
  refine ⟨padicCyclotomicUnramified_galToResidueGal_injective
    vK vL hExt hhens hk hpn hζ hζgen, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
  exact hUnramified.2.trans
    (padicCyclotomicUnramified_exponentialResidueDegree_eq_finrank vK vL hExt)

/-- the unramified cyclotomic theorem(ii): the canonical multiplicative equivalence obtained
from reduction of valuation-ring automorphisms. -/
noncomputable def padicCyclotomicUnramified_galEquivResidueGal
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Gal(L/K) ≃*
      Gal(padicCyclotomicUnramifiedResidueField vL / padicCyclotomicUnramifiedResidueField vK) := by
  letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) :=
    padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  exact MulEquiv.ofBijective
    (padicCyclotomicUnramified_galToResidueGal vK vL hExt hhens)
    (padicCyclotomicUnramified_galToResidueGal_bijective
      vK vL hExt hhens hk hpn hζ hζgen)

/-- The arithmetic Frobenius in `Gal(K(ζ)/K)`, defined canonically as the
inverse image of finite-field Frobenius under the reduction equivalence. -/
noncomputable def padicCyclotomicUnramifiedArithmeticFrobenius
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    Gal(L/K) := by
  let k := padicCyclotomicUnramifiedResidueField vK
  let ell := padicCyclotomicUnramifiedResidueField vL
  letI : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  letI : FiniteDimensional k ell :=
    padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
  letI : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  exact
    (padicCyclotomicUnramified_galEquivResidueGal
      vK vL hExt hhens hk hpn hζ hζgen).symm
        (FiniteField.frobeniusAlgEquivOfAlgebraic k ell)

@[simp]
theorem padicCyclotomicUnramified_galEquivResidueGal_arithmeticFrobenius
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    letI : FiniteDimensional (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
    letI : Algebra.IsAlgebraic (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      Algebra.IsAlgebraic.of_finite _ _
    padicCyclotomicUnramified_galEquivResidueGal
        vK vL hExt hhens hk hpn hζ hζgen
        (padicCyclotomicUnramifiedArithmeticFrobenius
          vK vL hExt hhens hk hpn hζ hζgen) =
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) := by
  simp [padicCyclotomicUnramifiedArithmeticFrobenius]









end LocalCyclotomicUnramified

section LocalCyclotomicEndpoint

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]





end LocalCyclotomicEndpoint

section IntegralInclusion

variable {R : Type u} {L : Type v}
variable [CommRing R] [Field L] [Algebra R L]



end IntegralInclusion

end Valuations
end AlgebraicNumberTheory

end
