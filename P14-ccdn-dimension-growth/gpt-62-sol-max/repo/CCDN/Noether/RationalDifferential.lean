/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Derivation.DifferentialRing
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! The formal derivative on a rational function field and its constant field. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

section Etale

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]

/-- Extend a derivation along an étale map by base change of Kähler differentials. -/
def etaleDerivation (d : Derivation R S S) : Derivation R T T :=
  ((KaehlerDifferential.isBaseChange_of_formallyEtale R S T).lift
    ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)).compDer (KaehlerDifferential.D R T)

@[simp] lemma etaleDerivation_algebraMap (d : Derivation R S S) (x : S) :
    etaleDerivation (T := T) d (algebraMap S T x) = algebraMap S T (d x) := by
  change ((KaehlerDifferential.isBaseChange_of_formallyEtale R S T).lift
    ((Algebra.linearMap S T).comp d.liftKaehlerDifferential))
      (KaehlerDifferential.D R T (algebraMap S T x)) = _
  rw [← KaehlerDifferential.map_D R R S T, IsBaseChange.lift_eq]
  simp [Derivation.liftKaehlerDifferential_comp_D]

end Etale

/-- The differential ring structure on an étale algebra over a differential ring. -/
@[reducible] def etaleDifferential (S T : Type*) [CommRing S] [CommRing T]
    [Algebra S T] [Differential S] [Algebra.FormallyEtale S T] : Differential T :=
  ⟨etaleDerivation (T := T) (Differential.deriv (R := S))⟩

lemma etaleDifferential_algebra (S T : Type*) [CommRing S] [CommRing T]
    [Algebra S T] [Differential S] [Algebra.FormallyEtale S T] :
    let := etaleDifferential S T
    DifferentialAlgebra S T := by
  solve_by_elim [CCDN.etaleDerivation_algebraMap]

theorem ratFuncEtale (K : Type*) [Field K] : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
attribute [local instance] ratFuncEtale

/-- Formal rational differentiation is the étale extension of polynomial differentiation. -/
@[reducible] def rationalDifferential (K : Type*) [Field K] : Differential (RatFunc K) := by
  let : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  exact ⟨(etaleDerivation (T := RatFunc K) (Polynomial.derivative' (R := K))).restrictScalars ℤ⟩

attribute [local instance] rationalDifferential
open scoped Differential

@[simp] lemma rationalDerivative_polynomial {K : Type*} [Field K] (p : K[X]) :
    (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) p.derivative :=
  etaleDerivation_algebraMap (T := RatFunc K) Polynomial.derivative' p

end
end CCDN
