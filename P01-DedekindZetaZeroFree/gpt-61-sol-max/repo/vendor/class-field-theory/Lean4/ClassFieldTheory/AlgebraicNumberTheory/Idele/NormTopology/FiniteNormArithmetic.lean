module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Finite-place arithmetic of idele norms

This file relates the finite components of the ordinary idele norm to local
orders and positive prime norms. It also proves the degree formula for the
finite positive norm under scalar extension.
-/

open scoped BigOperators NNReal NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations
open Function

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

private theorem finprod_over_fibers
    {α β G : Type*} [CommMonoid G]
    (g : α → β) (f : α → G)
    (hf : HasFiniteMulSupport f) :
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
      ∏ᶠ x : α, f x := by
  classical
  let s := hf.toFinset
  have hFiber (b : β) :
      (∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ x ∈ s with g x = b, f x := by
    rw [finprod_eq_prod_of_mulSupport_subset
      (fun x : {x : α // g x = b} => f x.1)
      (s := s.subtype fun x => g x = b)]
    · simp only [Finset.prod_subtype_eq_prod_filter]
    · intro x hx
      change x ∈ s.subtype (fun x => g x = b)
      change f x.1 ≠ 1 at hx
      exact Finset.mem_subtype.mpr (hf.mem_toFinset.2 hx)
  calc
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ᶠ b : β,
          ∏ x ∈ s with g x = b, f x :=
      finprod_congr hFiber
    _ = ∏ x ∈ s, f x := by
      rw [finprod_eq_prod_of_mulSupport_subset _
        (s.mulSupport_of_fiberwise_prod_subset_image f g)]
      exact
        Finset.prod_fiberwise_of_maps_to
          (t := s.image g)
          (fun x hx => Finset.mem_image_of_mem g hx) f
    _ = ∏ᶠ x : α, f x :=
      (finprod_eq_prod f hf).symm

/-- A finite idele norm is its finitely supported product of local prime
norms raised to the corresponding local orders. -/
private theorem finiteAbsoluteNorm_eq_finprod
    (a : FiniteIdeleGroup K) :
    FiniteIdeleGroup.absoluteNorm a =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        FiniteIdeleGroup.primeNorm v ^
          (FiniteIdeleGroup.localOrder v (a v)).toAdd := by
  classical
  let e := (FiniteIdeleGroup.valuationVector a).toAdd
  have heval (v : HeightOneSpectrum (𝓞 K)) :
      e v =
        (FiniteIdeleGroup.localOrder v (a v)).toAdd := by
    simpa only [e] using
      FiniteIdeleGroup.valuationVector_apply a v
  have hsupport :
      mulSupport
          (fun v : HeightOneSpectrum (𝓞 K) =>
            FiniteIdeleGroup.primeNorm v ^ e v) ⊆
        e.support := by
    intro v hv
    by_contra hmem
    have hev : e v = 0 :=
      Finsupp.notMem_support_iff.mp hmem
    exact hv (by simp [hev])
  rw [FiniteIdeleGroup.absoluteNorm_apply]
  change
    e.prod
        (fun v n => FiniteIdeleGroup.primeNorm v ^ n) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        FiniteIdeleGroup.primeNorm v ^
          (FiniteIdeleGroup.localOrder v (a v)).toAdd
  calc
    e.prod
          (fun v n => FiniteIdeleGroup.primeNorm v ^ n) =
        ∏ v ∈ e.support,
          FiniteIdeleGroup.primeNorm v ^ e v := rfl
    _ =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          FiniteIdeleGroup.primeNorm v ^ e v :=
      (finprod_eq_prod_of_mulSupport_subset _ hsupport).symm
    _ =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          FiniteIdeleGroup.primeNorm v ^
            (FiniteIdeleGroup.localOrder v (a v)).toAdd :=
      finprod_congr fun v => by rw [heval]

omit [FiniteDimensional K L] in
/-- The positive prime norm upstairs is the inertia-degree power of the
positive prime norm below. -/
theorem primeNorm_above
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀}) :
    FiniteIdeleGroup.primeNorm W.1 =
      FiniteIdeleGroup.primeNorm v₀ ^
        W.1.asIdeal.inertiaDeg (𝓞 K) := by
  let : W.1.asIdeal.LiesOver v₀.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  apply Units.ext
  apply NNReal.eq
  change
    (Ideal.absNorm W.1.asIdeal : ℝ) =
      (Ideal.absNorm v₀.asIdeal : ℝ) ^
        W.1.asIdeal.inertiaDeg (𝓞 K)
  exact_mod_cast
    (Ideal.absNorm_pow_inertiaDeg
      v₀.asIdeal W.1.asIdeal).symm

/-- An integer power of a commutative-group element carries a finite sum
of exponents to the corresponding finite product. -/
private theorem zpow_finset_sum
    {G : Type*} [CommGroup G]
    {ι : Type*} (g : G) (s : Finset ι) (e : ι → ℤ) :
    g ^ (∑ i ∈ s, e i) =
      ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [hi, ih, zpow_add]

/-- The order of a finite component of the ordinary idele norm is the sum
of the upstairs orders weighted by their inertia degrees. -/
theorem finiteComponentOrder_norm
    (v₀ : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    letI : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    letI : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K L v₀ W).toAlgebra
    (FiniteIdeleGroup.localOrder v₀
      (finiteComponent v₀ (norm K L a))).toAdd =
      ∑ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          (FiniteIdeleGroup.localOrder W.1
            (finiteComponent W.1 a)).toAdd := by
  classical
  dsimp only
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v₀
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀},
      Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K L v₀ W).toAlgebra
  have hcomponent :
      finiteComponent v₀ (norm K L a) =
        ∏ W : {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := K) W = v₀},
          LocalFieldTheory.normUnits
            (v₀.adicCompletion K) (W.1.adicCompletion L)
            (finiteComponent W.1 a) := by
    simpa only using
      finiteComponent_norm_eq_prod (K := K) (L := L) v₀ a
  rw [hcomponent]
  rw [map_prod]
  change
    (∑ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
      (FiniteIdeleGroup.localOrder v₀
        (LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a))).toAdd) =
      ∑ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          (FiniteIdeleGroup.localOrder W.1
            (finiteComponent W.1 a)).toAdd
  apply Finset.sum_congr rfl
  intro W _
  exact
    FiniteIdeleGroup.localOrder_normUnits
      K L v₀ W (finiteComponent W.1 a)

/-- The finite positive idele norm is preserved by the ordinary idele
norm. -/
theorem finiteAbsoluteNorm_norm
    (a : IdeleGroup L) :
    FiniteIdeleGroup.absoluteNorm (norm K L a).2 =
      FiniteIdeleGroup.absoluteNorm a.2 := by
  classical
  rw [finiteAbsoluteNorm_eq_finprod
      (K := K) ((norm K L a).2),
    finiteAbsoluteNorm_eq_finprod
      (K := L) a.2]
  have hfinite :
      HasFiniteMulSupport
        (fun W : HeightOneSpectrum (𝓞 L) =>
          FiniteIdeleGroup.primeNorm W ^
            (FiniteIdeleGroup.localOrder W
              (finiteComponent W a)).toAdd) := by
    refine
      ((FiniteIdeleGroup.valuationVector a.2).toAdd.support.finite_toSet).subset
        ?_
    intro W hW
    by_contra hmem
    have hzero :
      (FiniteIdeleGroup.localOrder W
          (finiteComponent W a)).toAdd = 0 := by
      change (FiniteIdeleGroup.valuationVector a.2).toAdd W = 0
      exact Finsupp.notMem_support_iff.mp hmem
    apply hW
    change FiniteIdeleGroup.primeNorm W ^
      (FiniteIdeleGroup.localOrder W (finiteComponent W a)).toAdd = 1
    rw [hzero, zpow_zero]
  calc
    (∏ᶠ v₀ : HeightOneSpectrum (𝓞 K),
        FiniteIdeleGroup.primeNorm v₀ ^
          (FiniteIdeleGroup.localOrder v₀
            (finiteComponent v₀ (norm K L a))).toAdd) =
        ∏ᶠ v₀ : HeightOneSpectrum (𝓞 K),
          ∏ᶠ W : {W : HeightOneSpectrum (𝓞 L) //
              _root_.finitePlaceBelow (K := K) W = v₀},
            FiniteIdeleGroup.primeNorm W.1 ^
              (FiniteIdeleGroup.localOrder W.1
                (finiteComponent W.1 a)).toAdd := by
      apply finprod_congr
      intro v₀
      let vK := HeightOneSpectrum.adicAbv K v₀
      let hvK : vK.IsNontrivial :=
        RayClass.adicAbv_isNontrivial v₀
      let :=
        completionTensorDecomposition_extensionFintype
          (K := K) (L := L) vK hvK
      let eAbove :=
        finitePlaceExtensionEquivAbove
          (K := K) (L := L) v₀
      let : Fintype {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀} :=
        Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
      let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
          Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
        fun W =>
          (finitePlaceAdicCompletionMap
            K L v₀ W).toAlgebra
      calc
        FiniteIdeleGroup.primeNorm v₀ ^
              (FiniteIdeleGroup.localOrder v₀
                (finiteComponent v₀ (norm K L a))).toAdd =
            FiniteIdeleGroup.primeNorm v₀ ^
              (∑ W : {W : HeightOneSpectrum (𝓞 L) //
                    _root_.finitePlaceBelow (K := K) W = v₀},
                (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
                  (FiniteIdeleGroup.localOrder W.1
                    (finiteComponent W.1 a)).toAdd) := by
          rw [finiteComponentOrder_norm K L v₀ a]
        _ =
            ∏ W : {W : HeightOneSpectrum (𝓞 L) //
                _root_.finitePlaceBelow (K := K) W = v₀},
              FiniteIdeleGroup.primeNorm v₀ ^
                ((W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
                  (FiniteIdeleGroup.localOrder W.1
                    (finiteComponent W.1 a)).toAdd) := by
          simpa using
            zpow_finset_sum
              (FiniteIdeleGroup.primeNorm v₀)
              Finset.univ
              (fun W : {W : HeightOneSpectrum (𝓞 L) //
                  _root_.finitePlaceBelow (K := K) W = v₀} =>
                (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
                  (FiniteIdeleGroup.localOrder W.1
                    (finiteComponent W.1 a)).toAdd)
        _ =
            ∏ W : {W : HeightOneSpectrum (𝓞 L) //
                _root_.finitePlaceBelow (K := K) W = v₀},
              FiniteIdeleGroup.primeNorm W.1 ^
                (FiniteIdeleGroup.localOrder W.1
                  (finiteComponent W.1 a)).toAdd := by
          apply Finset.prod_congr rfl
          intro W _
          rw [zpow_mul, zpow_natCast,
            ← primeNorm_above (K := K) (L := L) v₀ W]
        _ =
            ∏ᶠ W : {W : HeightOneSpectrum (𝓞 L) //
                _root_.finitePlaceBelow (K := K) W = v₀},
              FiniteIdeleGroup.primeNorm W.1 ^
                (FiniteIdeleGroup.localOrder W.1
                  (finiteComponent W.1 a)).toAdd :=
          (finprod_eq_prod_of_fintype _).symm
    _ =
        ∏ᶠ W : HeightOneSpectrum (𝓞 L),
          FiniteIdeleGroup.primeNorm W ^
            (FiniteIdeleGroup.localOrder W
              (finiteComponent W a)).toAdd :=
      finprod_over_fibers
        (_root_.finitePlaceBelow (K := K))
        (fun W : HeightOneSpectrum (𝓞 L) =>
          FiniteIdeleGroup.primeNorm W ^
            (FiniteIdeleGroup.localOrder W
              (finiteComponent W a)).toAdd)
        hfinite







































































































































end IdeleGroup

end
