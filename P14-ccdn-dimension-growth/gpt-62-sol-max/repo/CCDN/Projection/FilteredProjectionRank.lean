/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ImageFractionField
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.PolynomialComparison
import CCDN.Hilbert.ProperHilbertDimension
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The filtered Hilbert multiplicity of a finite linear projection is multiplied by
its function-field rank. A basis over the image field compares the filtered pieces in
both directions after clearing finitely many denominators. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Dimension is preserved and the degree is multiplied by the generic rank
in a finite linear projection with filtered generators. -/
theorem filtered_projection_rank
    {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]
    [Fintype σ] [Fintype τ] [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    [Algebra (MvPolynomial τ K ⧸ I) F] [IsScalarTower K (MvPolynomial τ K ⧸ I) F]
    [IsFractionRing (MvPolynomial τ K ⧸ I) F]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hfg : HasFilteredGenerators I (projectionCoordinateMap I a)) :
    let E := projectionImageField (F := F) I a
    let J := RingHom.ker (projectionCoordinateMap I a)
    Module.Finite E F ∧ (filteredHilbertPolynomial J).natDegree = (filteredHilbertPolynomial I).natDegree ∧
      (filteredHilbertPolynomial I).leadingCoeff =
        (Module.finrank E F : ℚ) * (filteredHilbertPolynomial J).leadingCoeff := by
  classical
  let A := MvPolynomial τ K ⧸ I
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  let R := MvPolynomial σ K ⧸ J
  let φ := Ideal.kerLiftAlg ψ
  let E := projectionImageField (F := F) I a
  let η := IsScalarTower.toAlgHom K A F
  let ν := projectionFieldMap (F := F) I a
  let ρ := Ideal.Quotient.liftₐ J ν fun p hp =>
    (RingHom.mem_ker (f := ν.toRingHom)).mp (projectionFieldMap_ker (F := F) I a |>.symm ▸ hp)
  have hη : Function.Injective η := IsFractionRing.injective A F
  have hρ (p : R) : (ρ p : F) = η (φ p) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    exact coe_projectionFieldMap I a p
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective ψ
  have hρi : Function.Injective ρ := fun p q h =>
    hφ (hη ((hρ p).symm.trans ((congrArg Subtype.val h).trans (hρ q))))
  let : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let : Algebra R A := φ.toRingHom.toAlgebra
  let : Algebra R E := ρ.toRingHom.toAlgebra
  let : Algebra R F := (η.comp φ).toRingHom.toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R E F := IsScalarTower.of_algebraMap_eq fun p => (hρ p).symm
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hφ
  let : IsFractionRing R E := projectionImageField_isFractionRing I a ρ hρi (Ideal.Quotient.mkₐ K J) rfl
  let : Algebra.IsIntegral R A := ⟨hfg.isIntegral.kerLift⟩
  let : Algebra.IsAlgebraic R A := ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let : Module.Finite R A := Algebra.IsIntegral.finite
  let : Module.Finite E F := Module.Finite.equiv
    (Algebra.IsAlgebraic.isBaseChange_of_isFractionRing R A E F).equiv
  refine ⟨inferInstance, ?_⟩
  let r := Module.finrank E F
  let π := η ∘ Ideal.Quotient.mk I
  have hspan : Submodule.span E (Set.range π) = ⊤ := by
    change Submodule.span E (Set.range ((algebraMap A F) ∘ Ideal.Quotient.mk I)) = ⊤
    rw [Ideal.Quotient.mk_surjective.range_comp]
    simpa using span_eq_top_of_isLocalizedModule E (nonZeroDivisors R)
      (IsScalarTower.toAlgHom R A F).toLinearMap (v := Set.univ) (by simp)
  obtain ⟨ι, h, _, hsp, hi⟩ := exists_linearIndependent' E π
  have := hi.finite
  let : Fintype ι := Fintype.ofFinite ι
  let b := Module.Basis.mk hi (hsp.trans hspan).ge
  have hcard : Fintype.card ι = r := (Module.finrank_eq_card_basis b).symm
  have hb (i : ι) : b i = π (h i) := Module.Basis.mk_apply _ _ _
  let D : ℕ := Finset.univ.sup (fun i : ι => (h i).totalDegree)
  let V (N : ℕ) := filteredCoordinateSpace J N
  let U (N : ℕ) := filteredCoordinateSpace I N
  let L (N : ℕ) : (ι → V N) →ₗ[K] F :=
    (b.equivFun.symm.restrictScalars K).toLinearMap.comp
      (LinearMap.pi fun i => ρ.toLinearMap.comp ((V N).subtype.comp (LinearMap.proj i)))
  have hL (N) (v : ι → V N) : L N v = b.equivFun.symm (fun i => ρ (v i).val) := rfl
  have hLrank (N) : Module.finrank K (LinearMap.range (L N)) = r * Module.finrank K (V N) := by
    rw [LinearMap.finrank_range_of_inj]
    · simp [Module.finrank_pi_fintype, hcard]
    · intro v u he
      have h := b.equivFun.symm.injective (by simpa only [hL] using he)
      exact funext fun i => Subtype.ext (hρi (congrFun h i))
  have hlow (N) : r * Module.finrank K (V N) ≤ Module.finrank K (U (N + D)) := by
    have hmem : LinearMap.range (L N) ≤ (U (N + D)).map η.toLinearMap := by
      rintro _ ⟨v, rfl⟩
      refine ⟨∑ i, φ (v i).val * Ideal.Quotient.mk I (h i), (U (N + D)).sum_mem (fun i _ => ?_), ?_⟩
      · exact filteredCoordinateSpace_mul_mem I (projectionKerLift_filtered I a ha (v i).property)
          (mem_filteredCoordinateSpace.mpr ⟨h i, Finset.le_sup (f := fun i : ι => (h i).totalDegree) (Finset.mem_univ i), rfl⟩)
      · simp [hL, Module.Basis.equivFun_symm_apply, hb, π, Algebra.smul_def, hρ]
    rw [← hLrank N, (Submodule.equivMapOfInjective η.toLinearMap hη (U (N + D))).finrank_eq]
    exact Submodule.finrank_mono hmem
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun z : s × ι => (b.repr (η z.1.val)) z.2)
  choose p hp using fun z : s × ι => show ∃ p,
      ρ (Ideal.Quotient.mk J p) = ρ c * (b.repr (η z.1.val)) z.2 from by
    obtain ⟨y, hy⟩ := hc z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨p, hy⟩
  let C : ℕ := Finset.univ.sup fun z : s × ι => (p z).totalDegree
  let T := (LinearMap.mulLeft K (η (φ c))).comp η.toLinearMap
  have hT : Function.Injective T :=
    (mul_right_injective₀ (map_ne_zero_iff (η.comp φ) (hη.comp hφ) |>.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp c.property))).comp hη
  have hupp (N) : Module.finrank K (U N) ≤ r * Module.finrank K (V (N + C)) := by
    have hmem : (U N).map T ≤ LinearMap.range (L (N + C)) := by
      refine Submodule.map_le_iff_le_comap.mpr (hs N _ (fun g hg z hz => ?_))
      let v : ι → V (N + C) := fun i =>
        ⟨Ideal.Quotient.mk J (g * p (⟨z, hz⟩, i)),
          mem_filteredCoordinateSpace.mpr ⟨_, (totalDegree_mul _ _).trans
            (add_le_add hg (Finset.le_sup (f := fun z : s × ι => (p z).totalDegree) (Finset.mem_univ _))), rfl⟩⟩
      refine ⟨v, b.equivFun.injective ?_⟩
      have he : T (ψ g * z) = (ρ c * ρ (Ideal.Quotient.mk J g)) • η z := by
        change η (φ c) * η (ψ g * z) = _
        simp only [Algebra.smul_def, map_mul, mul_assoc]
        change _ = (ρ c : F) * ((ρ (Ideal.Quotient.mk J g) : F) * η z)
        rw [hρ, hρ, Ideal.kerLiftAlg_mk]
      rw [hL, b.equivFun.apply_symm_apply, he, map_smul]
      funext i
      change ρ (Ideal.Quotient.mk J (g * p _)) = _
      simp only [Module.Basis.equivFun_apply, map_mul, hp, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← hLrank, (Submodule.equivMapOfInjective T hT (U N)).finrank_eq]
    exact Submodule.finrank_mono hmem
  have hI : I ≠ ⊤ := Ideal.IsPrime.ne_top ‹I.IsPrime›
  have hJ := RingHom.ker_ne_top ψ.toRingHom
  have hr : 0 < r := Module.finrank_pos
  have h₁ := filteredHilbertPolynomial_compare J I hJ hI hr one_pos D (by simpa [V, U] using hlow)
  have h₂ := filteredHilbertPolynomial_compare I J hI hJ one_pos hr C (by simpa [V, U] using hupp)
  have hd := le_antisymm h₁.1 h₂.1
  exact ⟨hd, le_antisymm (by simpa using h₂.2 hd.symm) (by simpa using h₁.2 hd)⟩

/-- A filtered normalization has function-field rank equal to the multiplicity. -/
theorem filtered_normalization_rank
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F] [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (a : Fin (m + 1) → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hfg : HasFilteredGenerators I (projectionCoordinateMap I a))
    (hi : Function.Injective (projectionCoordinateMap I a)) {d : ℕ}
    (hdegree : HasProjectiveDimensionDegree I m d) :
    let E := projectionImageField (F := F) I a
    Module.Finite E F ∧ Module.finrank E F = d := by
  obtain ⟨hfin, _, h⟩ := filtered_projection_rank (F := F) I a ha hfg
  rw [hdegree.leadingCoeff_eq, (RingHom.injective_iff_ker_eq_bot _).mp hi,
    filteredHilbertPolynomial_bot, Polynomial.leadingCoeff_preHilbertPoly,
    Fintype.card_fin, ← div_eq_mul_inv, div_left_inj' (by positivity)] at h
  exact ⟨hfin, by exact_mod_cast h.symm⟩

/-- Filtered linear elimination preserves the dimension and cannot increase multiplicity. -/
theorem filtered_projection_dimension_degree_le
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hfg : HasFilteredGenerators I (projectionCoordinateMap I a)) {m d : ℕ}
    (hdegree : HasAffineDimensionDegree I m d) :
    ∃ e ≤ d, HasAffineDimensionDegree (RingHom.ker (projectionCoordinateMap I a)) m e := by
  let F := FractionRing (MvPolynomial τ K ⧸ I)
  obtain ⟨hfin, hdim, h⟩ := filtered_projection_rank (F := F) I a ha hfg
  let J := RingHom.ker (projectionCoordinateMap I a)
  have hdim' : (filteredHilbertPolynomial J).natDegree = m := hdim.trans hdegree.natDegree_eq
  obtain ⟨e, he, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity J (RingHom.ker_ne_top _)
  rw [hdim'] at hlc
  rw [hdegree.leadingCoeff_eq, hlc, ← mul_div_assoc, div_left_inj' (by positivity)] at h
  have hd : d = Module.finrank (projectionImageField (F := F) I a) F * e := by exact_mod_cast h
  have hp : 0 < Module.finrank (projectionImageField (F := F) I a) F := Module.finrank_pos
  exact ⟨e, hd ▸ (by simpa using Nat.mul_le_mul_right e (Nat.succ_le_of_lt hp)), hdim', hlc⟩

end
end CCDN
