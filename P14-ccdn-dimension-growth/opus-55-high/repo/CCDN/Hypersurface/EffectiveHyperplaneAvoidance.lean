/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hypersurface.UniversalHyperplaneRestriction
import CCDN.Noether.UniversalHomogeneousForm
import CCDN.Hypersurface.CoefficientwiseSubstitution
import CCDN.Hypersurface.GoodHyperplaneReindex
import CCDN.Noether.UniversalNoetherForms

/-! Effective hyperplane avoidance from the universal Noether forms.
The polynomial is nonzero by a constructed geometrically good section.
It is homogeneous of degree d(d²−1)+1 and vanishes on every bad graph
section, as well as on the omitted chart. -/

namespace CCDN
section
open MvPolynomial
universe u

section
variable {K σ : Type*} [Fintype σ]

lemma scaledHyperplaneRestriction_not_absolutely_irreducible
    [Field K] (A : Option σ → K) (hA : A none ≠ 0)
    {d : ℕ} {f : MvPolynomial (Option σ) K} (hf : f.IsHomogeneous d)
    (hbad : ¬Irreducible (map (algebraMap K (AlgebraicClosure K))
      (graphHyperplaneRestriction (fun i => -A (some i) / A none) f))) :
    ¬Irreducible (map (algebraMap K (AlgebraicClosure K))
      (scaledHyperplaneRestriction A f)) := by
  rw [(show scaledHyperplaneRestriction A f =
        C (A none ^ d) * graphHyperplaneRestriction (fun i => -A (some i) / A none) f by
      let v : Option σ → MvPolynomial σ K :=
        fun i => Option.elim i (∑ j, C (-A (some j) / A none) * X j) X
      have hv : (fun i => Option.elim i (-(∑ j, C (A (some j)) * X j))
          (fun j => C (A none) * X j)) = (C (A none) : MvPolynomial σ K) • v := by
        funext i
        cases i with
        | none =>
          change -(∑ j, C (A (some j)) * X j) =
            C (A none) * (∑ j, C (-A (some j) / A none) * X j)
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [← mul_assoc, ← map_mul]
          have he : A none * (-A (some j) / A none) = -A (some j) := by field_simp
          rw [he, map_neg, neg_mul]
        | some j => rfl
      change eval₂ C _ f = C (A none ^ d) * eval₂ C v f
      rw [hv, eval₂_eq_eval_map, homogeneous_eval_smul (hf.map C), ← eval₂_eq_eval_map,
        ← map_pow]), map_mul, map_C]
  have hu : IsUnit (C ((algebraMap K (AlgebraicClosure K)) (A none ^ d)) :
      MvPolynomial σ (AlgebraicClosure K)) :=
    (isUnit_iff_ne_zero.mpr
      (by simpa using
        (algebraMap K (AlgebraicClosure K)).injective.ne (pow_ne_zero d hA))).map C
  exact fun hi => hbad ((irreducible_isUnit_mul hu).mp hi)

end

/-- A corrected form of CCDN Lemma 4.3.7 for degree `d ≥ 2`, in explicit hyperplane coordinates:
for an absolutely irreducible integer form `f` of degree `d`, there is a nonzero integer form `G`
in the hyperplane coefficients, homogeneous of degree `d * (d ^ 2 - 1) + 1` and of total degree at
most `(4 + n) * d * (d ^ 2 - 1)`, that vanishes at every coefficient vector `A` over any field,
either with `A₀ = 0` or for which the restriction of `f` to the hyperplane `A` is not absolutely
irreducible. -/
theorem exists_effective_hyperplane_avoidance {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ G : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ,
      G ≠ 0 ∧ G.IsHomogeneous (d * (d ^ 2 - 1) + 1) ∧
      ∀ (K : Type u) [Field K] (A : Option (Option (Fin (2 + n))) → K),
        (A none ≠ 0 →
          ¬Irreducible (map (algebraMap K (AlgebraicClosure K))
            (graphHyperplaneRestriction (fun i => -A (some i) / A none)
              (map (Int.castRingHom K) f)))) →
        eval₂ (Int.castRingHom K) A G = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hdegree := hf.totalDegree (by
    intro hz
    exact hir.ne_zero (by grind))
  obtain ⟨a,ha⟩ : ∃ a : Option (Fin (2 + n)) → ℚ,
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction a (map (Int.castRingHom ℚ) f)) := by
    let e : Option (Fin (2 + n)) ≃ Fin (3 + n) :=
      (_root_.finSuccEquiv (2 + n)).symm.trans (finCongr (by omega))
    let F := rename (Equiv.optionCongr e) f
    have hFdeg : F.totalDegree = f.totalDegree := totalDegree_renameEquiv _ _
    obtain ⟨α, hgood⟩ := exists_bounded_geometrically_good_hyperplane F (by
      dsimp [AbsolutelyIrreducible]
      rw [map_rename]
      exact (MulEquiv.irreducible_iff
        (f := (renameEquiv (AlgebraicClosure ℚ) (Equiv.optionCongr e)).toMulEquiv)).mpr hir) (hFdeg ▸ (by omega))
    refine ⟨α ∘ e, ?_⟩
    have he := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (graphHyperplaneRestriction_rename e α (map (Int.castRingHom ℚ) f))
    rw [map_rename] at he
    apply (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv)).mp
    change Irreducible (rename e (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (graphHyperplaneRestriction (α ∘ e) (map (Int.castRingHom ℚ) f))))
    rw [he]
    simpa [F, map_rename] using hgood
  let q := graphHyperplaneRestriction a (map (Int.castRingHom ℚ) f)
  have hq :=
    graphHyperplaneRestriction_homogeneous a (hf.map (Int.castRingHom ℚ))
  obtain ⟨Φ,hΦ,hn⟩ := universalNoetherForms_nonvanishing k q hq ha
  let H := homogeneousCoefficientSpecialization (k + 2) (universalHyperplaneRestriction f) Φ
  let A : Option (Option (Fin (2 + n))) → ℚ :=
    fun i => Option.elim i 1 (fun j => -a j)
  have hvalue : eval₂Hom (Int.castRingHom ℚ) A H =
      homogeneousCoefficientSpecialization (k + 2) q Φ := by
    rw [homogeneousCoefficientSpecialization_map, universalHyperplaneRestriction_specialize, scaledHyperplaneRestriction_normalized]
  have hH : H ≠ 0 := by grind
  have hHhom :=
    homogeneousCoefficientSpecialization_homogeneous _ _ _ _
      (universalHyperplaneRestriction_coefficientwiseHomogeneous hf) Φ
      (universalNoetherForms_homogeneous k Φ hΦ)
  let G := X none * H
  have hG := mul_ne_zero (X_ne_zero none) hH
  refine ⟨G,hG,(by
    simpa [add_comm 1] using (isHomogeneous_X ℤ none).mul hHhom),?_⟩
  · intro K _ A hbad
    change (eval₂Hom (Int.castRingHom K) A) (X none * H) = 0
    rw [map_mul]
    have hx : eval₂Hom (Int.castRingHom K) A (X none) = A none := by simp_all
    by_cases hA : A none = 0
    · grind
    · have hh := scaledHyperplaneRestriction_not_absolutely_irreducible A hA
        (hf.map (Int.castRingHom K)) (hbad hA)
      have hz : homogeneousCoefficientSpecialization (k + 2) (scaledHyperplaneRestriction A (map (Int.castRingHom K) f)) Φ = 0 := by
        obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k Φ).mp hΦ
        let φ := algebraMap K (AlgebraicClosure K)
        have hz := ambientEuler_minor_eq_zero_of_not_irreducible k (MvPolynomial.map φ (scaledHyperplaneRestriction A (map (Int.castRingHom K) f)))
          ((scaledHyperplaneRestriction_homogeneous A (hf.map (Int.castRingHom K))).map φ) hh rows cols
        apply φ.injective
        rw [map_zero, ambientNoetherForm_specialize k (scaledHyperplaneRestriction A (map (Int.castRingHom K) f)) (scaledHyperplaneRestriction_homogeneous A (hf.map (Int.castRingHom K))) rows cols m,
          ← coeff_map, eulerClosedForm_minor_map, ← universalPlanePolynomial_map, hz]
        rfl
      rw [homogeneousCoefficientSpecialization_map, universalHyperplaneRestriction_specialize, hz, mul_zero]

