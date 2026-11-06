/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.InfinityParameterReduction
import CCDN.ForMathlib.LinearMap

/-!
The certified affine Hilbert degree bounds the number of geometric
infinity points in each normalized projective chart.

Homogeneous polynomials with extension-field coefficients contribute no
new directions beyond the extension-field span of ground-field monomials.

Finite interpolation in a projective affine chart can be performed by
homogeneous polynomials of any sufficiently large common degree.

Evaluating homogeneous polynomials at geometric infinity points has
L-linear rank at most the corresponding infinity Hilbert piece. The
source curve and its Hilbert function are defined over the original field K.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Each normalized infinity chart is a finite set with at most d
points, not merely a bound for already finite subsets. -/
theorem exists_finite_infinity_chart {K L σ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype σ] (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (j : σ) :
    ∃ S : Finset (σ → L), S.card ≤ d ∧ ∀ z,
      z ∈ S ↔ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) ∧ z j = 1 := by
  classical
  have hcard {ι : Type _} [Fintype ι] (z : ι → σ → L)
      (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
      (hinj : Function.Injective z) (hj : ∀ i, z i j = 1) :
      Fintype.card ι ≤ d := by
    obtain ⟨N, c, hN⟩ := hdegree
    let m := N + Fintype.card ι
    let V := homogeneousSubmodule σ K (m + 1)
    let : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg σ K (m + 1))
    let f := (infinityCoordinateMap I).toLinearMap.comp V.subtype
    let g : V →ₗ[K] (ι → L) :=
      LinearMap.pi fun i => (aeval (z i)).toLinearMap.comp V.subtype
    have hker : f.ker ≤ g.ker := fun p hp =>
      LinearMap.mem_ker.mpr (funext fun i => hz i _ hp)
    have hrange : f.range ≤ infinityGradedSpace I m := by
      rintro _ ⟨p, rfl⟩
      refine ⟨⟨(Ideal.Quotient.mk I) p,
        ⟨p, (mem_restrictTotalDegree _ _ _).mpr p.property.totalDegree_le, rfl⟩⟩, ?_⟩
      change Ideal.Quotient.mk (projectiveInfinityIdeal I) (projectiveMonomialMap I (m + 1) _) =
        Ideal.Quotient.mk (projectiveInfinityIdeal I) (quotientRadialMap I p)
      rw [quotientRadialMap_homogeneous I p (m + 1) p.property]
    let W := Submodule.span L (Set.range g)
    have hb : Module.finrank L W ≤ d :=
      ((LinearMap.finrank_span_range_le_of_ker_le f g hker).trans (Submodule.finrank_mono hrange)).trans_eq
        (infinityGradedSpace_eventually_degree I hN m (by dsimp [m]; omega))
    have htop : W = ⊤ := by
      let b := Pi.basisFun L ι
      have hbi (i : ι) : b i ∈ W := by
        have hdiff (k : ι) (hik : i ≠ k) : ∃ q : σ, z i q ≠ z k q := by
          by_contra! he; exact hik (hinj (funext he))
        let q (k : ι) (hik : i ≠ k) := (hdiff k hik).choose
        have hq (k : ι) (hik : i ≠ k) : z i (q k hik) - z k (q k hik) ≠ 0 :=
          sub_ne_zero.mpr (hdiff k hik).choose_spec
        let l (k : ι) : MvPolynomial σ L := if hik : i = k then X j else
          C ((z i (q k hik) - z k (q k hik))⁻¹) * (X (q k hik) - C (z k (q k hik)) * X j)
        have hl (k : ι) : (l k).IsHomogeneous 1 := by
          dsimp [l]; split_ifs
          · exact isHomogeneous_X L j
          · exact ((isHomogeneous_X L _).sub (isHomogeneous_C_mul_X _ _)).C_mul _
        have hli (k : ι) : MvPolynomial.eval (z i) (l k) = 1 := by
          dsimp [l]; split_ifs with hik <;> simp [hj, hq]
        have hlk (k : ι) (hik : i ≠ k) : MvPolynomial.eval (z k) (l k) = 0 := by simp [l, hik, hj]
        let p : MvPolynomial σ L := (∏ k, l k) * X j ^ (m + 1 - Fintype.card ι)
        have hp : p.IsHomogeneous (m + 1) := by
          have hh : (∏ k, l k).IsHomogeneous (Fintype.card ι) := by
            simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
              IsHomogeneous.prod Finset.univ l (fun _ => 1) fun k _ => hl k
          simpa only [Nat.add_sub_of_le (by dsimp [m]; omega : Fintype.card ι ≤ m + 1)]
            using hh.mul (isHomogeneous_X_pow j (m + 1 - Fintype.card ι))
        have he (k : ι) : MvPolynomial.eval (z k) p = if i = k then 1 else 0 := by
          dsimp [p]
          by_cases hik : i = k
          · subst k; simp [hli, hj]
          · have hh : ∏ t, MvPolynomial.eval (z k) (l t) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ k) (hlk k hik)
            simp [hik, hh]
        have hmono (e : σ →₀ ℕ) (he' : e ∈ p.support) :
            (fun k => MvPolynomial.eval (z k) (monomial e (p.coeff e))) ∈ W := by
          have hdeg : e.degree = m + 1 := by
            rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]; exact hp (mem_support_iff.mp he')
          let q' : V := ⟨monomial e 1, isHomogeneous_monomial 1 hdeg⟩
          rw [show (fun k => MvPolynomial.eval (z k) (monomial e (p.coeff e))) = p.coeff e • g q' by
            funext k; simp [g, q', MvPolynomial.eval_monomial, aeval_monomial]]
          exact W.smul_mem _ (Submodule.subset_span ⟨q', rfl⟩)
        have hv : (fun k => MvPolynomial.eval (z k) p) ∈ W := by
          rw [show (fun k => MvPolynomial.eval (z k) p) =
              ∑ e ∈ p.support, (fun k => MvPolynomial.eval (z k) (monomial e (p.coeff e))) by
            funext k; simpa only [Finset.sum_apply, map_sum] using congrArg (MvPolynomial.eval (z k)) p.as_sum]
          exact W.sum_mem hmono
        rwa [show (fun k => MvPolynomial.eval (z k) p) = b i by
          funext k; simp [he, b, Pi.basisFun_apply, Pi.single_apply, eq_comm]] at hv
      exact top_unique fun v _ => by rw [← b.sum_repr v]; exact W.sum_mem fun i _ => W.smul_mem _ (hbi i)
    rw [htop] at hb
    simpa only [finrank_top, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one] using hb
  let T := {z : σ → L | z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) ∧ z j = 1}
  have hT : T.Finite := by
    by_contra hn
    obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hn (d + 1)
    have hb := hcard (fun z : S => z.val) (fun z => (hS z.property).1)
      Subtype.val_injective (fun z => (hS z.property).2)
    rw [Fintype.card_coe, hc] at hb; omega
  refine ⟨hT.toFinset, ?_, fun z => hT.mem_toFinset⟩
  simpa only [Fintype.card_coe] using hcard (fun z : hT.toFinset => z.val)
    (fun z => (hT.mem_toFinset.mp z.property).1) Subtype.val_injective
    (fun z => (hT.mem_toFinset.mp z.property).2)

end
end CCDN
