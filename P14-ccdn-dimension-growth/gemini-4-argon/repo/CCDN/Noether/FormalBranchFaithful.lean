/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.SectionImageRank
import CCDN.ForMathlib.PowerSeries
import CCDN.Hilbert.PlaneHilbert
import CCDN.Noether.FormalPlaneBranch
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal

/-! A formal plane parameterization with a free coordinate has exactly the
curve equation as its kernel. The proof uses the section-image rank bound
and arbitrarily many independent powers of the formal parameter. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every nonsingular point on an irreducible plane curve gives a
faithful formal branch, with the original point as its constant evaluation. -/
theorem exists_faithful_formal_plane_branch {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) (z : Fin 2 → K) (j : Fin 2)
    (hz : eval z f = 0) (hj : eval z (pderiv j f) ≠ 0) :
    ∃ ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K,
      (∀ h, PowerSeries.constantCoeff (ψ h) = eval z h) ∧
      ψ (X j.rev - C (z j.rev)) = PowerSeries.X ∧
      ∀ h, ψ h = 0 ↔ f ∣ h := by
  obtain ⟨g, ⟨hg1, hg2⟩, _⟩ := exists_unique_formal_plane_branch f z j hz hj
  /- The substitution map attached to a chosen formal branch. -/
  let ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K :=
    MvPolynomial.aeval (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev))
  have hψ : ψ f = 0 := by
    simpa only [ψ, MvPolynomial.aeval_def, PowerSeries.algebraMap_eq] using hg2
  have hparam : ψ (X j.rev - C (z j.rev)) = PowerSeries.X := by
    fin_cases j <;> simp [ψ, PowerSeries.algebraMap_eq]
  have hconst : PowerSeries.constantCoeff.comp ψ.toRingHom = eval z := by
    refine MvPolynomial.ringHom_ext
      (fun _ => by simp [ψ, PowerSeries.algebraMap_eq]) fun k => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ, aeval_X]
    by_cases hk : k = j
    · subst k; simp [hg1]
    · simp only [ite_eq_right hk, map_add, PowerSeries.constantCoeff_X,
        PowerSeries.constantCoeff_C, zero_add]
      simpa only [ite_eq_right hk, MvPolynomial.eval_X] using congrFun (plane_coordinate_cases z j) k
  refine ⟨ψ, RingHom.congr_fun hconst, hparam, fun q => ⟨fun hq => ?_, ?_⟩⟩
  · by_contra hnd
    let p : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
    have : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
    let φ : (MvPolynomial (Fin 2) K ⧸ p) →ₐ[K] PowerSeries K :=
      Ideal.Quotient.liftₐ p ψ fun l hl => by
        obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hl
        rw [map_mul, hψ, zero_mul]
    let N := f.totalDegree * q.totalDegree + 1
    let h : Fin N → MvPolynomial (Fin 2) K := fun i => (X j.rev - C (z j.rev)) ^ i.val
    have hi : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))) := by
      rw [show (fun i => φ ((Ideal.Quotient.mk p) (h i))) =
          fun i : Fin N => (PowerSeries.X : PowerSeries K) ^ i.val from
        funext fun i => by change ψ _ = _; simp only [h, map_pow, hparam]]
      exact PowerSeries.linearIndependent_of_order_injective _ Fin.val Fin.val_injective
        fun i => PowerSeries.order_X_pow i.val
    have hh := section_image_rank_le p f.totalDegree
      ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
        fun M hM => principal_plane_hilbert_function f hf.ne_zero hM⟩
      φ h hi q (by simpa only [p, Ideal.mem_span_singleton] using hnd) q.totalDegree le_rfl hq
    rw [Fintype.card_fin] at hh
    dsimp only [N] at hh
    omega
  · rintro ⟨u, rfl⟩
    rw [map_mul, hψ, zero_mul]

end
end CCDN
