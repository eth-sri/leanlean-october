/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Determinant.FormalBranchMultiplicity
import CCDN.Noether.PowerSeriesFrobenius
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A local Bézout bound on formal vanishing orders. It gives injective jets
on low-degree functions and verifies the jet condition in Frobenius
noncancellation for irreducible plane curves. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The local intersection bound supplies the independent jets needed for
Frobenius noncancellation as soon as `degree f * D < p`. -/
theorem formal_plane_frobenius_relation_trivial {K ι : Type*} [Field K]
    [Fintype ι] (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (z : Fin 2 → K) (hconst : ∀ h, PowerSeries.constantCoeff (ψ h) = eval z h)
    (j : Fin 2) (hparam : ψ (X j - C (z j)) = PowerSeries.X)
    {D : ℕ} (hD : f.totalDegree * D < p) (h : ι → MvPolynomial (Fin 2) K)
    (hd : ∀ i, (h i).totalDegree ≤ D)
    (hi : LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i)))
    (a : ι → PowerSeries K) (hrel : ∑ i, ψ (h i) * (a i) ^ p = 0) : ∀ i, a i = 0 := by
  classical
  refine powerSeries_frobenius_relation_trivial p (fun i => ψ (h i)) ?_ a hrel
  intro c hc
  let g := ∑ i, c i • h i
  have hg : g.totalDegree ≤ D := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (hd i)
  apply (Fintype.linearIndependent_iff.mp hi) c
  have hdiv : f ∣ g := by
    by_contra hnd
    have hpow : PowerSeries.X ^ p ∣ ψ g :=
      PowerSeries.X_pow_dvd_iff.mpr (by simpa only [g, map_sum, map_smul] using hc)
    have hb := formal_plane_vanishing_order_bound f hf z ψ hψ hconst j hparam g hnd hpow
    nlinarith
  have hz : Ideal.Quotient.mkₐ K (Ideal.span {f}) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  simpa only [g, map_sum, map_smul] using hz

end
end CCDN
