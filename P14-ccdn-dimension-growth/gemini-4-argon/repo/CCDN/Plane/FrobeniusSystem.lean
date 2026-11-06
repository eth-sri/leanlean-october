/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
public import CCDN.Noether.FormalPlaneDifferentiation
import CCDN.Determinant.PlaneSingularities
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The finite linear system producing Frobenius auxiliary coefficients.
A strict dimension inequality gives a nontrivial solution. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Independent bounded-degree coefficient classes and more unknowns than
constraints yield bounded-degree auxiliary coefficients. -/
theorem exists_planeFrobenius_coefficients {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : MvPolynomial (Fin 2) K) (j : Fin 2)
    (h : ι → MvPolynomial (Fin 2) K) (b : κ → MvPolynomial (Fin 2) K)
    {D A N : ℕ} (hd : ∀ i, (h i).totalDegree ≤ D) (hb : ∀ k, (b k).totalDegree ≤ A)
    (hbi : LinearIndependent K (fun k => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (b k)))
    (hdim : (∑ r : Fin N, Module.finrank K
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) <
      Fintype.card ι * Fintype.card κ) :
    ∃ a : ι → MvPolynomial (Fin 2) K,
      (∀ i, (a i).totalDegree ≤ A) ∧ (∃ i, ¬ f ∣ a i) ∧
      ∀ r < N, f ∣ ∑ i, (planeTangent f j)^[r] (h i) * a i := by
  classical
  have htan_deg (g : MvPolynomial (Fin 2) K) (r : ℕ) :
      ((planeTangent f j)^[r] g).totalDegree ≤ g.totalDegree + r * f.totalDegree := by
    induction r with
    | zero => simp
    | succ r hr =>
      rw [Function.iterate_succ_apply', planeTangent_apply]
      have hstep : (pderiv j.rev f * pderiv j ((planeTangent f j)^[r] g) -
          pderiv j f * pderiv j.rev ((planeTangent f j)^[r] g)).totalDegree ≤
          ((planeTangent f j)^[r] g).totalDegree + f.totalDegree :=
        (totalDegree_sub _ _).trans (max_le
          ((totalDegree_mul _ _).trans (by
            have := pderiv_totalDegree_le f j.rev
            have := pderiv_totalDegree_le ((planeTangent f j)^[r] g) j; omega))
          ((totalDegree_mul _ _).trans (by
            have := pderiv_totalDegree_le f j
            have := pderiv_totalDegree_le ((planeTangent f j)^[r] g) j.rev; omega)))
      exact hstep.trans (by nlinarith)
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  let π := Ideal.Quotient.mkₐ K I
  let V (r : Fin N) := filteredCoordinateSpace I (D + A + r.val * f.totalDegree)
  let v (r : Fin N) (t : ι × κ) : V r :=
    ⟨π ((planeTangent f j)^[r.val] (h t.1) * b t.2), Submodule.mem_map.mpr
      ⟨_, (mem_restrictTotalDegree _ _ _).mpr ((totalDegree_mul _ _).trans (by
        have := htan_deg (h t.1) r.val; have := hd t.1; have := hb t.2; omega)), rfl⟩⟩
  let F : (ι × κ → K) →ₗ[K] (∀ r, V r) :=
    { toFun := fun c r => ∑ t, c t • v r t
      map_add' := by intros; funext r; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intros; funext r
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hdim' : Module.finrank K (∀ r, V r) < Module.finrank K (ι × κ → K) := by
    rwa [Module.finrank_pi, Fintype.card_prod, Module.finrank_pi_fintype]
  obtain ⟨c, hFc, hc⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := F) hdim')
  rw [LinearMap.mem_ker] at hFc
  let a : ι → MvPolynomial (Fin 2) K := fun i => ∑ k, c (i, k) • b k
  refine ⟨a, fun i => totalDegree_finsetSum_le fun k _ =>
    (totalDegree_smul_le _ _).trans (hb k), ?_, ?_⟩
  · by_contra! hn
    refine hc (funext fun t => ?_)
    have he : π (a t.1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hn t.1))
    exact Fintype.linearIndependent_iff.mp hbi (fun k => c (t.1, k))
      (by simpa only [a, map_sum, map_smul] using he) t.2
  · intro r hr
    have he := congrArg Subtype.val (congrFun hFc (⟨r, hr⟩ : Fin N))
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (∑ i, (planeTangent f j)^[r] (h i) * a i) = 0
    simpa only [F, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
      Submodule.coe_smul, v, Fintype.sum_prod_type, a, Finset.mul_sum,
      mul_smul_comm, map_sum, map_smul, Pi.zero_apply, ZeroMemClass.coe_zero] using he

end
end CCDN
