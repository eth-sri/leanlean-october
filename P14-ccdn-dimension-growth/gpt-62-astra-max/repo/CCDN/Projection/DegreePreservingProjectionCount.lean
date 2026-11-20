/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.FilteredIntersection
import CCDN.Algebra.PolynomialSection
import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Hilbert.PlaneHilbert
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Counting via interpolation modulo the plane equation and the filtered Bézout bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K τ : Type*} [Field K]

/-- Interpolate on the image, *modulo* its equation. The resulting proper section has
degree about `#T / d`, so pulling it back will cost only `O(d²)` excess points. -/
private lemma plane_image_interpolation (T : Finset (Fin 2 → K))
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) {d : ℕ} (hfd : f.totalDegree = d) (hd : 0 < d)
    (hT : ∀ x ∈ T, eval x f = 0) : ∃ g : MvPolynomial (Fin 2) K, ¬ f ∣ g ∧
      (∀ x ∈ T, eval x g = 0) ∧ d * g.totalDegree ≤ T.card + d * (d - 1) := by
  classical
  by_cases hsmall : T.card < d
  · let g : MvPolynomial (Fin 2) K := ∏ x ∈ T, (X 0 - C (x 0))
    have hne (x : Fin 2 → K) : (X 0 - C (x 0) : MvPolynomial (Fin 2) K) ≠ 0 := by
      intro h
      have := congrArg totalDegree (sub_eq_zero.mp h)
      simp at this
    have hdeg : g.totalDegree ≤ T.card := calc
      _ ≤ ∑ x ∈ T, (X 0 - C (x 0) : MvPolynomial (Fin 2) K).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ _ ∈ T, 1 := Finset.sum_le_sum fun x _ => (totalDegree_sub _ _).trans (by simp)
      _ = _ := by simp
    refine ⟨g, fun hh => ?_, fun x hx => ?_, (Nat.mul_le_mul_left d (by omega)).trans (Nat.le_add_left ..)⟩
    · have := totalDegree_le_of_dvd_of_isDomain hh (Finset.prod_ne_zero_iff.mpr fun x _ => hne x)
      omega
    simp [g, Finset.prod_eq_zero hx]
  let M := T.card / d + (d - 1)
  let I := Ideal.span {f}
  let V := filteredCoordinateSpace I M
  have hM : d ≤ M := by have := Nat.div_pos (le_of_not_gt hsmall) hd; dsimp [M]; omega
  have hdim := by
    have h := principal_plane_hilbert_function f hf (hfd ▸ hM)
    rw [hfd] at h
    have hquot := Nat.div_add_mod T.card d
    have hrem := Nat.mod_lt T.card hd
    have hchoose : d.choose 2 ≤ d * (d - 1) := by rw [Nat.choose_two_right]; omega
    have hlt : T.card + d.choose 2 < d * M + d := by dsimp [M]; rw [Nat.mul_add]; omega
    change T.card < Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M)
    omega
  let φ (x : T) := Ideal.Quotient.liftₐ I (aeval x.val) (by
    rintro u hu
    obtain ⟨v,rfl⟩ := Ideal.mem_span_singleton.mp hu
    simp_all)
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := (LinearMap.pi fun x => (φ x).toLinearMap.comp V.subtype)) (by simpa using hdim))
  obtain ⟨g, hg, he⟩ := Submodule.mem_map.mp v.property
  refine ⟨g, fun h => hn (Subtype.ext ?_), fun x hx => ?_, ?_⟩
  · rw [← he]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  · have h := congrFun (LinearMap.mem_ker.mp hv) ⟨x, hx⟩
    change φ ⟨x,hx⟩ v.val = 0 at h
    rwa [← he] at h
  · apply (Nat.mul_le_mul_left d ((mem_restrictTotalDegree _ _ _).mp hg)).trans
    dsimp [M]; rw [Nat.mul_add]; gcongr; exact Nat.mul_div_le _ _

/-- A full-degree plane projection identifies at most `d(d-1)` points on any finite
part of the curve. This uses Bézout on the pullback of the interpolating section,
not equations for a rational inverse or an analysis of individual fibers. -/
theorem degree_preserving_projection_card_le [Fintype τ] [DecidableEq (Fin 2 → K)]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime] (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (d : ℕ) (hd : 0 < d) (hdegree : HasFilteredCurveDegree I d)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hfd : f.totalDegree = d)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g) (S : Finset (τ → K)) (hS : ∀ z ∈ S, z ∈ idealZeroLocus I) :
    S.card ≤ (S.image (fun z j => eval z (a j))).card + d * (d - 1) := by
  classical
  have he (z : τ → K) (g : MvPolynomial (Fin 2) K) : eval z (aeval a g) = eval (fun j => eval z (a j)) g := by
    change eval z (eval₂ C a g) = _
    rw [← eval_assoc]; rfl
  obtain ⟨g, hnd, hz, hsize⟩ := plane_image_interpolation (S.image (fun z j => eval z (a j))) f hf hfd hd (by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    have h := hS z hz _ ((hker f).mpr dvd_rfl)
    rwa [he] at h)
  apply le_trans _ hsize
  simpa using polynomial_section_card_le_degree I d hdegree (aeval a g) (by grind)
    g.totalDegree (by simpa using aeval_totalDegree_le a ha g) (fun x : S => x.val) Subtype.val_injective
    (fun x => hS x x.property) (by grind)

end
end CCDN
