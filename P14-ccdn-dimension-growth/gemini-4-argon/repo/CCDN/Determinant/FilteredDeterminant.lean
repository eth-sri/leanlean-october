/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SingularTangent
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial
import CCDN.Determinant.LocalDeterminant
import CCDN.Determinant.ModularOriginGenerators
import CCDN.Determinant.SingularApproximation
import CCDN.ForMathlib.Matrix

/-! Local determinant divisibility in arbitrary dimension. The exponent is
computed from the cumulative dimensions of the origin-adic layers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The sum of the deficits below successive weights. For a graded profile
this is a lower bound for the sum of the first s weights, with multiplicity. -/
def filtrationExponent (r : ℕ → ℕ) (s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - (Finset.univ.sum fun j : Fin (k.val + 1) => r j.val)

/-- A homogeneous local generating family gives a determinant divisor
at any precision and in any dimension. -/
theorem origin_filtration_pow_dvd_det_mod {p n s e : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (x : Fin s → Fin (n + 1) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (he : e ≤ filtrationExponent
      (fun k => Module.finrank (ZMod p) (originLayer (map (Int.castRingHom (ZMod p)) f) k)) s)
    (hfx : ∀ i, (p : ℤ) ^ e ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin (n + 1)) ℤ) :
    (p : ℤ) ^ e ∣ (Matrix.of fun i j => eval (x i) (F j)).det := by
  /- Layer-cake inequality with an arbitrary cutoff `K`: counting, for each
  `k < K`, the weights exceeding `k` never exceeds the total weight. -/
  /- Distinct generators of weight at most k inject into all generators in
  layers zero through k, independently of the precision used to truncate them. -/
  /- Cauchy--Binet for a finite set of generators indexed in any way. -/
  classical
  obtain ⟨r, g, hr, hg, hrep⟩ := exists_integer_hypersurface_generators (p := p) f
  rw [← (funext hr : r = fun k => Module.finrank (ZMod p)
    (originLayer (map (Int.castRingHom (ZMod p)) f) k))] at he
  let N := e
  choose c hc using fun j => integer_generators_approximate_mod f r g (hrep N) (F j)
  choose U₀ hU using fun (i : Fin s) (z : (k : Fin N) × Fin (r k.val)) =>
    origin_power_eval_dvd (p : ℤ) (x i) (hx i) (homogeneous_mem_origin_power (hg z.1.val z.2))
  let U : Matrix (Fin s) ((k : Fin N) × Fin (r k.val)) ℤ := U₀
  let V : Matrix ((k : Fin N) × Fin (r k.val)) (Fin s) ℤ :=
    fun z j => (p : ℤ) ^ z.1.val * c j z.1 z.2
  have hdet : (p : ℤ) ^ N ∣ (U * V).det := by
    let a := (Fintype.equivFin ((k : Fin N) × Fin (r k.val))).symm
    rw [show U * V = U.submatrix id a * V.submatrix a id from
      Matrix.ext fun i j => (Equiv.sum_comp a (fun z => U i z * V z j)).symm]
    refine pow_dvd_det_of_weighted_factorization _ _ (p : ℤ) (fun z => (a z).1.val) N
      (fun _ _ => dvd_mul_right _ _) fun t0 => ?_
    let t := t0.toEmbedding.trans a.toEmbedding
    change e ≤ ∑ i, (t i).1.val
    refine he.trans ((Finset.sum_le_sum
      (g := fun k : Fin s => (Finset.univ.filter fun i => k.val < (t i).1.val).card)
      fun k _ => ?_).trans ?_)
    · let φ : {i : Fin s // (t i).1.val ≤ k.val} → ((j : Fin (k.val + 1)) × Fin (r j.val)) :=
        fun i => ⟨⟨(t i.val).1.val, by omega⟩, (t i.val).2⟩
      let forget : ((j : Fin N) × Fin (r j.val)) → ((j : ℕ) × Fin (r j)) :=
        Sigma.map Fin.val (fun _ j => j)
      have hinj : Function.Injective forget :=
        Fin.val_injective.sigma_map (fun _ => Function.injective_id)
      have hφ : Function.Injective φ := fun u v h => Subtype.ext <| t.injective <|
        hinj (congrArg (fun v : (j : Fin (k.val + 1)) × Fin (r j.val) =>
          (⟨v.1.val, v.2⟩ : (j : ℕ) × Fin (r j))) h)
      have hlow : (Finset.univ.filter fun i => (t i).1.val ≤ k.val).card ≤
          ∑ j : Fin (k.val + 1), r j.val := by
        simpa only [Fintype.card_subtype, Fintype.card_sigma, Fintype.card_fin] using
          Fintype.card_le_of_injective φ hφ
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin s))) (p := fun i => (t i).1.val ≤ k.val)
      simp only [Finset.card_univ, Fintype.card_fin, not_le] at hpart; omega
    · simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hcard : (Finset.univ.filter fun k : Fin s => k.val < (t i).1.val).card ≤ (t i).1.val := by
        rw [Fin.card_filter_val_lt]; exact min_le_right _ _
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcard
  have hd := Matrix.dvd_det_sub_det_of_dvd_sub (Matrix.of fun i j => eval (x i) (F j))
    (U * V) ((p : ℤ) ^ N) fun i j => by
      rw [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sigma,
        show (∑ k : Fin N, ∑ l, U i ⟨k, l⟩ * V ⟨k, l⟩ j) =
          ∑ k : Fin N, ∑ l, c j k l * eval (x i) (g k.val l) from
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [hU i ⟨k, l⟩]; dsimp only [U, V]; ring]
      exact hc j (x i) (hfx i) (hx i)
  simpa only [sub_add_cancel] using dvd_add hd hdet

end
end CCDN
