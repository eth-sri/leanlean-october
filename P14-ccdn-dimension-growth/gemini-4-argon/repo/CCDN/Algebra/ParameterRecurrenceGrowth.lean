/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ParameterPowerSpan
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Hilbert.AffineCurveDegree

/-!
If a filtration is eventually generated one step at a time by a parameter,
its linear growth has slope at most the function-field degree over K(t).
Common denominators affect only the fixed additive offset in the bound.

Any finite family in a finite extension of K(t) fits in a bounded power
block after multiplication by one nonzero rational-function denominator.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- The Hilbert slope is at most the parameter extension degree whenever the
coordinate filtration has the parameter-generation recurrence. -/
theorem parameter_recurrence_slope_le {K A F : Type*} [Field K]
    [AddCommGroup A] [Module K A] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F]
    (V : ℕ → Submodule K A) [∀ n, Module.Finite K (V n)]
    (L : A →ₗ[K] A) (φ : A →ₗ[K] F) (hφ : Function.Injective φ)
    (hL : ∀ x, φ (L x) = algebraMap (RatFunc K) F RatFunc.X * φ x)
    (N : ℕ) (hrec : ∀ n ≥ N, V (n + 1) = V n ⊔ (V n).map L)
    (d : ℕ) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank K (V n) : ℤ) = (d : ℤ) * n + c) :
    d ≤ Module.finrank (RatFunc K) F := by
  classical
  let b := Module.finBasis K (V N)
  let u := algebraMap (RatFunc K) F RatFunc.X
  let v := Module.finBasis (RatFunc K) F
  let r := Module.finrank (RatFunc K) F
  let w := fun i => φ (b i).val
  obtain ⟨q0, hq0⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun t : Fin (Module.finrank K (V N)) × Fin r => v.repr (w t.1) t.2)
  choose p hp using hq0
  let D := Finset.univ.sup (fun t => (p t).natDegree)
  let q := algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) q0.val)
  have hq : q ≠ 0 := (map_ne_zero_iff (algebraMap (RatFunc K) F)
    (algebraMap (RatFunc K) F).injective).mpr
    (RatFunc.algebraMap_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp q0.property))
  have heval (P : Polynomial K) :
      algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) P) = Polynomial.aeval u P := by
    let ψ := (IsScalarTower.toAlgHom K (RatFunc K) F).comp
      (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
    have he : ψ = Polynomial.aeval u := by
      apply Polynomial.algHom_ext
      simp [ψ, u, RatFunc.algebraMap_X]
    exact congrArg (fun f => f P) he
  have hD (j) : q * w j ∈ parameterPowerSpan K u v D := by
    rw [← v.sum_repr (w j), Finset.mul_sum]
    refine (parameterPowerSpan K u v D).sum_mem fun i _ => ?_
    have he : q * (v.repr (w j) i • v i) = Polynomial.aeval u (p (j, i)) * v i := by
      rw [Algebra.smul_def, ← mul_assoc]
      change (algebraMap (RatFunc K) F _ * algebraMap (RatFunc K) F _) * _ = _
      rw [← map_mul, ← (hp (j, i)).trans (Algebra.smul_def _ _), heval]
    rw [he]
    exact polynomial_parameter_mul_mem _ v i (p (j, i)) D
      (Finset.le_sup (f := fun t => (p t).natDegree) (Finset.mem_univ (j, i)))
  let T := (LinearMap.mulLeft K q).comp φ
  have hT (x : A) : T x = q * φ x := rfl
  have hTi : Function.Injective T := fun x y h => hφ (mul_left_cancel₀ hq h)
  have hTL (x : A) : T (L x) = u * T x := by rw [hT, hL, hT]; ring
  have hbound (m : ℕ) : ∀ x ∈ V (N + m), T x ∈ parameterPowerSpan K u v (D + m) := by
    induction m with
    | zero =>
      intro x hx
      have he : T x = ∑ i, b.repr ⟨x, hx⟩ i • (q * w i) := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hT, Finset.mul_sum,
          mul_smul_comm] using (congrArg (fun z : V N => T z.val) (b.sum_repr ⟨x, hx⟩)).symm
      rw [he]
      exact (parameterPowerSpan K u v D).sum_mem fun i _ =>
        (parameterPowerSpan K u v D).smul_mem _ (hD i)
    | succ m ih =>
      intro x hx
      rw [show N + (m + 1) = (N + m) + 1 by omega, hrec (N + m) (by omega)] at hx
      obtain ⟨y, hy, _, ⟨z, hz, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, hTL]
      exact (parameterPowerSpan K u v (D + (m + 1))).add_mem
        (parameterPowerSpan_mono u v (by omega) (ih y hy))
        (by simpa only [Nat.add_assoc] using parameterPowerSpan_mul_mem u v (D + m) (ih z hz))
  have hfin (m : ℕ) : Module.finrank K (V (N + m)) ≤ r * (D + m + 1) := by
    let Tm : V (N + m) →ₗ[K] parameterPowerSpan K u v (D + m) :=
      (T.comp (V (N + m)).subtype).codRestrict _ (fun x => hbound m x.val x.property)
    have hi : Function.Injective Tm := fun x y h => Subtype.ext (hTi (congrArg Subtype.val h))
    exact (LinearMap.finrank_le_finrank_of_injective hi).trans
      (by simpa only [Fintype.card_fin, Nat.add_assoc] using parameterPowerSpan_finrank_le u v (D + m))
  obtain ⟨M, c, hc⟩ := hdegree
  refine eventual_linear_slope_le (fun m => Module.finrank K (V (N + m)))
    (fun m => r * (D + m + 1)) d r
    ⟨M, (d : ℤ) * N + c, fun m _ => by rw [hc (N + m) (by omega)]; push_cast; ring⟩
    ⟨0, (r : ℤ) * (D + 1), fun m _ => by push_cast; ring⟩ hfin

end
end CCDN
