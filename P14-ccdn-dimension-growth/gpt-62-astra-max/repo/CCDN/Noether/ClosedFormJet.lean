/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.FormalBranchFaithful
public import CCDN.Noether.FormalPlaneDifferentiation
import CCDN.Noether.FormalBranchOrder
import Mathlib.RingTheory.PowerSeries.Inverse

/-! On a smooth branch a closed logarithmic form has locally constant residue through all orders below the characteristic. -/
@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K]

private lemma jet_dvd_of_constant {N : ℕ} (hchar : CharZeroOrGT K N) {u : PowerSeries K}
    (hd : PowerSeries.derivative u = 0) (h0 : PowerSeries.constantCoeff u = 0) : PowerSeries.X^(N+1) ∣ u := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro n hn
  cases n with
  | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
  | succ n =>
    have := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative,map_zero,mul_eq_zero] at this
    exact this.resolve_right (by exact_mod_cast hchar (n+1) (by omega) (by omega))

/-- A closed numerator pair on a smooth branch: if its first numerator vanishes at the base point,
its residue has zero jet, so the numerator meets the curve with multiplicity at least `N+1`. -/
lemma closed_form_zero_jet (f p q : MvPolynomial (Fin 2) K)
    (closed : pderiv 1 p*f - p*pderiv 1 f = pderiv 0 q*f - q*pderiv 0 f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hf : ψ f = 0)
    (a : K) (param : ψ (X 1-C a) = PowerSeries.X)
    (unit : IsUnit (ψ (pderiv 0 f))) (hp0 : PowerSeries.constantCoeff (ψ p) = 0)
    {N : ℕ} (hchar : CharZeroOrGT K N) : PowerSeries.X^(N+1) ∣ ψ p := by
  let fx := pderiv 0 f
  have h := congrArg ψ closed
  have dh := congrArg (fun b => ψ (pderiv 0 b)) closed
  simp only [map_sub,pderiv_mul,map_add,map_mul,hf,mul_zero,pderiv_comm 0 1 f] at h dh
  have htan : ψ fx * ψ (planeTangent f 1 p) - ψ p * ψ (planeTangent f 1 fx) = 0 := by
    simp only [planeTangent_apply,show (1:Fin 2).rev = 0 from rfl,map_sub,map_mul,fx]
    linear_combination ψ (pderiv 0 f)*dh - ψ (pderiv 0 (pderiv 0 f))*h
  rw [formal_plane_tangent f ψ hf 1 a param, formal_plane_tangent f ψ hf 1 a param] at htan
  change ψ fx*(ψ fx*PowerSeries.derivative (ψ p))-ψ p*(ψ fx*PowerSeries.derivative (ψ fx)) = 0 at htan
  obtain ⟨u,hu⟩ := unit
  have hn : ψ fx ≠ 0 := hu ▸ u.ne_zero
  let v := (↑u⁻¹:PowerSeries K) * ψ p
  have hv : v * ψ fx = ψ p := by change v*ψ (pderiv 0 f) = _; rw [← hu]; simp [v,mul_comm]
  have hdiff := congrArg PowerSeries.derivative hv
  simp only [Derivation.leibniz,smul_eq_mul] at hdiff
  have hv' : PowerSeries.derivative v * (ψ fx)^3 = 0 := by
    rw [← hdiff, ← hv] at htan
    linear_combination htan
  have hv0 : PowerSeries.constantCoeff v = 0 := by simp [v,hp0]
  rw [← hv]
  exact dvd_mul_of_dvd_left (jet_dvd_of_constant hchar ((mul_eq_zero.mp hv').resolve_right (pow_ne_zero _ hn)) hv0) _

end
end CCDN
