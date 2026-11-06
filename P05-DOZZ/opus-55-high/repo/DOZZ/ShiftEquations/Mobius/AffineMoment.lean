/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.RepinGMC
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.Statements.Correlations.NPointSExp
public import DOZZ.GMC.SharpMoments.SeibergWeight
import DOZZ.GMC.EquatorGFFChaosTransportLaw
import DOZZ.GMC.Construction.GMCGeneralTiltLimit
import DOZZ.ShiftEquations.Mobius.InversionMoment
import DOZZ.GMC.CircleAverage

/-!
# Coulomb moments under affine maps

For `ψ(y) = a y + b` with `a ≠ 0` and the zero-mode exponent `s = (∑ αₖ - 2Q)/γ`,
`E[I_{ψz}^{-s}] = |a|^{γ S s / 2} E[I_z^{-s}]`, `S = ∑ αₖ`.

The repinned model `(X̂, M̂)` has the law of `(X, M)` (law transport), and the Coulomb mass of `M̂`
at the roots `z` is `e^{-γL - γ² Var L/2}` times a deterministic reweighting of `M`. A
Cameron–Martin tilt by `γ s L` removes the random factor, and the deterministic identities
`c(ψy) = d(y) + κ`, `w(ψy) = e^{4d(y)}`, `Var L = 2κ` and `γ² + 4 = 2γQ` turn the reweighted mass
into the Coulomb mass at the roots `ψ z`, up to the constant `|a|^{γS/2} e^{γ²(1+s)κ}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The background ratio through the affine map is the exponential of the defect. -/
theorem repinWeight_affine (a b : ℂ) (ha : a ≠ 0) (y : ℂ) :
    repinWeight a b (a * y + b) = Real.exp (4 * affineDefect a b y) := by
  have hy := DOZZ.Proofs.normPlus_pos y
  have hψ := DOZZ.Proofs.normPlus_pos (a * y + b)
  have hapos := norm_pos_iff.mpr ha
  unfold repinWeight affineDefect
  rw [affineInv_affine a b ha y,
    show 4 * (Real.log (normPlus (a * y + b)) - Real.log (normPlus y) - Real.log ‖a‖ / 2) =
      Real.log (normPlus (a * y + b) ^ 4 / (normPlus y ^ 4 * ‖a‖ ^ 2)) by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring,
    Real.exp_log (by positivity), Real.rpow_neg hy.le, Real.rpow_neg hψ.le]
  norm_cast
  field_simp

/-- **The Coulomb weight through an affine map**, away from the roots. -/
theorem coulombWeight_affine {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (a b : ℂ)
    (ha : a ≠ 0) {y : ℂ} (hyz : ∀ k, y ≠ z k) :
    coulombWeight γ α (fun k => a * z k + b) 0 (a * y + b) =
      ENNReal.ofReal (Real.exp (γ * (∑ k, α k) * (affineDefect a b y - Real.log ‖a‖ / 2))) *
        coulombWeight γ α z 0 y := by
  have hy := DOZZ.Proofs.normPlus_pos y
  have hψ := DOZZ.Proofs.normPlus_pos (a * y + b)
  have hapos := norm_pos_iff.mpr ha
  set t := normPlus (a * y + b) / (‖a‖ * normPlus y) with htdef
  have ht : 0 < t := by positivity
  have hfac : ∀ k, normPlus (a * y + b) / ‖a * y + b - (a * z k + b)‖ =
      t * (normPlus y / ‖y - z k‖) := fun k => by
    have hk := norm_pos_iff.mpr (sub_ne_zero.mpr (hyz k))
    rw [show a * y + b - (a * z k + b) = a * (y - z k) by ring, norm_mul, htdef]
    field_simp
  have hlogt : Real.log t = affineDefect a b y - Real.log ‖a‖ / 2 := by
    unfold affineDefect
    rw [htdef, Real.log_div hψ.ne' (by positivity), Real.log_mul hapos.ne' hy.ne']
    ring
  unfold coulombWeight
  simp only [ENNReal.rpow_eq_pow, mul_zero, ENNReal.rpow_zero, mul_one]
  simp_rw [hfac, ENNReal.ofReal_mul ht.le]
  rw [Finset.prod_congr rfl fun k _ => ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top _, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_congr rfl fun k _ => ENNReal.ofReal_rpow_of_pos ht,
    ← ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.rpow_pos_of_pos ht _).le,
    ← Real.rpow_sum_of_pos ht, ← Finset.mul_sum, Real.rpow_def_of_pos ht, hlogt]
  ring_nf

theorem affine_affineInv (a b : ℂ) (ha : a ≠ 0) (x : ℂ) : a * affineInv a b x + b = x := by
  unfold affineInv
  field_simp
  ring

/-- Gaussian `L²` limits of test evaluations are closed under scaling. -/
theorem IsGaussianL2Limit.const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {L : Ω → ℝ} (hL : IsGaussianL2Limit P X L) (c : ℝ) :
    IsGaussianL2Limit P X (fun ω => c * L ω) := by
  obtain ⟨hLm, f, hf⟩ := hL
  refine ⟨hLm.const_mul c, fun n => c • f n, ?_⟩
  have h : ∀ n, (fun ω => c * L ω - X ω (c • f n)) = fun ω => c • (L ω - X ω (f n)) :=
    fun n => by
      funext ω
      rw [map_smul, smul_eq_mul, smul_eq_mul]
      ring
  simp_rw [h]
  have heq : ∀ n, eLpNorm (fun ω => c • (L ω - X ω (f n))) 2 P =
      ‖c‖ₑ * eLpNorm (fun ω => L ω - X ω (f n)) 2 P := fun n =>
    eLpNorm_const_smul c (fun ω => L ω - X ω (f n)) 2 P
  simp_rw [heq]
  simpa using ENNReal.Tendsto.const_mul hf (Or.inr enorm_ne_top)

end DOZZ.Proofs

end
