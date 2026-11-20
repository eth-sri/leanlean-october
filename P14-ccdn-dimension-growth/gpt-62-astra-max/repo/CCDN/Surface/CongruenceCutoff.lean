/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Surface.CongruenceAuxiliary
public import CCDN.AuxiliaryPolynomial.AffineScaledEstimate
import CCDN.AuxiliaryPolynomial.CongruenceBadPrimeCharge

/-! Fixed-degree estimate for the general auxiliary on smooth surface classes. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset MvPolynomial

section

variable (d : ℕ) (K : ℝ)

abbrev primeCost := Real.exp (2*mertensError+1) *
    (2 + 27*(d:ℝ)^4*hypersurfaceHeightConstant 3*(1+|K|/d^2))

private lemma surface_prime_charge {f : IntegerPolynomial 3} (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (hheight : Real.log H ≤ K*(Real.log B+1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    primeSetFactor (largeBadPrimes f hir ∪ P) ≤ primeCost f.totalDegree K * (1+Real.log B+∑ p ∈ P, Real.log p) := by
  let d := f.totalDegree
  let Q := ∑ p ∈ P, Real.log p
  let T := 1+Real.log B+Q
  let a := 27*(d:ℝ)^4*hypersurfaceHeightConstant 3
  have hc := (hypersurfaceHeightConstant_one_le 3).trans' zero_le_one
  have ha : 0 ≤ a := by positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have ht : 1 ≤ T := by dsimp [T]; linarith [Real.log_nonneg hB]
  have hheight' : Real.log H / (d:ℝ)^2 ≤ K/(d:ℝ)^2*T := by
    rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ (sq_nonneg _); dsimp [T]; nlinarith
  have hin : 1 + a*(1+Real.log H/(d:ℝ)^2)+Q ≤ (2+a*(1+K/(d:ℝ)^2))*T := by
    have hw := mul_le_mul_of_nonneg_left hheight' ha
    have hh := le_mul_of_one_le_right ha ht
    dsimp [T] at *; nlinarith only [hw,hh,ht,hQ,Real.log_nonneg hB]
  have h := hypersurface_and_congruence_prime_charge f hir hd H hH hcoeff _ P
    (fun p hp => (mem_largeBadPrimes f hir p).mp hp) hP
  have h' := Real.exp_le_exp.mpr h
  rw [add_assoc,Real.exp_add,Real.exp_log (by have := Real.log_nonneg hH; positivity)] at h'
  apply h'.trans
  dsimp only [primeCost]
  rw [abs_of_nonneg hK]
  linear_combination Real.exp (2*mertensError+1) * hin

abbrev lowerDegreeScale := (d:ℝ)^(1-1/(1+1:ℝ))

def surfaceCongruenceDegreeConstant := hypersurfaceAbsoluteAuxiliaryConstant 1 *
    (auxDegreeScale 1 d * primeCost d K * scalingCost 1 + lowerDegreeScale d * (6*d+1) + auxDegreeScale 1 d) + 3

lemma surfaceCongruenceDegreeConstant_pos : 0 < surfaceCongruenceDegreeConstant d K := by
  have := hypersurfaceAbsoluteAuxiliaryConstant_pos 1
  have := (hypersurfaceHeightConstant_one_le 3).trans' zero_le_one
  unfold surfaceCongruenceDegreeConstant scalingCost primeCost; positivity

end

private theorem surface_scaled_degree {d : ℕ} (hd : 0 < d) {K B p H Q b : ℝ} (hB : 1 ≤ B) (hp : 1 ≤ p)
    (hsize : p ≤ 6*B*d) (hH : p^d ≤ H) (hQ : 0 ≤ Q) (_hb : 0 ≤ b)
    (hbad : b ≤ primeCost d K*(1+Real.log B+Q)) :
    hypersurfaceAuxiliaryDegreeBound 1 d p (b/Real.exp Q) H + 3*Q ≤
      surfaceCongruenceDegreeConstant d K * (B^(1/Real.sqrt (d:ℝ))/Real.exp Q+1) * (1+Real.log B+Q) := by
  let U := affineBoxPower 1 d B / Real.exp Q + 1
  let T := 1+Real.log B+Q
  let D := auxDegreeScale 1 d
  let E := primeCost d K
  have hp0 := zero_lt_one.trans_le hp
  have hc := (hypersurfaceHeightConstant_one_le 3).trans' zero_le_one
  have he : 0 ≤ E := by positivity
  have hsc : 0 ≤ scalingCost 1 := by unfold scalingCost; positivity
  have hB0 := zero_le_one.trans hB
  have hlog := Real.log_nonneg hB
  have hu : 1 ≤ U := by apply le_add_of_nonneg_left; positivity
  have ht : 1 ≤ T := by linarith
  have htu : T ≤ U*T := le_mul_of_one_le_left (by linarith) hu
  have h1 := ht.trans htu
  have hl : Real.log p ≤ (6*d+1)*(U*T) := by
    have := log_scaling hd hB hp hsize
    linarith [le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) d) h1]
  have hH0 := (pow_pos hp0 d).trans_le hH
  have hpq : p^boxExponent 1 d / H^heightExponent 1 d ≤ scalingCost 1 * affineBoxPower 1 d B := by
    apply le_trans _ (affine_power_scaling hd hp hB hsize)
    rw [scaling_identity hd hp0, div_le_iff₀ (by positivity),mul_comm]
    gcongr
  have hm : auxMainTerm 1 d p (b/Real.exp Q) H ≤ D*E*scalingCost 1*(U*T) := calc
    _ = D*b/Real.exp Q*(p^boxExponent 1 d / H^heightExponent 1 d) := by unfold auxMainTerm; ring
    _ ≤ D*(E*T)/Real.exp Q*(scalingCost 1*affineBoxPower 1 d B) := by gcongr
    _ = D*E*scalingCost 1*((affineBoxPower 1 d B/Real.exp Q)*T) := by ring
    _ ≤ _ := by gcongr; linarith
  have hw : lowerDegreeScale d * Real.log p ≤ lowerDegreeScale d * ((6*d+1)*(U*T)) := by gcongr
  have hD := le_mul_of_one_le_right (show 0 ≤ D by positivity) h1
  have hc0 := (hypersurfaceAbsoluteAuxiliaryConstant_pos 1).le
  have hdeg : auxDegreeBound 1 d p (b/Real.exp Q) H ≤ (D*E*scalingCost 1 + lowerDegreeScale d*(6*d+1)+D)*(U*T) := by
    unfold auxDegreeBound
    simp only [D, auxDegreeScale, lowerDegreeScale, Nat.cast_one] at hD hw hm ⊢
    linear_combination hm + hw + hD
  have hu' : B^(1/Real.sqrt (d:ℝ))/Real.exp Q+1 = U := by norm_num [U,affineBoxPower,degreeRoot,Real.sqrt_eq_rpow]
  rw [hu']; unfold hypersurfaceAuxiliaryDegreeBound surfaceCongruenceDegreeConstant
  have hq' : Q ≤ U*T := le_trans (by linarith) htu
  linear_combination hypersurfaceAbsoluteAuxiliaryConstant 1 * hdeg + 3*hq'

/-- The smooth residue classes have a proper auxiliary of degree
O_d,K((B^(1/√d)/exp Q + 1)(1 + log B + Q)). -/
theorem exists_surface_congruence_auxiliary
    (f : IntegerPolynomial 3)
    (hprim : PrimitiveIntegerPolynomial f) (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → IntPoint 3)
    (ha : ∀ p ∈ P, MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j => (a p j : ZMod p)) f = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, MvPolynomial.eval (fun i => (a p i : ZMod p))
      (MvPolynomial.pderiv j (residueEquation p f)) ≠ 0) :
    ∃ g : IntegerPolynomial 3, g ≠ 0 ∧
      ¬ rationalEquation f ∣ rationalEquation g ∧
      (g.totalDegree : ℝ) ≤ surfaceCongruenceDegreeConstant f.totalDegree K *
        (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
          Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) ∧
      ∀ x ∈ affineCongruencePoints f B P a, MvPolynomial.eval x g = 0 := by
  obtain ⟨S⟩ := exists_boxScaling f hprim hd hB
  let X := affineCongruencePoints f B P a
  have hx (x : X) := mem_affineCongruencePoints.mp x.property
  obtain ⟨g,hnd,hz,hdeg⟩ := S.auxiliary hprim hir hd X (fun _ h => (mem_affineCongruencePoints.mp h).1)
    (fun _ h => (mem_affineCongruencePoints.mp h).2.1) P a ⟨hP,ha,hsmooth,fun p hp i => (hx i).2.2 p hp⟩
  refine ⟨g,fun h => hnd (h ▸ dvd_zero _),fun h => hnd (hprim.rational_map_dvd_iff.mp h),hdeg.trans ?_,hz⟩
  norm_num only [Nat.cast_one,show (1+2) = 3 by norm_num]
  exact surface_scaled_degree hd hB (by exact_mod_cast S.prime.one_le) S.small
    ((le_mul_of_one_le_right (by positivity) (leading_height_one_le f (ne_zero_of_irreducible_map hir))).trans S.leading_height)
    (by positivity) (Real.exp_pos _).le (surface_prime_charge hir hd hK hB hH hcoeff hheight P hP)

end
end CCDN
