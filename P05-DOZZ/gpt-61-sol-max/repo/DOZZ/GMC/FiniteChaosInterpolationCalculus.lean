/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMass
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Pointwise calculus for the finite-chaos Kahane interpolation path. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions NNReal

namespace DOZZ.Proofs

variable {ΩX ΩY ι : Type*} [_inst1 : Fintype ι] (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ) (vX vY a : ι → ℝ) (γ t : ℝ) (ω : ΩX × ΩY)

include ΩX ΩY ι _inst1 X Y vX vY a γ t ω in
/-- The Wick-normalized finite chaos mass along the independent Gaussian interpolation path. -/
noncomputable def kahaneInterpolatedMass
     : ℝ :=
  ∑ i, a i * Real.exp
    (γ * (Real.sqrt t * X ω.1 i + Real.sqrt (1 - t) * Y ω.2 i) -
      γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i))

include ΩX ΩY ι _inst1 X Y vX vY a γ t ω in
/-- At an interior interpolation time, the derivative of the finite chaos mass is the sum of the
coordinate derivatives, including the derivative of the Wick variance normalization. -/
theorem kahaneInterpolatedMass_hasDerivAt

    (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => kahaneInterpolatedMass X Y vX vY a γ s ω)
      (∑ i, a i * Real.exp
        (γ * (Real.sqrt t * X ω.1 i + Real.sqrt (1 - t) * Y ω.2 i) -
          γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i)) *
        (γ * (X ω.1 i / (2 * Real.sqrt t) -
            Y ω.2 i / (2 * Real.sqrt (1 - t))) -
          γ ^ 2 / 2 * (vX i - vY i))) t := by
  classical
  have hA  := Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hB : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s))
      (-1 / (2 * Real.sqrt (1 - t))) t := by
    have ht1pos : 0 < 1 - t := by linarith
    have hinner : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1
      · ext s
        simp [id_eq]
      · ring
    have hs := (Real.hasDerivAt_sqrt (ne_of_gt ht1pos)).comp t hinner
    convert hs using 1
    · ext s
      rfl
    · ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i hi => by
    let E : ℝ → ℝ := fun s =>
      γ * (Real.sqrt s * X ω.1 i + Real.sqrt (1 - s) * Y ω.2 i) -
        γ ^ 2 / 2 * (s * vX i + (1 - s) * vY i)
    have hfield : HasDerivAt
        (fun s => Real.sqrt s * X ω.1 i + Real.sqrt (1 - s) * Y ω.2 i)
        (X ω.1 i / (2 * Real.sqrt t) -
          Y ω.2 i / (2 * Real.sqrt (1 - t))) t := by
      convert (hA.const_mul (X ω.1 i)).add (hB.const_mul (Y ω.2 i)) using 1
      · ext s
        change Real.sqrt s * X ω.1 i + Real.sqrt (1 - s) * Y ω.2 i =
          X ω.1 i * Real.sqrt s + Y ω.2 i * Real.sqrt (1 - s)
        rw [mul_comm (Real.sqrt s) (X ω.1 i),
          mul_comm (Real.sqrt (1 - s)) (Y ω.2 i)]
      · ring
    have hvar : HasDerivAt (fun s => s * vX i + (1 - s) * vY i)
        (vX i - vY i) t := by
      convert (hasDerivAt_id t).const_mul (vX i) |>.add
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) |>.const_mul (vY i))
        using 1
      · ext s
        change s * vX i + (1 - s) * vY i =
          vX i * s + vY i * (1 - s)
        ring
      · ring
    have hE : HasDerivAt E
        (γ * (X ω.1 i / (2 * Real.sqrt t) -
          Y ω.2 i / (2 * Real.sqrt (1 - t))) -
          γ ^ 2 / 2 * (vX i - vY i)) t := by
      dsimp [E]
      convert (hfield.const_mul γ).sub (hvar.const_mul (γ ^ 2 / 2)) using 1
    have hterm := (Real.hasDerivAt_exp (E t)).comp t hE
    have hscaled := hterm.const_mul (a i)
    exact hscaled)
  convert hsum using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro i hi
    ring

include ΩX ΩY ι _inst1 X Y vX vY a γ t ω in
/-- Applying a differentiable scalar test to the interpolated finite chaos mass. -/
theorem kahaneInterpolatedTest_hasDerivAt

    (F F' : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (F' x) x)
    (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => F (kahaneInterpolatedMass X Y vX vY a γ s ω))
      (F' (kahaneInterpolatedMass X Y vX vY a γ t ω) *
        ∑ i, a i * Real.exp
          (γ * (Real.sqrt t * X ω.1 i + Real.sqrt (1 - t) * Y ω.2 i) -
            γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i)) *
          (γ * (X ω.1 i / (2 * Real.sqrt t) -
              Y ω.2 i / (2 * Real.sqrt (1 - t))) -
            γ ^ 2 / 2 * (vX i - vY i))) t := by
  have hmass := kahaneInterpolatedMass_hasDerivAt X Y vX vY a γ t ω ht ht1
  exact (hF (kahaneInterpolatedMass X Y vX vY a γ t ω)).comp t hmass

/-- One Wick weight and the full finite chaos sum as deterministic functions of a field vector. -/
noncomputable def finiteChaosVectorWeight {ι : Type*}
    (a v : ι → ℝ) (γ : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  a i * Real.exp (γ * x i - γ ^ 2 / 2 * v i)

noncomputable def finiteChaosVectorMass {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (γ : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, finiteChaosVectorWeight a v γ x i

/-- Directional differentiation of one Wick weight times the scalar test derivative. The result
is the covariance-contraction form needed when Gaussian IBP shifts the whole field vector. -/
theorem finiteChaosVectorTestWeight_directional_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ : ℝ) (F' F'' : ℝ → ℝ)
    (hF' : ∀ z, HasDerivAt F' (F'' z) z)
    (x d : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s => finiteChaosVectorWeight a v γ (fun j => x j + s * d j) i *
        F' (finiteChaosVectorMass a v γ (fun j => x j + s * d j)))
      (∑ j, d j *
        (γ * (if i = j then
          finiteChaosVectorWeight a v γ (fun k => x k + t * d k) i *
            F' (finiteChaosVectorMass a v γ (fun k => x k + t * d k)) else 0) +
          γ * finiteChaosVectorWeight a v γ (fun k => x k + t * d k) i *
            finiteChaosVectorWeight a v γ (fun k => x k + t * d k) j *
              F'' (finiteChaosVectorMass a v γ (fun k => x k + t * d k)))) t := by
  classical
  let z  := fun s j => x j + s * d j
  have hz (j : ι) : HasDerivAt (z · j) (d j) t := by
    convert ((hasDerivAt_id t).const_mul (d j)).add
      (hasDerivAt_const t (x j)) using 1
    · ext s
      change x j + s * d j = d j * s + x j
      ring
    · ring
  have hweight (j : ι) : HasDerivAt
      (fun s => finiteChaosVectorWeight a v γ (z s) j)
      (γ * d j * finiteChaosVectorWeight a v γ (z t) j) t := by
    have hlin : HasDerivAt (fun s => γ * z s j - γ ^ 2 / 2 * v j)
        (γ * d j) t := by
      convert ((hz j).const_mul γ).sub
        (hasDerivAt_const t (γ ^ 2 / 2 * v j)) using 1
      ring
    have hexp := (Real.hasDerivAt_exp
      (γ * z t j - γ ^ 2 / 2 * v j)).comp t hlin
    convert hexp.const_mul (a j) using 1
    · simp [finiteChaosVectorWeight]
    · simp [finiteChaosVectorWeight]
      ring
  have hmass : HasDerivAt (fun s => finiteChaosVectorMass a v γ (z s))
      (∑ j, γ * d j * finiteChaosVectorWeight a v γ (z t) j) t := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j hj => hweight j)
    exact hsum
  have hFcomp : HasDerivAt (fun s => F' (finiteChaosVectorMass a v γ (z s)))
      (F'' (finiteChaosVectorMass a v γ (z t)) *
        (∑ j, γ * d j * finiteChaosVectorWeight a v γ (z t) j)) t :=
    (hF' (finiteChaosVectorMass a v γ (z t))).comp t hmass
  have hprod := (hweight i).mul hFcomp
  convert hprod using 1
  let w  := finiteChaosVectorWeight a v γ (z t)
  let m  := finiteChaosVectorMass a v γ (z t)
  have hdiag : (∑ j, d j * (γ * (if i = j then w i * F' m else 0))) =
      γ * d i * w i * F' m := by
    rw [Finset.sum_eq_single i]
    · simp [w, m]
      ring
    · intro j hj hne
      have hij : i ≠ j := fun h => hne h.symm
      simp [hij]
    · simp
  have hmix : (∑ j, d j * (γ * w i * w j * F'' m)) =
      (γ * w i * F'' m) * ∑ j, d j * w j := by
    calc
      _ = ∑ j, (γ * w i * F'' m) * (d j * w j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (γ * w i * F'' m) * ∑ j, d j * w j := by rw [Finset.mul_sum]
  have hsum : (∑ j, γ * d j * w j) = γ * ∑ j, d j * w j := by
    calc
      _ = ∑ j, γ * (d j * w j) := by
        noncomm_ring
      _ = γ * ∑ j, d j * w j := by rw [Finset.mul_sum]
  calc
    (∑ j, d j *
        (γ * (if i = j then
          finiteChaosVectorWeight a v γ (fun k => x k + t * d k) i *
            F' (finiteChaosVectorMass a v γ (fun k => x k + t * d k)) else 0) +
          γ * finiteChaosVectorWeight a v γ (fun k => x k + t * d k) i *
            finiteChaosVectorWeight a v γ (fun k => x k + t * d k) j *
              F'' (finiteChaosVectorMass a v γ (fun k => x k + t * d k))))
        = (∑ j, d j * (γ * (if i = j then w i * F' m else 0))) +
          ∑ j, d j * (γ * w i * w j * F'' m) := by
          simp only [w, m, z]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
    _ = γ * d i * w i * F' m +
          (γ * w i * F'' m) * ∑ j, d j * w j := by rw [hdiag, hmix]
    _ = γ * d i * w i * F' m +
          w i * (F'' m * ∑ j, γ * d j * w j) := by
          rw [hsum]
          ring
    _ = γ * d i * finiteChaosVectorWeight a v γ (z t) i *
          F' (finiteChaosVectorMass a v γ (z t)) +
        finiteChaosVectorWeight a v γ (z t) i *
          (F'' (finiteChaosVectorMass a v γ (z t)) *
            ∑ j, γ * d j * finiteChaosVectorWeight a v γ (z t) j) := rfl

end DOZZ.Proofs
