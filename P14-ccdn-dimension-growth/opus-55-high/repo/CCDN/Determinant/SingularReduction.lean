/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.PlaneMultiplicity
import CCDN.Plane.FiniteFieldConstants
import CCDN.Determinant.BlockDeterminant
import CCDN.Determinant.ResidueAggregation

/-! All reduced points, their positive multiplicities, and the resulting
local determinant lower bound. The sharp finite-field total-multiplicity
estimate is a separate geometric obligation. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable (f : MvPolynomial (Fin 2) ℤ)

lemma cast_plane_eval {p : ℕ} (z : Fin 2 → ℤ) :
    (MvPolynomial.eval z f : ZMod p) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (z j : ZMod p)) f := by
  simpa [MvPolynomial.eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
    MvPolynomial.eval₂_comp_left (Int.castRingHom (ZMod p)) (RingHom.id ℤ) z f

/-- All affine rational points of the reduced plane equation. -/
def PlaneResidue (p : ℕ) :=
  {a : Fin 2 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) a f = 0}

end

instance (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [NeZero p] :
    Fintype (PlaneResidue f p) := by
  unfold PlaneResidue
  infer_instance

/-- The finite-field point-count hypothesis for one plane equation `f`, with degree
parameter `d` and constant `C`: at every prime `p > stepanovThreshold d` where `f` has
irreducible reduction, `f` has at most `p + C d² √p` zeros in `𝔽_p²`. `PlaneResidueBound C`
asserts it for every equation with `d = deg f`, and `planeResidueBound` proves it with
`C = planeResidueConstant`. -/
def PlaneResidueCountBound (C : ℝ) (d : ℕ) (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → stepanovThreshold (d : ℝ) < p →
    Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) f) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (d : ℝ) ^ 2 * Real.sqrt p

section
variable {f : MvPolynomial (Fin 2) ℤ} {p : ℕ} (a : PlaneResidue f p)

/-- The integer lift, with coordinates in `[0, p)`, of an `𝔽_p`-point of the reduced affine plane
curve. -/
def planeResidueLift :
    Fin 2 → ℤ := fun j => (a.val j).val

/-- The integer lift of a residue point reduces modulo `p` to the point itself. -/
lemma cast_planeResidueLift [NeZero p]
    (j : Fin 2) : (planeResidueLift a j : ZMod p) = a.val j := by
  simp [planeResidueLift]

/-- The reduction of `f` modulo `p` vanishes at the reduction of the integer lift of a residue point
of `f`. -/
lemma planeResidueLift_zero [NeZero p]
    :
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (planeResidueLift a j : ZMod p)) f = 0 := by
  simpa [cast_planeResidueLift] using a.property

end

section
variable (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime] (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)

/-- Multiplicity is selected from the translated reduced equation. -/
def planeResidueMultiplicity
    (a : PlaneResidue f p) : ℕ :=
  Classical.choose (exists_hypersurface_reduction_multiplicity f (planeResidueLift a) hf
    (planeResidueLift_zero a))

/-- The multiplicity of `f mod p` at a residue point `a` is between `1` and the total degree of `f`;
after translating `a` to the origin, the reduced equation lies in that power of the ideal of the
origin and has a nonzero homogeneous component of that degree. -/
theorem planeResidueMultiplicity_spec
    (a : PlaneResidue f p) :
    0 < planeResidueMultiplicity f p hf a ∧
      planeResidueMultiplicity f p hf a ≤ f.totalDegree ∧
      map (Int.castRingHom (ZMod p)) (originShift (planeResidueLift a) f) ∈
        idealOfVars (Fin 2) (ZMod p) ^ planeResidueMultiplicity f p hf a ∧
      homogeneousComponent (planeResidueMultiplicity f p hf a)
        (map (Int.castRingHom (ZMod p)) (originShift (planeResidueLift a) f)) ≠ 0 :=
  Classical.choose_spec (exists_hypersurface_reduction_multiplicity f (planeResidueLift a) hf
    (planeResidueLift_zero a))

/-- The finite-field total multiplicity appearing in the denominator
of the local determinant exponent. -/
def planeTotalMultiplicity
    : ℕ :=
  ∑ a : PlaneResidue f p, planeResidueMultiplicity f p hf a

lemma planeTotalMultiplicity_bounds
    :
    Fintype.card (PlaneResidue f p) ≤ planeTotalMultiplicity f p hf ∧
      planeTotalMultiplicity f p hf ≤ Fintype.card (PlaneResidue f p) * f.totalDegree := by
  constructor
  · calc _ = ∑ _a : PlaneResidue f p, 1 := by simp
         _ ≤ _ := Finset.sum_le_sum fun a _ => (planeResidueMultiplicity_spec f p hf a).1
  · calc _ ≤ ∑ _a : PlaneResidue f p, f.totalDegree :=
           Finset.sum_le_sum fun a _ => (planeResidueMultiplicity_spec f p hf a).2.1
         _ = _ := by simp

end

