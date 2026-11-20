/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Determinant.MinorGcd
public import CCDN.Algebra.OriginShift
public import Mathlib.Algebra.Field.ZMod
public import CCDN.Determinant.LocalDeterminant
public import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.ForMathlib.MvPolynomial

/-! Positive singular multiplicity is derived from a nonzero equation
vanishing at the origin; it is bounded by the equation's total degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The first nonzero homogeneous component realizes the order at the origin. -/
theorem exists_origin_multiplicity {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hz : eval (0 : σ → K) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      f ∈ idealOfVars σ K ^ μ ∧ homogeneousComponent μ f ≠ 0 := by
  classical
  have hex : ∃ n, homogeneousComponent n f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    rw [← sum_homogeneousComponent f]
    aesop
  let μ := Nat.find hex
  have hμ := Nat.find_spec hex
  have hpow : f ∈ idealOfVars σ K ^ μ := by
    rw [mem_pow_idealOfVars_iff']
    intro e he
    simpa [coeff_homogeneousComponent] using (congrArg (fun u : MvPolynomial σ K => u.coeff e) (not_not.mp (Nat.find_min hex he)))
  have hpos : 0 < μ := by
    by_contra h
    have hconst := by simpa [constantCoeff_eq] using hz
    aesop
  have hdeg : μ ≤ f.totalDegree := by
    by_contra h
    exact hμ (homogeneousComponent_eq_zero μ f (by omega))
  exact ⟨μ, hpos, hdeg, hpow, hμ⟩

/-- A reduced hypersurface point determines a positive, degree-bounded
multiplicity in every ambient dimension. -/
theorem exists_hypersurface_reduction_multiplicity {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (hf : residueEquation p f ≠ 0)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      residueEquation p (originShift a f) ∈ idealOfVars σ (ZMod p) ^ μ ∧
      homogeneousComponent μ (residueEquation p (originShift a f)) ≠ 0 := by
  let φ := Int.castRingHom (ZMod p)
  have hshift := originShift_map φ a f
  have hn : map φ (originShift a f) ≠ 0 := by
    rw [hshift]
    exact originShift_ne_zero _ hf
  have hz : eval (0 : σ → ZMod p) (map φ (originShift a f)) = 0 := by
    rw [hshift, eval_zero_originShift, eval_map]
    exact ha
  have hdeg := (totalDegree_map_le φ (originShift a f)).trans (originShift_totalDegree_le a f)
  obtain ⟨μ, hpos, hμdeg, hpow, hμ⟩ := exists_origin_multiplicity _ hn hz
  exact ⟨μ, hpos, hμdeg.trans hdeg, hpow, hμ⟩

end
end CCDN
