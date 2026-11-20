/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.OriginShift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Positive singular multiplicity is derived from a nonzero equation
vanishing at the origin; it is bounded by the equation's total degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The order at the origin: least nonzero homogeneous degree. -/
def originMultiplicity {K σ : Type*} [Field K] (f : MvPolynomial σ K) : ℕ :=
  sInf {n | homogeneousComponent n f ≠ 0}

private theorem originMultiplicity_spec {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hz : eval (0 : σ → K) f = 0) :
    0 < originMultiplicity f ∧ originMultiplicity f ≤ f.totalDegree ∧
      f ∈ idealOfVars σ K ^ originMultiplicity f ∧ homogeneousComponent (originMultiplicity f) f ≠ 0 := by
  classical
  have htop := homogeneousComponent_totalDegree_ne_zero hf
  let S := {d | homogeneousComponent d f ≠ 0}
  have htop' : f.totalDegree ∈ S := htop
  have hμ : homogeneousComponent (originMultiplicity f) f ≠ 0 := Nat.sInf_mem ⟨_, htop'⟩
  refine ⟨?_, Nat.sInf_le htop', ?_, hμ⟩
  · by_contra! h
    have he : originMultiplicity f = 0 := by omega
    apply hμ
    simpa [he, homogeneousComponent_zero, eval_zero, constantCoeff_eq] using congrArg (C (σ := σ)) hz
  · rw [mem_pow_idealOfVars_iff']
    intro e he
    have hzero : homogeneousComponent e.degree f = 0 := by
      by_contra hn
      exact (not_le_of_gt he) (Nat.sInf_le (s := {n | homogeneousComponent n f ≠ 0}) hn)
    simpa [coeff_homogeneousComponent] using congrArg (fun u : MvPolynomial σ K => u.coeff e) hzero

/-- At a reduced zero the translated equation has positive multiplicity, at most the degree. -/
theorem reduction_originMultiplicity_spec {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0) :
    let g := map (Int.castRingHom (ZMod p)) (originShift a f)
    let μ := originMultiplicity g
    0 < μ ∧ μ ≤ f.totalDegree ∧ g ∈ idealOfVars σ (ZMod p) ^ μ ∧ homogeneousComponent μ g ≠ 0 := by
  dsimp only
  rw [originShift_map]
  have hn := originShift_ne_zero (fun j => (a j : ZMod p)) hf
  have hz : eval (0 : σ → ZMod p) (originShift (fun j => (a j : ZMod p)) (map (Int.castRingHom (ZMod p)) f)) = 0 := by
    rw [eval_zero_originShift, eval_map]
    exact ha
  obtain ⟨hpos, hdeg, rest⟩ := originMultiplicity_spec _ hn hz
  exact ⟨hpos, hdeg.trans ((originShift_totalDegree_le ..).trans (totalDegree_map_le ..)), rest⟩

end
end CCDN
