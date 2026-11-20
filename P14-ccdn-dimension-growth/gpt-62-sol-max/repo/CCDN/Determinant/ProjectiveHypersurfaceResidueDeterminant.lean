/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.BlockDeterminant
public import CCDN.Determinant.ProjectiveHypersurfaceReduction
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
import CCDN.Determinant.HypersurfaceMultiplicityEstimate

/-!
Projective hypersurface residue classes give the sharp single-prime
determinant bound in every positive dimension. The residue partition, chart
units and positive local multiplicities are all constructed from the equation.

Sharp aggregation of local hypersurface exponents. Summing the exact
integer cutoff inequalities before optimizing preserves the leading constant
and gives a linear error independent of all residue multiplicities.
-/

@[expose] public section
namespace CCDN
noncomputable section

open MvPolynomial

/-- Every affine chart of a homogeneous integer polynomial whose reduction modulo `p` is nonzero
also has nonzero reduction modulo `p`. -/
lemma projectiveHypersurfaceChart_mod_ne_zero {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (k : Fin (n + 3)) :
    map (Int.castRingHom (ZMod p)) (affineChartAt k f) ≠ 0 := by
  rw [map_affineChartAt]
  apply affineChart_ne_zero_of_homogeneous (hf.map _).rename_isHomogeneous
  exact fun h => hf0 (rename_injective _ (Equiv.swap 0 k).injective (h.trans (map_zero _).symm))

/-- The `𝔽_p`-points of the reduction modulo `p` of the projective hypersurface `f = 0` in `ℙⁿ⁺²`.
-/
def ProjectiveHypersurfaceResidue {n : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ) (p : ℕ)
    [Fact p.Prime] :=
  {r : ProjectiveResidueSpace (n + 2) p | eval r.rep (map (Int.castRingHom (ZMod p)) f) = 0}

instance {n : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ) (p : ℕ) [Fact p.Prime] :
    Fintype (ProjectiveHypersurfaceResidue f p) := Fintype.ofFinite _

/-- The multiplicity in the affine chart of a projective residue point. -/
def projectiveHypersurfaceResidueMultiplicity {n p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (r : ProjectiveHypersurfaceResidue f p) : ℕ :=
  originMultiplicity (map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val)
    (affineChartAt (hypersurfaceResiduePivot r.val) f)))

/-- The multiplicity and the first nonzero term in the chart of a residue point. -/
theorem projectiveHypersurfaceResidueMultiplicity_spec {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectiveHypersurfaceResidue f p) :
    let g := map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val)
      (affineChartAt (hypersurfaceResiduePivot r.val) f))
    let μ := projectiveHypersurfaceResidueMultiplicity (p := p) f r
    0 < μ ∧ μ ≤ d ∧ g ∈ idealOfVars (Fin (n + 2)) (ZMod p) ^ μ ∧ homogeneousComponent μ g ≠ 0 := by
  have h := reduction_originMultiplicity_spec _ _
    (projectiveHypersurfaceChart_mod_ne_zero f hf hf0 _) (hypersurfaceResidueChartLift_zero f hf r.val r.property)
  exact ⟨h.1, h.2.1.trans ((affineChart_totalDegree_le _).trans hf.rename_isHomogeneous.totalDegree_le), h.2.2⟩

/-- The total residue multiplicity of the projective hypersurface `f = 0` modulo `p`: the sum of the
multiplicities of `f mod p` at all of its `𝔽_p`-points. This is the quantity of CCDN Proposition
2.6. -/
def projectiveHypersurfaceTotalMultiplicity {n : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  ∑ r : ProjectiveHypersurfaceResidue f p, projectiveHypersurfaceResidueMultiplicity f r

/-- The total residue multiplicity of `f mod p` lies between the number of its `𝔽_p`-points and `d`
times that number. -/
theorem projectiveHypersurfaceTotalMultiplicity_bounds {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) :
    Fintype.card (ProjectiveHypersurfaceResidue f p) ≤
      projectiveHypersurfaceTotalMultiplicity f p ∧
    projectiveHypersurfaceTotalMultiplicity f p ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) * d := by
  constructor
  · calc _ = ∑ _r : ProjectiveHypersurfaceResidue f p, 1 := by simp
         _ ≤ _ :=
           Finset.sum_le_sum fun r _ =>
             (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).1
  · calc _ ≤ ∑ _r : ProjectiveHypersurfaceResidue f p, d :=
           Finset.sum_le_sum fun r _ =>
             (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).2.1
         _ = _ := by simp

/-- Primitive zeros construct all local data. The resulting divisor has the
sharp leading constant in terms of the total residue multiplicity. -/
theorem projective_hypersurface_reduction_minorGcd {n s N p d M : ℕ}
    [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    0 < projectiveHypersurfaceTotalMultiplicity f p ∧ ∃ e : ℕ,
      (∀ K : ℕ, s * K ≤ e + projectiveHypersurfaceTotalMultiplicity f p *
        (n + 1 + K).choose (n + 2)) ∧
      (p : ℤ) ^ e ∣ minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  let red : Fin s → ProjectiveHypersurfaceResidue f p := fun i =>
    ⟨primitiveProjectiveReduction (z i) (hprim i),
      primitiveProjectiveReduction_zero f hf (z i) (hprim i) (hz i)⟩
  let μ := projectiveHypersurfaceResidueMultiplicity (p := p) f
  let sizes := fun r : ProjectiveHypersurfaceResidue f p => Fintype.card {i // red i = r}
  let e (r) := hypersurfaceMultiplicityExponent (n + 1) (μ r) (sizes r)
  have hμ r := projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r
  refine ⟨(Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩).trans_le
    (projectiveHypersurfaceTotalMultiplicity_bounds f hf hf0).1, ∑ r, e r, ?_, ?_⟩
  · intro K
    have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
      hypersurfaceMultiplicityExponent_cutoff_pos (n + 1) (sizes r) K (by omega) (hμ r).1)
    simpa only [Finset.sum_add_distrib, ← Finset.sum_mul, sizes, sum_residue_class_sizes red,
      projectiveHypersurfaceTotalMultiplicity, e, μ] using h
  · apply residue_prime_powers_dvd_minorGcd _ red
    intro r cols
    let k := hypersurfaceResiduePivot r.val
    let a := hypersurfaceResidueChartLift r.val
    let rows := residueRows red r
    have hv (i) := primitiveProjectiveReduction_hypersurface_chart
      (z (rows i)) (hprim (rows i)) r.val (congrArg Subtype.val (residueRows_label red r i))
    exact projective_hypersurface_local_det_divisibility f hf (F ∘ cols) (fun _ => hF _)
      (z ∘ rows) k a (hμ r).2.2.1 (hμ r).2.2.2 (fun i => (hv i).1) (fun i => (hv i).2) (fun _ => hz _)

end
end CCDN
