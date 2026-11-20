/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Projection.BoundedIntegerNormalization
public import CCDN.Projection.CurvePrimitivePair
public import CCDN.Projection.ImageFractionField
import CCDN.Projection.ClosureBirationalDegree
import CCDN.Hilbert.PrincipalHilbertPolynomial
import CCDN.Projection.LeadingCoordinateExtension
import CCDN.Projection.LinearParameterPrimitive

/-! A bounded integer linear finite birational projection of a
prime quotient to a hypersurface of exactly the same degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient bound for the birational hypersurface projection in `n` variables and degree
`d`: the maximum of the normalization height and `(n * d ^ 2 + 1) ^ n`, which bounds the moment
row. -/
def integerBirationalProjectionHeight (n d : ℕ) : ℕ :=
  max (integerNormalizationHeight n d) ((n * d ^ 2 + 1) ^ n)

/-- Prepending the integer moment row `(t ^ j)_j` to integer rows realizes the moment
coordinate as the leading linear form. -/
theorem integerLinearForm_moment_cons {m n : ℕ} (t : ℕ) (a : Fin (m + 1) → Fin n → ℤ) :
    (fun i => integerLinearForm
      ((Fin.cases (fun j => (t : ℤ) ^ j.val) a : Fin (m + 2) → Fin n → ℤ) i)) =
      Fin.cases (momentCoordinate ℚ n t) (fun i => integerLinearForm (a i)) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  simp [integerLinearForm, linearForm, momentCoordinate]

/-- Prepending the moment row with parameter `t ≤ n d²` to rows bounded by the normalization
height keeps every entry within the birational projection height. -/
theorem moment_cons_abs_le_integerBirationalProjectionHeight {m n d t : ℕ}
    (ht : t ≤ n * d ^ 2) (a : Fin (m + 1) → Fin n → ℤ)
    (ha : ∀ i j, |a i j| ≤ integerNormalizationHeight n d) (i : Fin (m + 2)) (j : Fin n) :
    |(Fin.cases (fun j => (t : ℤ) ^ j.val) a : Fin (m + 2) → Fin n → ℤ) i j| ≤
      integerBirationalProjectionHeight n d := by
  refine Fin.cases ?_ (fun s => ?_) i
  · change |(t : ℤ) ^ j.val| ≤ _
    have hp := by
      calc
        _ ≤ (n * d ^ 2 + 1) ^ j.val :=
          Nat.pow_le_pow_left (ht.trans (Nat.le_succ _)) _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt j.isLt)
    exact_mod_cast hp.trans (le_max_right _ _)
  · exact (ha s j).trans (by
      exact_mod_cast le_max_left _ _)

private lemma closure_integral_of_tail {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (l : Fin (m+1) → MvPolynomial (Fin n) K)
    (h : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates fun i : Fin m => l i.succ)).IsIntegral) :
    (projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates l)).IsIntegral := by
  let e : Fin _ → Fin (m+2) := Fin.cons 0 fun j => j.succ.succ
  let φ := projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates l)
  have he : φ.comp (rename e) = projectionCoordinateMap _
      (closureProjectionCoordinates fun i : Fin m => l i.succ) := by
    ext i
    simp only [φ, projectionCoordinateMap, AlgHom.comp_apply, rename_X, aeval_X]
    exact Fin.cases rfl (fun _ => rfl) i
  apply RingHom.IsIntegral.tower_top (rename e).toRingHom φ.toRingHom
  change (φ.comp (rename e)).IsIntegral
  rwa [he]

/-- A bounded primitive augmentation of the constructed normalization
produces a irreducible equation of exactly the original degree. -/
private theorem exists_bounded_birational_hypersurface_projection
    (m k : ℕ) (I : Ideal (CoordinatePolynomial (m + 1 + k))) [I.IsPrime]
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin (m + 1 + k) → ℤ) (f : CoordinatePolynomial (m + 2)),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + 1 + k) d) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      f.totalDegree = d := by
  classical
  let n := m + 1 + k
  let F := FractionRing (CoordinatePolynomial n ⧸ I)
  obtain ⟨a, ha, hinta, hinja, hcone⟩ := exists_bounded_integer_closure_normalization m k I d hdimdeg
  obtain ⟨t, ht, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I _ (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  let b : Fin _ → Fin n → ℤ := Fin.cases (fun j => t ^ j.val) a
  let l := fun i => integerLinearForm (b i)
  have hfield' : IntermediateField.adjoin ℚ (Set.range (fun i =>
      algebraMap _ F ((Ideal.Quotient.mk I) (l i)))) = ⊤ := by
    have hl : l = Fin.cases _ (fun i => integerLinearForm (a i)) :=
      integerLinearForm_moment_cons t a
    rwa [hl]
  obtain ⟨f,hf,hpos,_,hker⟩ := exists_extended_projection_equation_degree_le I l
    (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  have hlc := closure_finite_birational_leadingCoeff_eq I l (fun i => linearForm_isHomogeneous _)
    (closure_integral_of_tail I l hcone) hfield'
  rw [hker, principal_filteredHilbertPolynomial_leadingCoeff f hf.ne_zero hpos,
    hdimdeg.leadingCoeff_eq] at hlc
  have hfdeg := by exact_mod_cast (div_left_inj' (by positivity)).mp hlc
  exact ⟨b, f, moment_cons_abs_le_integerBirationalProjectionHeight ht a ha, ⟨hinta, hinja⟩,
    ⟨⟨hfield', hf, hker⟩, projectionCoordinateMap_isIntegral_of_tail I l hinta⟩, hfdeg⟩

/-- A homogeneous prime ideal in `n ≥ m + 1` variables, of projective dimension `m` and
degree `d`, has a bounded integral linear projection to `m + 2` coordinates: the integer
coefficients are bounded by `integerBirationalProjectionHeight n d`, the projection is integral
and birational, and its kernel is generated by an irreducible homogeneous form of degree `d`.
The number of variables is arbitrary, not written as `m + 1 + k`. -/
theorem exists_bounded_birational_hypersurface_projection_of_le
    (m n : ℕ) (hmn : m + 1 ≤ n)
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin n → ℤ) (f : CoordinatePolynomial (m + 2)),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      f.totalDegree = d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  solve_by_elim [exists_bounded_birational_hypersurface_projection]

section

/-! The constructed projection has a coefficient bound polynomial in
the degree, with exponent and constant depending only on ambient
dimension. -/

variable (n : ℕ)

/-- The constant `n! * 2 ^ n + (n + 1) ^ n` in the polynomial bound on the birational projection
height in `n` variables. -/
def birationalProjectionHeightConstant : ℕ :=
  n.factorial * 2 ^ n + (n + 1) ^ n

/-- The birational projection height constant is positive. -/
lemma birationalProjectionHeightConstant_pos :
    0 < birationalProjectionHeightConstant n := by
  dsimp [birationalProjectionHeightConstant]
  positivity

/-- For degree `d ≥ 1`, the birational projection height in `n` variables is at most
`birationalProjectionHeightConstant n * d ^ (2 * n)`. -/
theorem integerBirationalProjectionHeight_le (d : ℕ) (hd : 1 ≤ d) :
    integerBirationalProjectionHeight n d ≤
      birationalProjectionHeightConstant n * d ^ (2 * n) := by
  have hfirst : integerNormalizationHeight n d ≤
      (n.factorial * 2 ^ n) * d ^ (2 * n) := by
    calc
      _ ≤ n.factorial * (2 * d) ^ n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n.factorial * 2 ^ n) * d ^ n := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hd (by omega))
  have hsecond : (n * d ^ 2 + 1) ^ n ≤ (n + 1) ^ n * d ^ (2 * n) := by
    calc
      _ ≤ ((n + 1) * d ^ 2) ^ n :=
        Nat.pow_le_pow_left (by nlinarith) _
      _ = _ := by grind [Nat.mul_pow, pow_mul]
  apply max_le
  · exact hfirst.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  exact hsecond.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

end

end
end CCDN
