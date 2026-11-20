module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FiniteFischerRaw
open KPCplxIntertwinerEigenvalues
open scoped BigOperators
open MvPolynomial

noncomputable def radiusQuadratic : MvPolynomial (Fin 3) ℂ :=
  ∑ i : Fin 3, MvPolynomial.X i ^ 2

private lemma deriv_radius (i : Fin 3) :
    pderiv i radiusQuadratic = 2 * X i := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.EquivariantFischer.deriv_radius <;> assumption
private lemma radius_homogeneous : radiusQuadratic.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i hi
  exact isHomogeneous_X_pow i 2
private lemma lap_radius_mul (q : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (radiusQuadratic * q) =
      radiusQuadratic * polynomialLaplacian q + 6 * q +
        4 * ∑ i : Fin 3, X i * pderiv i q := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.EquivariantFischer.lap_radius_mul <;> assumption
private lemma lap_radius_hom {q : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hq : q.IsHomogeneous d) :
    polynomialLaplacian (radiusQuadratic * q) =
      radiusQuadratic * polynomialLaplacian q +
        (2 * (2 * (d : ℂ) + 3)) • q := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.EquivariantFischer.lap_radius_hom <;> assumption

theorem laplacian_radius_pow {q : MvPolynomial (Fin 3) ℂ} {degree : ℕ}
    (hq : q.IsHomogeneous degree) (k : ℕ) :
    polynomialLaplacian (radiusQuadratic ^ k * q) =
      radiusQuadratic ^ k * polynomialLaplacian q +
        (2 * (k : ℂ) * (2 * (degree : ℂ) + 2 * (k : ℂ) + 1)) •
          (radiusQuadratic ^ (k - 1) * q) := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.laplacian_radius_pow <;> assumption

section

variable {p : MvPolynomial (Fin 3) ℂ} {n : ℕ}

private lemma lap_hom
    (hp : p.IsHomogeneous n) : (polynomialLaplacian p).IsHomogeneous (n - 2) := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.lap_hom <;> assumption
private lemma lap_low
    (hp : p.IsHomogeneous n) (hn : n ≤ 1) : polynomialLaplacian p = 0 := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.EquivariantFischer.lap_low <;> assumption
private lemma harmonic_smul
    (hp : p ∈ harmonicPolynomials n) (c : ℂ) : c • p ∈ harmonicPolynomials n :=
  (harmonicPolynomials n).smul_mem c hp
private lemma radial_inverse
    (hp : p ∈ harmonicPolynomials n) (k : ℕ) :
    polynomialLaplacian (radiusQuadratic ^ (k + 1) *
      ((2 * ((k + 1 : ℕ) : ℂ) * (2 * (n : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) + 1))⁻¹ • p)) =
      radiusQuadratic ^ k * p := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.EquivariantFischer.radial_inverse <;> assumption

end

theorem homogeneous_fischer {p : MvPolynomial (Fin 3) ℂ} {degree : ℕ}
    (hp : p.IsHomogeneous degree) :
    ∃ h : ℕ → MvPolynomial (Fin 3) ℂ,
      (∀ k ≤ degree / 2, h k ∈ harmonicPolynomials (degree - 2 * k)) ∧
      p = ∑ k ∈ Finset.range (degree / 2 + 1), radiusQuadratic ^ k * h k := by apply @DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw.homogeneous_fischer <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse.FiniteFischerRaw
