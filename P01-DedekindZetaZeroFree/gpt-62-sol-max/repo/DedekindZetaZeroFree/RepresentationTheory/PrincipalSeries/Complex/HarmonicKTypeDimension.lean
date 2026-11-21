module

public import DedekindZetaZeroFree.Analysis.HarmonicPolynomials.SphereRestriction
public import DedekindZetaZeroFree.Analysis.HarmonicPolynomials.FiniteFischerDecomposition

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.HopfMap
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar
open scoped BigOperators

namespace CompactDimension
open ComplexFractionalInverse
open MvPolynomial

open ComplexFractionalInverse.FiniteFischerRaw

noncomputable def homogeneousSphereBasis (ℓ : ℕ) :
    Module.Basis {d : Fin 3 →₀ ℕ | d.degree = ℓ} ℂ
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
  (MvPolynomial.basisRestrictSupport ℂ {d : Fin 3 →₀ ℕ | d.degree = ℓ}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) ℂ ℓ).symm)
private theorem homogeneousSphere_finrank (ℓ : ℕ) :
    Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) = Nat.multichoose 3 ℓ := by
  classical
  letI := (Finsupp.finite_of_degree_eq (σ := Fin 3) ℓ).fintype
  rw [Module.finrank_eq_card_basis (homogeneousSphereBasis ℓ)]
  have he : {d : Fin 3 →₀ ℕ | d.degree = ℓ} ≃
      ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag ℓ) :=
    Equiv.Set.congr (by
      ext d
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_multichoose]
  simp

noncomputable def homogeneousLaplacian (ℓ : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (ℓ + 2)) →ₗ[ℂ]
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
  (polynomialLaplacian.comp (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (ℓ + 2)).subtype).codRestrict
    _ (fun p => by simpa using lap_hom p.property)
noncomputable def harmonicLaplacianKerEquiv (ℓ : ℕ) :
    harmonicPolynomials (ℓ + 2) ≃ₗ[ℂ] (homogeneousLaplacian ℓ).ker where
  toFun p := ⟨⟨p.val, p.property.1⟩, by
    apply Subtype.ext
    exact p.property.2⟩
  invFun p := ⟨p.val.val, ⟨p.val.property, by
    have hh := p.property
    exact congrArg Subtype.val hh⟩⟩
  left_inv p := rfl
  right_inv p := rfl
  map_add' p q := rfl
  map_smul' c p := rfl
private theorem harmonic_finrank_of_laplacian_surjective (ℓ : ℕ)
    (h : Function.Surjective (homogeneousLaplacian ℓ)) :
    Module.finrank ℂ (harmonicPolynomials (ℓ + 2)) + Nat.multichoose 3 ℓ =
      Nat.multichoose 3 (ℓ + 2) := by
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (ℓ + 2)) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ (ℓ + 2))
  have hh := LinearMap.finrank_range_add_finrank_ker (homogeneousLaplacian ℓ)
  rw [LinearMap.range_eq_top.mpr h, finrank_top,
    homogeneousSphere_finrank, ← (harmonicLaplacianKerEquiv ℓ).finrank_eq] at hh
  simpa [homogeneousSphere_finrank, Nat.add_comm] using hh

private theorem harmonicPolynomials_low_degree {ℓ : ℕ} (hℓ : ℓ ≤ 1) :
    harmonicPolynomials ℓ = MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ := by
  apply le_antisymm inf_le_left
  intro p hp
  exact ⟨hp, lap_low hp hℓ⟩
private theorem harmonicPolynomials_finrank_zero : Module.finrank ℂ (harmonicPolynomials 0) = 1 := by
  rw [harmonicPolynomials_low_degree (by omega), homogeneousSphere_finrank]
  simp []
private theorem harmonicPolynomials_finrank_one : Module.finrank ℂ (harmonicPolynomials 1) = 3 := by
  rw [harmonicPolynomials_low_degree (by omega), homogeneousSphere_finrank]
  simp []
private theorem harmonic_dimension_of_laplacian_surjective (ℓ : ℕ)
    (h : Function.Surjective (homogeneousLaplacian ℓ)) :
    Module.finrank ℂ (harmonicPolynomials (ℓ + 2)) = 2 * (ℓ + 2) + 1 := by
  have hh := harmonic_finrank_of_laplacian_surjective ℓ h
  have hm : Nat.multichoose 3 (ℓ + 2) = Nat.multichoose 3 ℓ + (2 * (ℓ + 2) + 1) := by
    have h1 := Nat.multichoose_succ_succ 2 (ℓ + 1)
    have h2 := Nat.multichoose_succ_succ 2 ℓ
    simp only [Nat.multichoose_two] at h1 h2
    change Nat.multichoose 3 (ℓ + 2) = (ℓ + 1 + 1 + 1) + Nat.multichoose 3 (ℓ + 1) at h1
    change Nat.multichoose 3 (ℓ + 1) = (ℓ + 1 + 1) + Nat.multichoose 3 ℓ at h2
    omega
  omega

private theorem homogeneousLaplacian_surjective (n : ℕ) :
    Function.Surjective (homogeneousLaplacian n) := by
  intro p
  obtain ⟨q, hq, hp⟩ := exists_radial_preimage p.property
  exact ⟨⟨radiusQuadratic * q, by simpa [Nat.add_comm] using radius_homogeneous.mul hq⟩,
    Subtype.ext hp⟩

private theorem finrank_harmonicPolynomials (ℓ : ℕ) :
    Module.finrank ℂ (harmonicPolynomials ℓ) = 2 * ℓ + 1 := by
  rcases ℓ with _ | _ | ℓ
  · simpa using harmonicPolynomials_finrank_zero
  · simpa using harmonicPolynomials_finrank_one
  · exact harmonic_dimension_of_laplacian_surjective ℓ (homogeneousLaplacian_surjective ℓ)

private theorem harmonicSphere_injective (ℓ : ℕ) :
    Function.Injective (fun p : harmonicPolynomials ℓ => polynomialSphere p.val) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply homogeneous_sphere_eq_zero (p.property.1.sub q.property.1)
  intro x
  simpa [polynomialSphere, map_sub] using sub_eq_zero.mpr (congrFun hpq x)

end CompactDimension

open ComplexFractionalInverse (Ambient hopf_surjective hopf_complex_coordinates)

theorem polynomialCompactHarmonics_finrank (ℓ : ℕ) :
    Module.finrank ℂ ((harmonicPolynomials ℓ).map polynomialCompactRestriction) =
      2 * ℓ + 1 := by
  let f : harmonicPolynomials ℓ →ₗ[ℂ]
      ((harmonicPolynomials ℓ).map polynomialCompactRestriction) :=
    (polynomialCompactRestriction.domRestrict (harmonicPolynomials ℓ)).codRestrict _
      (fun p => Submodule.mem_map.mpr ⟨p, p.property, rfl⟩)
  have hinj : Function.Injective f := by
    intro p q hpq
    apply CompactDimension.harmonicSphere_injective ℓ
    funext x
    obtain ⟨k, hk⟩ := hopf_surjective x
    have h := congrFun (congrArg Subtype.val hpq) k
    change MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) p.val =
      MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) q.val
    rw [← hk, hopf_complex_coordinates]
    exact h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp y.property
    refine ⟨⟨p, hp⟩, ?_⟩
    exact Subtype.ext he
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq.symm.trans
    (CompactDimension.finrank_harmonicPolynomials ℓ)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
