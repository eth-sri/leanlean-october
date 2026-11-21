module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicRaising
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicCharacterExpansion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CharacterAverageOrbitClosure
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CoordinateBoosts

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicPropagation

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

theorem harmonic_le_of_nonzero_vector (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s)) (hinv : IsKInvariant s U)
    (n : ℕ) (v : PrincipalSeries s)
    (hvU : v ∈ U) (hvtype : v ∈ harmonicKType s n) (hv : v ≠ 0) :
    harmonicKType s n ≤ U := by
  have hWinv : IsKInvariant s (U ⊓ harmonicKType s n) := by
    intro k f hf
    exact ⟨hinv k f hf.1, (harmonicKType_multiplicity_one s n).1 k f hf.2⟩
  have hmem : v ∈ U ⊓ harmonicKType s n := ⟨hvU, hvtype⟩
  have hW : U ⊓ harmonicKType s n = harmonicKType s n := by
    rcases (harmonicKType_multiplicity_one s n).2.2.1 (U ⊓ harmonicKType s n)
      inf_le_right hWinv with h | h
    · exact absurd (by rw [h] at hmem; exact hmem) (by simpa using hv)
    · exact h
  rw [← hW]
  exact inf_le_left

end DedekindZetaZeroFree.KPCplxHarmonicPropagation

end

section

namespace DedekindZetaZeroFree.KPCplxLoweringHarmonicDecomposition

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open MvPolynomial
open scoped BigOperators
open ComplexFractionalInverse.FiniteFischerRaw

private theorem partials_commute (i j : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  ext d
  simp only [coeff_pderiv]
  by_cases hij : i = j
  · subst j; rfl
  · simp [Finsupp.single_apply, hij, Ne.symm hij, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm]

private theorem harmonic_partial_mem (n : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials (n + 1)) (i : Fin 3) :
    pderiv i p ∈ harmonicPolynomials n := by
  refine ⟨by simpa using hp.1.pderiv (i := i), ?_⟩
  change KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian (pderiv i p) = 0
  have hc : KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian (pderiv i p) = pderiv i (KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian p) := by
    change (∑ j : Fin 3, pderiv j (pderiv j (pderiv i p))) =
      pderiv i (∑ j : Fin 3, pderiv j (pderiv j p))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [partials_commute j i, partials_commute j i]
  rw [hc, show KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian p = 0 from hp.2, map_zero]

private theorem laplacian_coordinate_mul (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian (X i * p) = X i * KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian p + 2 * pderiv i p := by
  classical
  change (∑ j : Fin 3, pderiv j (pderiv j (X i * p))) = _
  have hc (j : Fin 3) : pderiv j (pderiv j (X i)) = (0 : MvPolynomial (Fin 3) ℂ) := by
    by_cases h : i = j <;> simp [pderiv_X, Pi.single_apply, h]
  simp only [pderiv_mul, map_add, hc, zero_mul, zero_add]
  change _ = X i * (∑ j : Fin 3, pderiv j (pderiv j p)) + _
  simp only [Finset.mul_sum]
  have he (j : Fin 3) :
      pderiv j (X i) * pderiv j p +
        (pderiv j (X i) * pderiv j p + X i * pderiv j (pderiv j p)) =
      X i * pderiv j (pderiv j p) + if j = i then 2 * pderiv i p else 0 := by
    by_cases h : j = i
    · subst j; simp; ring
    · simp [pderiv_X, Pi.single_apply, h, Ne.symm h]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

noncomputable def harmonicRaise (n : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  X i * p - (2 * (n : ℂ) + 1)⁻¹ •
    (ComplexFractionalInverse.FiniteFischerRaw.radiusQuadratic * pderiv i p)

private theorem harmonicRaise_succ_mem (n : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials (n + 1)) (i : Fin 3) :
    harmonicRaise (n + 1) i p ∈ harmonicPolynomials (n + 2) := by
  open ComplexFractionalInverse.FiniteFischerRaw in
  have hpartial := harmonic_partial_mem n p hp i
  refine ⟨?_, ?_⟩
  · change (X i * p - (2 * ((n + 1 : ℕ) : ℂ) + 1)⁻¹ •
        (radiusQuadratic * pderiv i p)).IsHomogeneous (n + 2)
    apply IsHomogeneous.sub
    · convert (isHomogeneous_X ℂ i).mul hp.1 using 1 <;> omega
    · apply (homogeneousSubmodule (Fin 3) ℂ (n + 2)).smul_mem
      simpa [add_comm] using radius_homogeneous.mul hpartial.1
  · change KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian (harmonicRaise (n + 1) i p) = 0
    have hrad := laplacian_radius_pow hpartial.1 1
    simp only [pow_one, Nat.cast_one, one_mul, Nat.sub_self, pow_zero] at hrad
    have hzero : KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian (pderiv i p) = 0 := hpartial.2
    rw [hzero, mul_zero, zero_add] at hrad
    have hc : (2 * ((n + 1 : ℕ) : ℂ) + 1) ≠ 0 := by
      norm_cast
    dsimp only [harmonicRaise]
    rw [map_sub, map_smul, laplacian_coordinate_mul, show KPCplxHarmonicIntertwinerSpectrum.polynomialLaplacian p = 0 from hp.2,
      mul_zero, zero_add, hrad]
    simp only [Nat.cast_add, Nat.cast_one, smul_smul, one_mul, mul_one]
    have he : (2 * ((n : ℂ) + 1) + 1)⁻¹ * (2 * (2 * (n : ℂ) + 2 + 1)) = 2 := by
      have hc' : 2 * ((n : ℂ) + 1) + 1 ≠ 0 := by simpa using hc
      field_simp
    rw [he]
    simp [smul_eq_C_mul, map_ofNat]

private theorem compact_radius (k : KPCplxCharacterHaar.ComplexSU2) :
    MvPolynomial.eval (compactSphereCoordinate k) radiusQuadratic = 1 := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hu : m * star m = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hr := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hr
  simp only [Complex.star_def, Complex.mul_conj', Complex.add_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at hr
  have hprod : (m 1 0 * star (m 1 1)).re ^ 2 +
      (m 1 0 * star (m 1 1)).im ^ 2 = ‖m 1 0‖ ^ 2 * ‖m 1 1‖ ^ 2 := by
    calc
      _ = Complex.normSq (m 1 0 * star (m 1 1)) := by
        simp only [Complex.normSq_apply, sq]
      _ = _ := by rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_star]
  simp only [radiusQuadratic, Fin.sum_univ_three, map_add, map_pow, MvPolynomial.eval_X,
    compactSphereCoordinate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change ((2 * (m 1 0 * star (m 1 1)).re : ℝ) : ℂ)^2 +
    ((2 * (m 1 0 * star (m 1 1)).im : ℝ) : ℂ)^2 +
    ((‖m 1 0‖^2 - ‖m 1 1‖^2 : ℝ) : ℂ)^2 = 1
  norm_cast
  nlinarith [hprod, sq_nonneg (‖m 1 0‖^2 + ‖m 1 1‖^2 - 1)]

theorem conformal_gradient_harmonic_decomposition (s : ℝ) (n : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials (n + 1))
    (i : Fin 3) (D : PrincipalSeries s)
    (hD : compactRestriction s D = polynomialCompactRestriction
      (pderiv i p - ((((n + 1 : ℕ) : ℂ)) + 1 + 2 * (s : ℂ)) • (X i * p))) :
    ∃ a b : PrincipalSeries s,
      a ∈ harmonicKType s (n + 2) ∧
      b ∈ harmonicKType s n ∧
      D = a + b ∧
      compactRestriction s b =
        (((((n + 1 : ℕ) : ℂ)) - 2 * (s : ℂ)) /
          (2 * (((n + 1 : ℕ) : ℂ)) + 1)) •
          polynomialCompactRestriction (pderiv i p) := by
  classical
  let c : ℂ := ((((n + 1 : ℕ) : ℂ)) - 2 * (s : ℂ)) /
    (2 * (((n + 1 : ℕ) : ℂ)) + 1)
  let α : ℂ := (((n + 1 : ℕ) : ℂ)) + 1 + 2 * (s : ℂ)
  have hpartial := harmonic_partial_mem n p hp i
  have hrange : polynomialCompactRestriction (pderiv i p) ∈
      (compactRestriction s).range := by
    apply (show (harmonicPolynomials n).map polynomialCompactRestriction ≤
      (compactRestriction s).range from
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactHarmonics_extend s n)
    exact Submodule.mem_map.mpr ⟨pderiv i p, hpartial, rfl⟩
  obtain ⟨q, hq⟩ := hrange
  have hc : (2 * ((n + 1 : ℕ) : ℂ) + 1) ≠ 0 := by norm_cast
  have hprofile : compactRestriction s (D - c • q) =
      polynomialCompactRestriction ((-α) • harmonicRaise (n + 1) i p) := by
    rw [map_sub, map_smul, hD, hq]
    ext k
    simp only [polynomialCompactRestriction, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, harmonicRaise, map_sub, map_smul,
      map_mul, eval_X, compact_radius, one_mul]
    dsimp only [c, α]
    have hc' : ((n + 1 : ℕ) : ℂ) * 2 + 1 ≠ 0 := by simpa [mul_comm] using hc
    field_simp [hc']
    <;> ring
  refine ⟨D - c • q, c • q, ?_, ?_, ?_, ?_⟩
  · change compactRestriction s (D - c • q) ∈
      (harmonicPolynomials (n + 2)).map polynomialCompactRestriction
    exact Submodule.mem_map.mpr ⟨(-α) • harmonicRaise (n + 1) i p,
      (harmonicPolynomials (n + 2)).smul_mem (-α) (harmonicRaise_succ_mem n p hp i),
      hprofile.symm⟩
  · change compactRestriction s (c • q) ∈
      (harmonicPolynomials n).map polynomialCompactRestriction
    rw [map_smul, hq]
    exact (Submodule.map polynomialCompactRestriction (harmonicPolynomials n)).smul_mem c
      (Submodule.mem_map.mpr ⟨pderiv i p, hpartial, rfl⟩)
  · exact (sub_add_cancel D (c • q)).symm
  · rw [map_smul, hq]

end DedekindZetaZeroFree.KPCplxLoweringHarmonicDecomposition

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicPropagation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Topology

theorem lowering_harmonic_disjoint (s : ℝ) (m n : ℕ) (hmn : m ≠ n) :
    Disjoint (harmonicKType s m) (harmonicKType s n) := by
  have hm := harmonicKType_multiplicity_one s m
  have hn := harmonicKType_multiplicity_one s n
  have hi : IsKInvariant s (harmonicKType s m ⊓ harmonicKType s n) :=
    fun k f hf => ⟨hm.1 k f hf.1, hn.1 k f hf.2⟩
  apply disjoint_iff.mpr
  rcases hm.2.2.1 _ inf_le_left hi with hbot | heq
  · exact hbot
  · have hle : harmonicKType s m ≤ harmonicKType s n := by
      rw [← heq]
      exact inf_le_right
    rcases hn.2.2.1 _ hle hm.1 with hbot | heq'
    · have hd : Module.finrank ℂ (harmonicKType s m) = 0 := by rw [hbot]; simp
      rw [hm.2.1] at hd
      omega
    · have hd : 2 * m + 1 = 2 * n + 1 := by
        rw [← hm.2.1, heq', hn.2.1]
      omega

private theorem lowering_pi_sub (s : ℝ) (g : ComplexPGL2)
    (f h : PrincipalSeries s) : pi s g (f - h) = pi s g f - pi s g h := by
  induction g using Quotient.inductionOn with
  | h g =>
    change rightTranslate s g (f - h) = rightTranslate s g f - rightTranslate s g h
    rfl

private theorem lowering_sum_projection (s : ℝ) (A B W : Submodule ℂ (PrincipalSeries s))
    (hd : Disjoint A B) (hW : W ≤ A ⊔ B) :
    ∃ P : W →ₗ[ℂ] B, ∀ w : W, (w : PrincipalSeries s) - P w ∈ A := by
  classical
  have hex (w : W) : ∃ b : B, (w : PrincipalSeries s) - b ∈ A := by
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp (hW w.property)
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [← he]
    simpa using ha
  let p (w : W) : B := (hex w).choose
  have hp (w : W) : (w : PrincipalSeries s) - p w ∈ A := (hex w).choose_spec
  have huniq (w : W) (b : B) (hb : (w : PrincipalSeries s) - b ∈ A) : p w = b := by
    apply Subtype.ext
    have hA : (p w : PrincipalSeries s) - b ∈ A := by
      simpa only [sub_sub_sub_cancel_left] using A.sub_mem hb (hp w)
    have hB := B.sub_mem (p w).property b.property
    have hm : (p w : PrincipalSeries s) - b ∈ A ⊓ B := ⟨hA, hB⟩
    rw [disjoint_iff.mp hd] at hm
    have hz : (p w : PrincipalSeries s) - b = 0 := by simpa using hm
    exact sub_eq_zero.mp hz
  refine ⟨{ toFun := p, map_add' := ?_, map_smul' := ?_ }, hp⟩
  · intro x y
    apply huniq
    change (x : PrincipalSeries s) + y - ((p x : PrincipalSeries s) + p y) ∈ A
    simpa only [add_sub_add_comm] using A.add_mem (hp x) (hp y)
  · intro c x
    apply huniq
    change c • (x : PrincipalSeries s) - c • (p x : PrincipalSeries s) ∈ A
    simpa only [smul_sub] using A.smul_mem c (hp x)

set_option backward.isDefEq.respectTransparency false in

theorem lowering_two_harmonic_components_mem (s : ℝ) (m n : ℕ) (hmn : m ≠ n)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (a b : PrincipalSeries s) (ha : a ∈ harmonicKType s m)
    (hb : b ∈ harmonicKType s n) (hab : a + b ∈ U) : b ∈ U := by
  classical
  let A := harmonicKType s m
  let B := harmonicKType s n
  have hA := harmonicKType_multiplicity_one s m
  have hB := harmonicKType_multiplicity_one s n
  have hd : Disjoint A B := lowering_harmonic_disjoint s m n hmn
  have hUA : IsKInvariant s (U ⊓ A) := fun k f hf => ⟨hU k f hf.1, hA.1 k f hf.2⟩
  rcases hA.2.2.1 (U ⊓ A) inf_le_right hUA with hzero | hfull
  · by_cases hbzero : b = 0
    · simpa [hbzero] using U.zero_mem
    let W := U ⊓ (A ⊔ B)
    obtain ⟨P, hP⟩ := lowering_sum_projection s A B W hd inf_le_right
    have huniq (w : W) (v : B) (hv : (w : PrincipalSeries s) - v ∈ A) : P w = v := by
      apply Subtype.ext
      have hhA : (P w : PrincipalSeries s) - v ∈ A := by
        simpa only [sub_sub_sub_cancel_left] using A.sub_mem hv (hP w)
      have hm : (P w : PrincipalSeries s) - v ∈ A ⊓ B :=
        ⟨hhA, B.sub_mem (P w).property v.property⟩
      rw [disjoint_iff.mp hd] at hm
      have he : (P w : PrincipalSeries s) - v = 0 := by simpa using hm
      exact sub_eq_zero.mp he
    have hWinv : IsKInvariant s W := by
      intro k f hf
      refine ⟨hU k f hf.1, ?_⟩
      obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hf.2
      rw [← he]
      have hepi : pi s k (a + b) = pi s k a + pi s k b := by
        induction (k : ComplexPGL2) using Quotient.inductionOn with
        | h g =>
          change rightTranslate s g (a + b) = rightTranslate s g a + rightTranslate s g b
          rfl
      rw [hepi]
      exact (A ⊔ B).add_mem (Submodule.mem_sup_left (hA.1 k a ha))
        (Submodule.mem_sup_right (hB.1 k b hb))
    have hequiv (k : compactSubgroup) (w : W) :
        P ⟨pi s k w, hWinv k w w.property⟩ =
          ⟨pi s k (P w), hB.1 k (P w) (P w).property⟩ := by
      apply huniq
      change pi s k w - pi s k (P w) ∈ A
      rw [← lowering_pi_sub]
      exact hA.1 k _ (hP w)
    let L : W →ₗ[ℂ] PrincipalSeries s := B.subtype.comp P
    have hLin : Function.Injective L := by
      intro x y hxy
      have hpEq : P x = P y := Subtype.ext hxy
      have hhA : (x : PrincipalSeries s) - y ∈ A := by
        have hh := A.sub_mem (hP x) (hP y)
        rw [hpEq] at hh
        simpa only [sub_sub_sub_cancel_right] using hh
      have hhUA : (x : PrincipalSeries s) - y ∈ U ⊓ A :=
        ⟨U.sub_mem x.property.1 y.property.1, hhA⟩
      rw [hzero] at hhUA
      have he : (x : PrincipalSeries s) - y = 0 := by simpa using hhUA
      exact Subtype.ext (sub_eq_zero.mp he)
    have hRinv : IsKInvariant s L.range := by
      intro k f hf
      obtain ⟨w, rfl⟩ := hf
      refine ⟨⟨pi s k w, hWinv k w w.property⟩, ?_⟩
      exact congrArg (fun v : B => (v : PrincipalSeries s)) (hequiv k w)
    have hRle : L.range ≤ B := by
      rintro f ⟨w, rfl⟩
      exact (P w).property
    have hw : a + b ∈ W := ⟨hab, Submodule.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩⟩
    have hPb : P ⟨a + b, hw⟩ = ⟨b, hb⟩ := by
      apply huniq
      simpa using ha
    have hRne : L.range ≠ ⊥ := by
      intro hbot
      have hbR : b ∈ L.range := ⟨⟨a + b, hw⟩,
        congrArg (fun v : B => (v : PrincipalSeries s)) hPb⟩
      rw [hbot] at hbR
      exact hbzero (by simpa using hbR)
    have hReq : L.range = B := (hB.2.2.1 L.range hRle hRinv).resolve_left hRne
    have hWE : KEquivalent s W B := by
      let e : W ≃ₗ[ℂ] B := (LinearEquiv.ofInjective L hLin).trans
        (LinearEquiv.ofEq _ _ hReq)
      refine ⟨e, ?_⟩
      intro k u v huv
      have hv : v = ⟨pi s k u, hWinv k u u.property⟩ := Subtype.ext huv
      subst v
      exact congrArg (fun v : B => (v : PrincipalSeries s)) (hequiv k u)
    have hWeq : W = B := hB.2.2.2 W hWinv hWE
    have hbW : b ∈ W := by rw [hWeq]; exact hb
    exact hbW.1
  · have haU : a ∈ U := by
      have : a ∈ U ⊓ A := by rw [hfull]; exact ha
      exact this.1
    simpa only [add_sub_cancel_left] using U.sub_mem hab haU

open MvPolynomial
open scoped BigOperators

private theorem partials_commute_lowering (i j : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  ext d
  simp only [coeff_pderiv]
  by_cases hij : i = j
  · subst j; rfl
  · simp [Finsupp.single_apply, hij, Ne.symm hij, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm]

private theorem partial_mem_lowering (n : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials (n + 1)) (i : Fin 3) :
    pderiv i p ∈ harmonicPolynomials n := by
  refine ⟨by simpa using hp.1.pderiv (i := i), ?_⟩
  change polynomialLaplacian (pderiv i p) = 0
  have hc : polynomialLaplacian (pderiv i p) = pderiv i (polynomialLaplacian p) := by
    change (∑ j : Fin 3, pderiv j (pderiv j (pderiv i p))) =
      pderiv i (∑ j : Fin 3, pderiv j (pderiv j p))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [partials_commute_lowering j i, partials_commute_lowering j i]
  rw [hc, show polynomialLaplacian p = 0 from hp.2, map_zero]

 theorem compact_polynomial_ne_zero_lowering (n : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous n) (hne : p ≠ 0) :
    polynomialCompactRestriction p ≠ 0 := by
  intro h
  apply hne
  apply ComplexFractionalInverse.homogeneous_sphere_eq_zero hp
  intro x
  obtain ⟨k, rfl⟩ := ComplexFractionalInverse.hopf_surjective x
  have hk := congrFun h k
  change MvPolynomial.eval (compactSphereCoordinate k) p = 0 at hk
  convert hk using 1
  unfold ComplexFractionalInverse.polynomialSphere ComplexFractionalInverse.hopf
    ComplexFractionalInverse.hopfVector
  congr 2
  funext i
  fin_cases i <;> simp [compactSphereCoordinate, ← Complex.ofReal_pow]

theorem nonzero_adjacent_lowering_of_component (s : ℝ) (n : ℕ)
    (hcoeff : ((((n + 1 : ℕ) : ℂ) - 2 * (s : ℂ)) /
      (2 * ((n + 1 : ℕ) : ℂ) + 1)) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s))
    (hn : harmonicKType s (n + 1) ≤ U)
    (hcomponent : ∀ (f : PrincipalSeries s) (p : MvPolynomial (Fin 3) ℂ),
      f ∈ U → p ∈ harmonicPolynomials (n + 1) →
      compactRestriction s f = polynomialCompactRestriction p → ∀ i : Fin 3,
      ∃ v : PrincipalSeries s, v ∈ U ∧ compactRestriction s v =
        ((((n + 1 : ℕ) : ℂ) - 2 * (s : ℂ)) /
          (2 * ((n + 1 : ℕ) : ℂ) + 1)) • polynomialCompactRestriction (pderiv i p)) :
    ∃ v : PrincipalSeries s, v ∈ U ∧ v ∈ harmonicKType s n ∧ v ≠ 0 := by
  have hdim : 0 < Module.finrank ℂ (harmonicKType s (n + 1)) := by
    rw [(harmonicKType_multiplicity_one s (n + 1)).2.1]
    omega
  haveI : Nontrivial (harmonicKType s (n + 1)) :=
    Module.nontrivial_of_finrank_pos hdim
  obtain ⟨f, hf⟩ := exists_ne (0 : harmonicKType s (n + 1))
  have hfne : (f : PrincipalSeries s) ≠ 0 := by
    intro h
    apply hf
    exact Subtype.ext h
  obtain ⟨p, hp, he⟩ := f.property
  have hpne : p ≠ 0 := by
    intro h
    subst p
    rw [map_zero] at he
    apply hfne
    apply compactRestriction_injective s
    simpa using he.symm
  have hpartial : ∃ i : Fin 3, pderiv i p ≠ 0 := by
    by_contra h
    push Not at h
    have he := hp.1.sum_X_mul_pderiv
    simp only [h, mul_zero, Finset.sum_const_zero] at he
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have he' : (n + 1 : ℂ) • p = 0 := by
      simpa only [← Nat.cast_add_one (R := ℂ), Nat.cast_smul_eq_nsmul] using he.symm
    exact hpne ((smul_eq_zero.mp he').resolve_left hn)
  obtain ⟨i, hi⟩ := hpartial
  obtain ⟨v, hvU, hv⟩ := hcomponent f p (hn f.property) hp he.symm i
  have hpi := partial_mem_lowering n p hp i
  refine ⟨v, hvU, ?_, ?_⟩
  · change compactRestriction s v ∈ (harmonicPolynomials n).map polynomialCompactRestriction
    rw [hv]
    exact Submodule.smul_mem _ _ ⟨pderiv i p, hpi, rfl⟩
  · intro hzero
    rw [hzero, map_zero] at hv
    have hcompact : polynomialCompactRestriction (pderiv i p) ≠ 0 :=
      compact_polynomial_ne_zero_lowering n _ hpi.1 hi
    exact hcompact ((smul_eq_zero.mp hv.symm).resolve_left hcoeff)

theorem nonzero_adjacent_lowering (s : ℝ) (n : ℕ)
    (hcoeff : ((((n + 1 : ℕ) : ℂ) - 2 * (s : ℂ)) /
      (2 * ((n + 1 : ℕ) : ℂ) + 1)) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s))
    (hclosed : IsClosed (U : Set (PrincipalSeries s)))
    (hinv : ∀ (g : ComplexPGL2) (f : PrincipalSeries s), f ∈ U → pi s g f ∈ U)
    (hn : harmonicKType s (n + 1) ≤ U) :
    ∃ v : PrincipalSeries s, v ∈ U ∧ v ∈ harmonicKType s n ∧ v ≠ 0 := by
  apply nonzero_adjacent_lowering_of_component s n hcoeff U hn
  intro f p hf hp he i
  obtain ⟨γ, hγ, hzero, hboost⟩ :=
    KPCplxLoweringCoordinateBoost.exists_coordinate_boost i
  obtain ⟨D, hlimit, hderiv⟩ :=
    KPCplxLoweringOrbitDifferentiation.smooth_matrix_orbit_derivative s γ hγ hzero f
  have hDU : D ∈ U := hclosed.mem_of_tendsto hlimit
    (Filter.Eventually.of_forall (fun t => U.smul_mem _
      (U.sub_mem (by
        simpa only [pi_mk] using hinv (Matrix.ProjGenLinGroup.mk (γ t)) f hf) hf)))
  have hprofile : compactRestriction s D = polynomialCompactRestriction
      (pderiv i p - ((((n + 1 : ℕ) : ℂ)) + 1 + 2 * (s : ℂ)) • (X i * p)) := by
    ext k
    exact (hderiv (complexSU2Embedding k)).unique (hboost s (n + 1) p f hp.1 he k)
  obtain ⟨a, b, ha, hb, hD, hbprofile⟩ :=
    KPCplxLoweringHarmonicDecomposition.conformal_gradient_harmonic_decomposition
      s n p hp i D hprofile
  have hbU : b ∈ U := lowering_two_harmonic_components_mem s (n + 2) n
    (by omega) U (fun k v hv => hinv k v hv) a b ha hb (by rwa [← hD])
  exact ⟨b, hbU, hbprofile⟩

end DedekindZetaZeroFree.KPCplxHarmonicPropagation

end

section

namespace DedekindZetaZeroFree.KPCplxActualImageProof

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Topology

open KPCplxIntertwinerEigenvalues MvPolynomial
open scoped BigOperators

theorem exceptional_boost_coefficients_ne_zero (s : ℝ)
    (hs : s = KPCplxPrincipalSeriesCharts.positiveParameter ∨
      s = KPCplxPrincipalSeriesCharts.negativeParameter) (n : ℕ) :
    ((n : ℂ) + 1 + 2 * (s : ℂ)) ≠ 0 ∧
      (((n + 1 : ℕ) : ℂ) - 2 * (s : ℂ)) / (2 * ((n + 1 : ℕ) : ℂ) + 1) ≠ 0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : (n : ℝ) + 1 + 2 * s ≠ 0 ∧ (n : ℝ) + 1 - 2 * s ≠ 0 := by
    rcases hs with rfl | rfl <;>
      dsimp only [KPCplxPrincipalSeriesCharts.positiveParameter,
        KPCplxPrincipalSeriesCharts.negativeParameter] <;>
      constructor <;> linarith
  constructor
  · exact_mod_cast hr.1
  · apply div_ne_zero
    · exact_mod_cast hr.2
    · norm_cast

theorem harmonic_propagation_of_adjacent (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s))
    (hraise : ∀ n : ℕ, harmonicKType s n ≤ U → harmonicKType s (n + 1) ≤ U)
    (hlower : ∀ n : ℕ, harmonicKType s (n + 1) ≤ U → harmonicKType s n ≤ U)
    (ℓ : ℕ) (hℓ : harmonicKType s ℓ ≤ U) :
    ∀ m : ℕ, harmonicKType s m ≤ U := by
  have hdown : ∀ n : ℕ, harmonicKType s n ≤ U → harmonicKType s 0 ≤ U := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih => exact fun hn => ih (hlower n hn)
  have hzero := hdown ℓ hℓ
  intro m
  induction m with
  | zero => exact hzero
  | succ n ih => exact hraise n ih

theorem exceptional_harmonic_propagation (s : ℝ)
    (hs : s = positiveParameter ∨ s = negativeParameter)
    (U : Submodule ℂ (PrincipalSeries s))
    (hclosed : IsClosed (U : Set (PrincipalSeries s)))
    (hinv : ∀ (g : ComplexPGL2) (f : PrincipalSeries s), f ∈ U → pi s g f ∈ U)
    (ℓ : ℕ) (hℓ : harmonicKType s ℓ ≤ U) :
    ∀ m : ℕ, harmonicKType s m ≤ U := by
  have hK : IsKInvariant s U := fun k f hf => hinv k f hf
  have hraise : ∀ n : ℕ, harmonicKType s n ≤ U → harmonicKType s (n + 1) ≤ U := by
    intro n hn
    obtain ⟨v, hvU, hvtype, hv⟩ :=
      KPCplxHarmonicPropagation.nonzero_adjacent_raising s n
        (exceptional_boost_coefficients_ne_zero s hs n).1 U hclosed hinv hn
    exact KPCplxHarmonicPropagation.harmonic_le_of_nonzero_vector
      s U hK (n + 1) v hvU hvtype hv
  have hlower : ∀ n : ℕ, harmonicKType s (n + 1) ≤ U → harmonicKType s n ≤ U := by
    intro n hn
    obtain ⟨v, hvU, hvtype, hv⟩ :=
      KPCplxHarmonicPropagation.nonzero_adjacent_lowering s n
        (exceptional_boost_coefficients_ne_zero s hs n).2 U hclosed hinv hn
    exact KPCplxHarmonicPropagation.harmonic_le_of_nonzero_vector
      s U hK n v hvU hvtype hv
  exact harmonic_propagation_of_adjacent s U hraise hlower ℓ hℓ

end DedekindZetaZeroFree.KPCplxActualImageProof

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicPropagation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Topology

theorem orbit_limit_eq_of_pointwise_derivative (s : ℝ)
    (γ : ℝ → ComplexPGL2) (hγ : γ 0 = 1) (f D v : PrincipalSeries s)
    (hlimit : Filter.Tendsto
      (fun t : ℝ => (t : ℂ)⁻¹ • (pi s (γ t) f - f))
      (𝓝[≠] (0 : ℝ)) (𝓝 D))
    (hv : ∀ g : ComplexGL2,
      HasDerivAt (fun t : ℝ => pi s (γ t) f g) (v g) 0) : D = v := by
  apply Subtype.ext
  funext g
  have hD := (KPCplxHarmonicExtraction.principalSeries_evaluation_continuous s g
    |>.tendsto D).comp hlimit
  have hscalar := (hv g).tendsto_slope_zero
  simp only [zero_add] at hscalar
  have heq : (fun t : ℝ => (t : ℂ)⁻¹ * (pi s (γ t) f g - f g)) =
      (fun t : ℝ => t⁻¹ • (pi s (γ t) f g - pi s (γ 0) f g)) := by
    funext t
    rw [hγ, pi_one]
    simp only [Complex.real_smul, Complex.ofReal_inv]
  change Filter.Tendsto
    (fun t : ℝ => (t : ℂ)⁻¹ * (pi s (γ t) f g - f g))
    (𝓝[≠] (0 : ℝ)) (𝓝 (D g)) at hD
  rw [heq] at hD
  exact tendsto_nhds_unique hD hscalar

open MvPolynomial
open scoped BigOperators

end DedekindZetaZeroFree.KPCplxHarmonicPropagation

end
