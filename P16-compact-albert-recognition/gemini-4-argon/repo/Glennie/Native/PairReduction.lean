/- Actual compact diagonal/complex pair reduction.
Every reduction map is a constructed native product- and trace-preserving equivalence.
No spectral, triality-transitivity, or pair-reduction conclusion is a hypothesis.
-/
module

public import Glennie.ComplexLine
public import Glennie.Diagonalization
public import Glennie.Theorems.OctonionAutomorphisms

@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

/-- Two arbitrary unit octonions can be sent to the unit by an actual related triple. -/
theorem octTwoUnitSlots (p q : Octonion) (hp : octNormSq p = 1)
    (hq : octNormSq q = 1) :
    ∃ g : OctRelatedTriple, g.A p = octScalar 1 ∧ g.B q = octScalar 1 := by
  let r := octMul q (octConj p)
  have hr : octNormSq r = 1 := by simp [r, octNormSq_mul, hp, hq]
  obtain ⟨a, ha, _, hcancel⟩ := octUnit_normalizing_cube r hr
  let m := octMiddleTriple (octConj p) (by simpa using hp)
  let t := OctRelatedTriple.unitStabilizerTriple a ha
  refine ⟨t.comp m, ?_, ?_⟩
  · change t.A (octMul (octConj p) p) = octScalar 1
    rw [octMul_conj_self, hp]
    exact OctRelatedTriple.unitStabilizer_fix_unit a ha
  · change t.B r = octScalar 1
    rw [OctRelatedTriple.unitStabilizer_B, octMul_right_alternative]
    exact hcancel

/-- Positive scaling also includes zero, using the literal unit for that case. -/
theorem octUnit_scaling (x : Octonion) :
    ∃ a : Octonion, ∃ r : ℝ, octNormSq a = 1 ∧ 0 ≤ r ∧ x = r • a := by
  by_cases hx : x = 0
  · exact ⟨octScalar 1, 0, by norm_num [octNormSq, octScalar, Quaternion.normSq_def'], le_rfl, by simpa using hx⟩
  · obtain ⟨a, r, hr, ha, hx⟩ := octUnit_decomposition x hx
    exact ⟨a, r, ha, hr.le, hx⟩

/-- Arbitrary 01 and 12 slots, including zeros, become nonnegative real slots. -/
theorem octTwoSlotsReal (u w : Octonion) :
    ∃ g : OctRelatedTriple, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      g.A u = octScalar a ∧ g.B w = octScalar b := by
  obtain ⟨p, a, hp, ha, hu⟩ := octUnit_scaling u
  obtain ⟨q, b, hq, hb, hw⟩ := octUnit_scaling w
  obtain ⟨g, hgu, hgw⟩ := octTwoUnitSlots p q hp hq
  exact ⟨g, a, b, ha, hb,
    by rw [hu, map_smul, hgu, octScalar_smul, mul_one],
    by rw [hw, map_smul, hgw, octScalar_smul, mul_one]⟩

@[simp] theorem octInComplex_scalar (r : ℝ) : OctInComplex (octScalar r) := by
  simp [OctInComplex, octScalar]

theorem octInComplex_standardLine (z : ℂ) : OctInComplex (octComplexLine octI z) := by
  simp [OctInComplex, octComplexLine, octI, quatI, octScalar, smul_eq_mul]

/-- A genuine diagonal related triple fixes every real scalar. -/
theorem diagonalOctTriple_scalar (g : OctRelatedTriple) (hg : DiagonalOctTriple g)
    (r : ℝ) : g.A (octScalar r) = octScalar r := by
  have hs : r • octScalar 1 = octScalar r := by simpa using octScalar_smul r 1
  rw [← hs, map_smul, hg.2.2]

/-- Every octonion, including real elements and zero, is transported into the
standard complex line by a genuine scalar-fixing octonion automorphism. -/
theorem exists_octAutomorphism_to_complex (v : Octonion) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ OctInComplex (g.C v) := by
  obtain ⟨I, hi, hn, z, hz⟩ := exists_octComplexLine v
  obtain ⟨g, hg, hI⟩ := exists_octAutomorphism_to_i I hi hn
  have hv : g.A v = octComplexLine octI z := by
    simp only [← hz, octComplexLine, map_add, map_smul, hg.2.2, hI]
  exact ⟨g, hg, by rw [hg.2.1, hv]; exact octInComplex_standardLine z⟩

/-- Any actual related-triple Albert map preserves the entire diagonal subspace. -/
theorem relatedTriple_isDiagonal (g : OctRelatedTriple) (x : Albert)
    (hx : IsDiagonal x) : IsDiagonal (g.compactAutomorphism.equiv x) := by
  change g.A x.o01 = 0 ∧ g.C x.o02 = 0 ∧ g.B x.o12 = 0
  simp only [hx.1, hx.2.1, hx.2.2, map_zero, and_self]

/-- Unrestricted native compact pair reduction, including zero slots and repeated spectra. -/
theorem universal_pair_reduction : UniversalPairReduction := by
  intro x y
  obtain ⟨d, hdx⟩ := native_diagonalization x
  let y' := d.equiv y
  obtain ⟨t, a, b, ha, hb, h01, h12⟩ := octTwoSlotsReal y'.o01 y'.o12
  obtain ⟨k, hk, h02⟩ := exists_octAutomorphism_to_complex (t.C y'.o02)
  refine ⟨k.compactAutomorphism.comp (t.compactAutomorphism.comp d),
    relatedTriple_isDiagonal k _ (relatedTriple_isDiagonal t _ hdx), ?_⟩
  change OctInComplex (k.A (t.A y'.o01)) ∧
    OctInComplex (k.C (t.C y'.o02)) ∧ OctInComplex (k.B (t.B y'.o12))
  rw [h01, h12, diagonalOctTriple_scalar k hk a, hk.1,
    diagonalOctTriple_scalar k hk b]
  exact ⟨octInComplex_scalar a, h02, octInComplex_scalar b⟩

end
end Glennie
