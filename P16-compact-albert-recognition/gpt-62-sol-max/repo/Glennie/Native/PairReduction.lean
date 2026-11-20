/- Actual compact diagonal/complex pair reduction.
Every reduction map is a constructed native product- and trace-preserving equivalence.
No spectral, triality-transitivity, or pair-reduction conclusion is a hypothesis.
-/
module

public import Glennie.Diagonalization
public import Glennie.Native.PairNormalization
public import Glennie.Sector
public import Glennie.Theorems.OctonionAutomorphisms
@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

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
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ OctInComplex (g.C v) ∧ 0 ≤ (complexPart (g.C v)).im := by
  obtain ⟨I, hi, hn, z, hzi, hz⟩ := exists_octComplexLine v
  obtain ⟨g, hg, hI⟩ := exists_octAutomorphism_to_i I hi hn
  have hv : g.A v = octComplexLine octI z := by
    simp only [← hz, octComplexLine, map_add, map_smul, hg.2.2, hI]
  refine ⟨g, hg, ?_⟩
  rw [hg.2.1, hv]
  exact ⟨octInComplex_standardLine z, by simpa [octComplexLine, complexPart, octI, quatI, octScalar] using hzi⟩

/-- Related triples fix every diagonal element. -/
theorem relatedTriple_fixes_diagonal (g : OctRelatedTriple) (x : Albert)
    (hx : IsDiagonal x) : g.compactAutomorphism.equiv x = x := by
  apply Albert.ext <;> try rfl
  · change g.A x.o01 = x.o01
    rw [hx.1, map_zero]
  · change g.C x.o02 = x.o02
    rw [hx.2.1, map_zero]
  · change g.B x.o12 = x.o12
    rw [hx.2.2, map_zero]

/-- The gauge used to compare normalized pairs. -/
structure PositiveNormal (y : Albert) : Prop where
  complex : InComplexSector y
  slot01 : ∃ a ≥ 0, y.o01 = octScalar a
  slot12 : ∃ b ≥ 0, y.o12 = octScalar b
  imag_nonneg : 0 ≤ (complexPart y.o02).im

theorem positive_complex_reduction (y : Albert) :
    ∃ g : OctRelatedTriple, PositiveNormal (g.compactAutomorphism.equiv y) := by
  obtain ⟨t,a,b,ha,hb,hA,hB⟩ := octTwoSlotsReal y.o01 y.o12
  obtain ⟨k,hk,hC,hzi⟩ := exists_octAutomorphism_to_complex (t.C y.o02)
  have h01 : k.A (t.A y.o01) = octScalar a := by rw [hA, diagonalOctTriple_scalar _ hk]
  have h12 : k.B (t.B y.o12) = octScalar b := by rw [hB, hk.1, diagonalOctTriple_scalar _ hk]
  refine ⟨k.comp t, ?_, ⟨a, ha, h01⟩, ⟨b, hb, h12⟩, hzi⟩
  change OctInComplex (k.A (t.A y.o01)) ∧ OctInComplex (k.C (t.C y.o02)) ∧
    OctInComplex (k.B (t.B y.o12))
  rw [h01, h12]
  exact ⟨octInComplex_scalar a, hC, octInComplex_scalar b⟩

theorem universal_pair_reduction : UniversalPairReduction := by
  intro x y
  obtain ⟨d, hd⟩ := native_diagonalization x
  obtain ⟨g, hg⟩ := positive_complex_reduction (d.equiv y)
  exact ⟨g.compactAutomorphism.comp d, relatedTriple_fixes_diagonal g _ hd ▸ hd, hg.complex⟩

end
end Glennie
