module
public import Glennie.Diagonalization
public import Glennie.Theorems.Frames
public import Glennie.Theorems.OctonionAutomorphisms
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

def octComplexLine (I : Octonion) (z : ℂ) : Octonion := z.re • octScalar 1 + z.im • I

@[simp] theorem octComplexLine_one (I : Octonion) : octComplexLine I 1 = octScalar 1 := by simp [octComplexLine]

theorem octComplexLine_mul (I : Octonion) (hi : octRe I = 0) (hn : octNormSq I = 1) (z w : ℂ) :
    octComplexLine I (z * w) = octMul (octComplexLine I z) (octComplexLine I w) := by
  have hi2 : octMul I I = (-1 : ℝ) • octScalar 1 := by
    simpa only [octScalar_smul, mul_one] using octMul_pure_unit_self I hi hn
  simp only [octComplexLine, Complex.mul_re, Complex.mul_im, octMul_add_left, octMul_add_right,
    octMul_smul_left, octMul_smul_right, octMul_scalar_left, octMul_scalar_right, hi2, one_smul]
  module

theorem octComplexLine_normSq (I : Octonion) (hi : octRe I = 0) (hn : octNormSq I = 1) (z : ℂ) :
    octNormSq (octComplexLine I z) = Complex.normSq z := by
  have h := congrArg (fun r : ℝ => z.im ^ 2 * r) hn
  simp only [octRe] at hi
  simp [octComplexLine, octNormSq, Quaternion.normSq_def', octScalar, Complex.normSq_apply, smul_eq_mul, hi] at h ⊢
  nlinarith [h]

theorem octComplexLine_conj (I : Octonion) (hi : octRe I = 0) (z : ℂ) :
    octConj (octComplexLine I z) = octComplexLine I (star z) := by
  have hI : octConj I = -I := by apply Prod.ext <;> apply Quaternion.ext <;> simp_all [octConj, octRe]
  simp [octComplexLine, octConj_add, octConj_smul, octConj_scalar, hI, smul_neg]

theorem exists_octComplexLine (x : Octonion) :
    ∃ I : Octonion, octRe I = 0 ∧ octNormSq I = 1 ∧ ∃ z : ℂ, octComplexLine I z = x := by
  let b := x - octScalar (octRe x)
  have hb : octRe b = 0 := by simp [b, octRe, octScalar]
  by_cases hz : b = 0
  · refine ⟨octI, rfl, by norm_num [octI, quatI, octNormSq, Quaternion.normSq_def'], ⟨octRe x, 0⟩, ?_⟩
    simpa [octComplexLine, octScalar_smul] using (sub_eq_zero.mp hz).symm
  · obtain ⟨I, r, hr, hn, hdecomp⟩ := octUnit_decomposition b hz
    have hi : octRe I = 0 := by
      have h : octRe b = r * octRe I := congrArg octRe hdecomp
      exact (mul_eq_zero.mp (hb ▸ h).symm).resolve_left hr.ne'
    refine ⟨I, hi, hn, ⟨octRe x, r⟩, ?_⟩
    change octRe x • octScalar 1 + r • I = x
    rw [octScalar_smul, mul_one, ← hdecomp]; exact add_sub_cancel _ _

theorem octUnit_normalizing_cube (r : Octonion) (hr : octNormSq r = 1) :
    ∃ a : Octonion, octNormSq a = 1 ∧ octMul a (octMul a a) = octConj r ∧
      octMul a (octMul r (octMul a a)) = octScalar 1 := by
  obtain ⟨I, hi, hn, z, hz⟩ := exists_octComplexLine r
  have hzn : Complex.normSq z = 1 := by rw [← octComplexLine_normSq I hi hn z, hz, hr]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (star z) (n := 3) (by decide)
  have hwn : Complex.normSq w = 1 := by
    have h : Complex.normSq (w ^ 3) = Complex.normSq ((starRingEnd ℂ) z) := congrArg Complex.normSq hw
    rw [map_pow, Complex.normSq_conj, hzn] at h
    exact (pow_left_inj₀ (Complex.normSq_nonneg w) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp (by simpa using h)
  have hc : w * (z * (w * w)) = 1 := by
    calc w * (z * (w * w)) = z * w ^ 3 := by ring
      _ = z * (starRingEnd ℂ) z := by rw [hw]; rfl
      _ = 1 := by rw [Complex.mul_conj, hzn, Complex.ofReal_one]
  refine ⟨octComplexLine I w, by rw [octComplexLine_normSq I hi hn, hwn], ?_, ?_⟩
  · rw [← octComplexLine_mul I hi hn, ← octComplexLine_mul I hi hn, show w * (w * w) = w ^ 3 by ring,
      hw, ← octComplexLine_conj I hi, hz]
  · rw [← hz, ← octComplexLine_mul I hi hn, ← octComplexLine_mul I hi hn, ← octComplexLine_mul I hi hn, hc, octComplexLine_one]

theorem octTwoUnitSlots (p q : Octonion) (hp : octNormSq p = 1) (hq : octNormSq q = 1) :
    ∃ g : OctRelatedTriple, g.A p = octScalar 1 ∧ g.B q = octScalar 1 := by
  let r := octMul q (octConj p)
  obtain ⟨a, ha, _, hcancel⟩ := octUnit_normalizing_cube r (by simp [r, octNormSq_mul, hp, hq])
  refine ⟨(OctRelatedTriple.unitStabilizerTriple a ha).comp (octMiddleTriple (octConj p) (by simpa using hp)), ?_, ?_⟩
  · change (OctRelatedTriple.unitStabilizerTriple a ha).A (octMul (octConj p) p) = octScalar 1
    rw [octMul_conj_self, hp]; exact OctRelatedTriple.unitStabilizer_fix_unit a ha
  · change (OctRelatedTriple.unitStabilizerTriple a ha).B r = octScalar 1
    rw [OctRelatedTriple.unitStabilizer_B, octMul_right_alternative]; exact hcancel

theorem octUnit_scaling (x : Octonion) :
    ∃ a : Octonion, ∃ r : ℝ, octNormSq a = 1 ∧ 0 ≤ r ∧ x = r • a := by
  by_cases hx : x = 0
  · exact ⟨octScalar 1, 0, by norm_num [octNormSq, octScalar, Quaternion.normSq_def'], le_rfl, by simpa using hx⟩
  · obtain ⟨a, r, hr, ha, hx⟩ := octUnit_decomposition x hx
    exact ⟨a, r, ha, hr.le, hx⟩

theorem octTwoSlotsReal (u w : Octonion) :
    ∃ g : OctRelatedTriple, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ g.A u = octScalar a ∧ g.B w = octScalar b := by
  obtain ⟨p, a, hp, ha, hu⟩ := octUnit_scaling u
  obtain ⟨q, b, hq, hb, hw⟩ := octUnit_scaling w
  obtain ⟨g, hgu, hgw⟩ := octTwoUnitSlots p q hp hq
  exact ⟨g, a, b, ha, hb, by rw [hu, map_smul, hgu, octScalar_smul, mul_one],
    by rw [hw, map_smul, hgw, octScalar_smul, mul_one]⟩

@[simp] theorem octInComplex_scalar (r : ℝ) : OctInComplex (octScalar r) := by simp [OctInComplex, octScalar]

theorem diagonalOctTriple_scalar (g : OctRelatedTriple) (hg : DiagonalOctTriple g) (r : ℝ) :
    g.A (octScalar r) = octScalar r := by
  rw [show octScalar r = r • octScalar 1 by simp [octScalar_smul], map_smul, hg.2.2]

theorem exists_octAutomorphism_to_complex (v : Octonion) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ OctInComplex (g.C v) := by
  obtain ⟨I, hi, hn, z, hz⟩ := exists_octComplexLine v
  obtain ⟨g, hg, hI⟩ := exists_octAutomorphism_to_i I hi hn
  refine ⟨g, hg, ?_⟩
  rw [hg.2.1, show g.A v = octComplexLine octI z by simp only [← hz, octComplexLine, map_add, map_smul, hg.2.2, hI]]
  simp [OctInComplex, octComplexLine, octI, quatI, octScalar, smul_eq_mul]

theorem relatedTriple_isDiagonal (g : OctRelatedTriple) (x : Albert) (hx : IsDiagonal x) :
    IsDiagonal (g.compactAutomorphism.equiv x) := by
  change g.A x.o01 = 0 ∧ g.C x.o02 = 0 ∧ g.B x.o12 = 0
  simp only [hx.1, hx.2.1, hx.2.2, map_zero, and_self]

theorem universal_pair_reduction : UniversalPairReduction := fun x y => by
  obtain ⟨d, hdx⟩ := native_diagonalization x
  obtain ⟨t, a, b, _, _, h01, h12⟩ := octTwoSlotsReal (d.equiv y).o01 (d.equiv y).o12
  obtain ⟨k, hk, h02⟩ := exists_octAutomorphism_to_complex (t.C (d.equiv y).o02)
  refine ⟨k.compactAutomorphism.comp (t.compactAutomorphism.comp d),
    relatedTriple_isDiagonal k _ (relatedTriple_isDiagonal t _ hdx), ?_⟩
  change OctInComplex (k.A (t.A (d.equiv y).o01)) ∧ OctInComplex (k.C (t.C (d.equiv y).o02)) ∧
    OctInComplex (k.B (t.B (d.equiv y).o12))
  rw [h01, h12, diagonalOctTriple_scalar k hk a, hk.1, diagonalOctTriple_scalar k hk b]
  exact ⟨octInComplex_scalar a, h02, octInComplex_scalar b⟩

end
end Glennie
