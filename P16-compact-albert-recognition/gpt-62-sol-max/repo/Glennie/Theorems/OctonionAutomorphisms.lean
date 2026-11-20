module

public import Glennie.Native.Triality
public import Glennie.Native.Statements
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
/- Genuine compact octonion automorphisms from order-three unit stabilizers.
All multiplication is the declared octMul; the alias's inherited product is unused.
The sixth-root conjugation principle is classical (Dixon, hep-th/9604116 Eq.8).
-/

public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

private theorem g2_conj_formula (x : Octonion) :
    octConj x = (2*octRe x) • octScalar 1-x := by
  rw [eq_sub_iff_add_eq, add_comm, octAdd_conj, octScalar_smul (2 * octRe x) 1, mul_one, octScalar_smul]
private theorem g2_conj_pure (x : Octonion) (hx : octRe x = 0) : octConj x = -x := by
  rw [g2_conj_formula, hx]
  simp
/-- These equalities make the actual related triple an octonion automorphism. -/
@[expose] def DiagonalOctTriple (g : OctRelatedTriple) : Prop :=
  (∀ x, g.B x = g.A x) ∧ (∀ x, g.C x = g.A x) ∧
    g.A (octScalar 1) = octScalar 1

theorem diagonalOctTriple_comp (g h : OctRelatedTriple)
    (hg : DiagonalOctTriple g) (hh : DiagonalOctTriple h) :
    DiagonalOctTriple (g.comp h) := by
  simp [DiagonalOctTriple, OctRelatedTriple.comp, hg.1, hh.1, hg.2.1, hh.2.1, hg.2.2, hh.2.2]

/-- The actual order-three unit produces one map in all three triality slots. -/
theorem orderThree_diagonalTriple (q : Octonion) (hn : octNormSq q = 1)
    (hr : octRe q = -1 / 2) :
    DiagonalOctTriple (OctRelatedTriple.unitStabilizerTriple q hn) := by
  have hs : octMul q q = octConj q := by
    rw [octMul_self_eq, g2_conj_formula, hn, hr]
    norm_num <;> module
  let g := OctRelatedTriple.unitStabilizerTriple q hn
  have hA : g.A (octScalar 1) = octScalar 1 := OctRelatedTriple.unitStabilizer_fix_unit q hn
  have hB (x : Octonion) : g.B x = g.A x := by
    simp only [g, OctRelatedTriple.unitStabilizer_B, OctRelatedTriple.unitStabilizer_A,
      octMul_right_alternative, hs]
  refine ⟨hB, fun x => ?_, hA⟩
  simpa [hA, hB] using (g.product (octScalar 1) x).symm

/-- Orthogonal unit imaginaries are intertwined by the unit
`-(1/2) • ((1-x)(1-y))`, whose real part is `-1/2`. -/
private theorem transport_orthogonal (x y : Octonion) (hx : octRe x = 0)
    (hy : octRe y = 0) (hxn : octNormSq x = 1) (hyn : octNormSq y = 1)
    (hxy : octDot x y = 0) : ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ g.A x = y := by
  let q := (-1/2 : ℝ) • (octScalar 1-x-y+octMul x y)
  have hr : octRe (octMul x y) = 0 := by
    simpa [octDot, g2_conj_pure y hy, octMul_neg_right, octRe] using hxy
  have hyx : octMul y x = -octMul x y := by
    simpa only [g2_conj_pure _ hr, g2_conj_pure x hx, g2_conj_pure y hy,
      octMul_neg_left, octMul_neg_right, neg_neg] using (octConj_mul x y).symm
  have hn (z : Octonion) (hz : octRe z = 0) : octNormSq (octScalar 1-z) = 1+octNormSq z := by
    simp [oct_coord] at hz ⊢
    rw [hz]
    ring
  have hq : octNormSq q = 1 := by
    have he : q = (-1/2:ℝ) • octMul (octScalar 1-x) (octScalar 1-y) := by
      simp only [q, octMul_sub_left, octMul_sub_right, octMul_scalar_left, octMul_scalar_right, one_smul]
      abel
    rw [he, octNormSq_smul, octNormSq_mul, hn x hx, hn y hy, hxn, hyn]
    norm_num
  have hqr : octRe q = -1/2 := by
    dsimp only [q]
    rw [octRe_smul, octRe_add, octRe_sub, octRe_sub, hx, hy, hr]
    norm_num [octRe, octScalar]
  have hX : octMul (octMul x y) x = y := by
    rw [octMul_flexible, hyx, ← octMul_neg_left x y, ← g2_conj_pure x hx,
      octMul_left_conj_cancel, hxn, one_smul]
  have hY : octMul y (octMul x y) = x := by
    rw [← octMul_flexible y x, hyx, ← octMul_neg_right x y, ← g2_conj_pure y hy,
      octMul_right_conj_cancel, hyn, one_smul]
  have heq : octMul q x = octMul y q := by
    simp only [q, octMul_smul_left, octMul_smul_right, octMul_add_left, octMul_add_right,
      octMul_sub_left, octMul_sub_right, hX, hY, octMul_pure_unit_self x hx hxn,
      octMul_pure_unit_self y hy hyn, octMul_scalar_left, octMul_scalar_right, one_smul]
    abel
  refine ⟨OctRelatedTriple.unitStabilizerTriple q hq, orderThree_diagonalTriple q hq hqr,
    (octRightUnitEquiv q hq).injective ?_⟩
  change octMul ((OctRelatedTriple.unitStabilizerTriple q hq).A x) q = octMul y q
  rw [OctRelatedTriple.unitStabilizer_A, octMul_flexible, octMul_right_conj_cancel, hq, one_smul, heq]

/-- Three homogeneous linear equations in eight real coordinates leave a
nonzero vector, which we normalize without changing orthogonality. -/
private theorem perpendicular_unit (x y : Octonion) :
    ∃ z : Octonion, octRe z = 0 ∧ octNormSq z = 1 ∧ octDot x z = 0 ∧ octDot y z = 0 := by
  let v : Fin 3 → Octonion := ![octScalar 1,x,y]
  let f : Octonion →ₗ[ℝ] (Fin 3 → ℝ) := LinearMap.pi fun i =>
    ⟨⟨octDot (v i), octDot_add_right (v i)⟩, fun c a => octDot_smul_right c (v i) a⟩
  have hk : f.ker ≠ ⊥ := by
    intro he
    have h := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    norm_num [Octonion, Module.finrank_prod, Quaternion.finrank_eq_four] at h
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  obtain ⟨z,r,hr,hn,he⟩ := octUnit_decomposition w hw0
  have h (i : Fin 3) : octDot (v i) z = 0 := by
    have hh : octDot (v i) w = 0 := congrFun (LinearMap.mem_ker.mp hw) i
    rw [he, octDot_smul_right, mul_eq_zero] at hh
    exact hh.resolve_left hr.ne'
  exact ⟨z, by simpa [v, octDot_unit_left] using h 0, hn, h 1, h 2⟩

/-- Use an intermediate unit imaginary orthogonal to both prescribed axes. -/
theorem exists_octAutomorphism_to_i (I : Octonion) (hi : octRe I = 0)
    (hn : octNormSq I = 1) : ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ g.A I = octI := by
  obtain ⟨z,hz,hnz,h1,h2⟩ := perpendicular_unit I octI
  have hni : octNormSq octI = 1 := by norm_num [octI, quatI, octNormSq, Quaternion.normSq_def']
  obtain ⟨g,hg,he⟩ := transport_orthogonal I z hi hz hn hnz h1
  obtain ⟨k,hk,he'⟩ := transport_orthogonal z octI hz rfl hnz hni
    (by rwa [octDot_comm])
  refine ⟨k.comp g, diagonalOctTriple_comp k g hk hg, ?_⟩
  change k.A (g.A I) = octI
  rw [he, he']

end
end Glennie
