module
public import Glennie.Native.Triality
public import Glennie.Theorems.Frames

public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

@[simp] private theorem octRe_add (x y : Octonion) : octRe (x + y) = octRe x + octRe y := rfl
@[simp] private theorem octRe_sub (x y : Octonion) : octRe (x - y) = octRe x - octRe y := rfl
@[simp] private theorem octRe_smul (r : ℝ) (x : Octonion) : octRe (r • x) = r * octRe x := by simp [octRe, smul_eq_mul]

private theorem g2_conj_formula (x : Octonion) : octConj x = (2 * octRe x) • octScalar 1 - x := by
  have h := octAdd_conj x; rw [octScalar_smul] at h
  simpa only [octScalar_smul, mul_one] using eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h : octConj x + x = _)

private theorem g2_mul_sub_left (x y z : Octonion) : octMul (x - y) z = octMul x z - octMul y z := by
  simp [sub_eq_add_neg, octMul_add_left, show octMul (-y) z = -octMul y z by simpa using octMul_smul_left (-1 : ℝ) y z]

private theorem g2_mul_sub_right (x y z : Octonion) : octMul x (y - z) = octMul x y - octMul x z := by
  simp [sub_eq_add_neg, octMul_add_right, show octMul x (-z) = -octMul x z by simpa using octMul_smul_right (-1 : ℝ) x z]

@[expose] def DiagonalOctTriple (g : OctRelatedTriple) : Prop :=
  (∀ x, g.B x = g.A x) ∧ (∀ x, g.C x = g.A x) ∧ g.A (octScalar 1) = octScalar 1

theorem diagonalOctTriple_comp (g h : OctRelatedTriple) (hg : DiagonalOctTriple g) (hh : DiagonalOctTriple h) :
    DiagonalOctTriple (g.comp h) :=
  ⟨fun x => by change g.B (h.B x) = g.A (h.A x); rw [hh.1, hg.1],
   fun x => by change g.C (h.C x) = g.A (h.A x); rw [hh.2.1, hg.2.1],
   by change g.A (h.A (octScalar 1)) = octScalar 1; rw [hh.2.2, hg.2.2]⟩

theorem orderThree_diagonalTriple (q : Octonion) (hn : octNormSq q = 1) (hr : octRe q = -1 / 2) :
    DiagonalOctTriple (OctRelatedTriple.unitStabilizerTriple q hn) := by
  have hs : octMul q q = octConj q := by rw [octMul_self_eq, g2_conj_formula, hn, hr]; norm_num; module
  exact ⟨OctRelatedTriple.unitStabilizer_B_eq_A q hn hs, OctRelatedTriple.unitStabilizer_C_eq_A q hn hs,
    OctRelatedTriple.unitStabilizer_fix_unit q hn⟩

theorem exists_orderThree_map (x y : Octonion) (hx : octRe x = 0) (hy : octRe y = 0)
    (hxn : octNormSq x = 1) (hyn : octNormSq y = 1) (ht : -(1 / 2 : ℝ) ≤ octDot x y) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ g.A x = y := by
  let t := octDot x y; let w := x + y; let z := octMul x y + t • octScalar 1
  let a := Real.sqrt (1 + 2 * t) / (2 * (1 + t)); let b := 1 / (2 * (1 + t))
  let q := (-1 / 2 : ℝ) • octScalar 1 + a • w - b • z
  have ht' : -(1 / 2 : ℝ) ≤ t := ht
  have ht0 : 1 + t ≠ 0 := by linarith
  have hb : b * (1 + t) = 1 / 2 := by dsimp [b]; field_simp [ht0]
  have hx2 : octMul x x = (-1 : ℝ) • octScalar 1 := by simpa only [octScalar_smul, mul_one] using octMul_pure_unit_self x hx hxn
  have hy2 : octMul y y = (-1 : ℝ) • octScalar 1 := by simpa only [octScalar_smul, mul_one] using octMul_pure_unit_self y hy hyn
  have hxyre : octRe (octMul x y) = -t := by
    have h : octRe (octMul x y) + octDot x y = 2 * octRe x * octRe y := by simp [octRe, octMul, octDot_coordinates]; ring
    rw [hx, hy] at h; linarith
  have hyx : octMul y x = (-2 * t) • octScalar 1 - octMul x y := by
    have hcp (u : Octonion) (hu : octRe u = 0) : octConj u = -u := by rw [g2_conj_formula, hu]; simp
    calc octMul y x = octConj (octMul x y) := by
          rw [octConj_mul, hcp x hx, hcp y hy, show octMul (-y) (-x) = octMul y x by
            rw [show -y = (-1 : ℝ) • y by simp, show -x = (-1 : ℝ) • x by simp, octMul_smul_left, octMul_smul_right, smul_smul]; norm_num]
      _ = (-2 * t) • octScalar 1 - octMul x y := by rw [g2_conj_formula, hxyre, show 2 * -t = -2 * t by ring]
  have hwre : octRe w = 0 := by simp [w, hx, hy]
  have hzre : octRe z = 0 := by simp [z, hxyre, show octRe (octScalar 1) = 1 from rfl]
  have hd_u (u : Octonion) : octDot u (octScalar 1) = octRe u := by simp [octDot_coordinates, octScalar, octRe]
  have hd_r (u v s : Octonion) : octDot u (v + s) = octDot u v + octDot u s := by rw [octDot_comm, octDot_add_left, octDot_comm v, octDot_comm s]
  have hd_s (r : ℝ) (u v : Octonion) : octDot u (r • v) = r * octDot u v := by rw [octDot_comm, octDot_smul_left, octDot_comm v]
  have hwz : octDot w z = 0 := by
    have hxxy : octDot x (octMul x y) = 0 := by rw [octDot_comm, octDot_mul_left, octMul_conj_self, hxn, hd_u, hy]
    have hyxy : octDot y (octMul x y) = 0 := by rw [octDot_comm, octDot_mul_right, octMul_self_conj, hyn, hd_u, hx]
    simp only [w, z, octDot_add_left, hd_r, hd_s, hxxy, hyxy, hd_u, octRe_add, hx, hy]; ring
  have hzx : octMul z x = y - t • x := by
    simp only [z, octMul_add_left, octMul_scalar_left, octMul_smul_left, octMul_flexible, hyx,
      g2_mul_sub_right, octMul_smul_right, octMul_scalar_right, octMul_left_alternative, hx2]; module
  have hyz : octMul y z = x - t • y := by
    dsimp only [z]
    rw [octMul_add_right, octMul_smul_right, octMul_scalar_right, ← octMul_flexible y x, hyx,
      g2_mul_sub_left, octMul_smul_left, octMul_scalar_left, octMul_right_alternative, hy2, octMul_smul_right, octMul_scalar_right]; module
  have hwx : octMul w x = octMul y w := by dsimp only [w]; rw [octMul_add_left, octMul_add_right, hx2, hy2]; module
  have hqre : octRe q = -1 / 2 := by simp [q, hwre, hzre, show octRe (octScalar 1) = 1 from rfl]
  have hqn : octNormSq q = 1 := by
    have hn_sub (u v : Octonion) : octNormSq (u - v) = octNormSq u + octNormSq v - 2 * octDot u v := by
      simp [octNormSq, Quaternion.normSq_def', octDot_coordinates]; ring
    have hn_u : octNormSq (octScalar 1) = 1 := by norm_num [octNormSq, octScalar, Quaternion.normSq_def']
    have hwn : octNormSq w = 2 + 2 * t := by dsimp only [w]; rw [octNormSq_add, hxn, hyn]; ring
    have hzn : octNormSq z = 1 - t ^ 2 := by dsimp only [z]; rw [octNormSq_add, octNormSq_mul, hxn, hyn, octNormSq_smul, hn_u, hd_s, hd_u, hxyre]; ring
    have hQ : octNormSq q = 1 / 4 + a ^ 2 * (2 + 2 * t) + b ^ 2 * (1 - t ^ 2) := by
      simp only [q, hn_sub, octNormSq_add, octNormSq_smul, hn_u, octDot_add_left, octDot_smul_left, hd_s,
        show ∀ u, octDot (octScalar 1) u = octRe u by intro u; rw [octDot_comm, hd_u], hwre, hzre, hwz, hwn, hzn]; ring
    rw [hQ]; simp only [a, b, div_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * t), one_pow]
    field_simp [ht0, (by linarith : 2 * (1 + t) ≠ 0)]; ring
  have hqx : octMul q x = octMul y q := sub_eq_zero.mp <| by
    rw [show octMul q x - octMul y q = ((-1 / 2 : ℝ) + b * t + b) • (x - y) by
      simp only [q, g2_mul_sub_left, g2_mul_sub_right, octMul_add_left, octMul_add_right,
        octMul_smul_left, octMul_smul_right, octMul_scalar_left, octMul_scalar_right, hwx, hzx, hyz]; module,
      show (-1 / 2 : ℝ) + b * t + b = 0 by linarith [hb], zero_smul]
  refine ⟨OctRelatedTriple.unitStabilizerTriple q hqn, orderThree_diagonalTriple q hqn hqre, ?_⟩
  rw [OctRelatedTriple.unitStabilizer_A,
    show octMul q (octMul x (octConj q)) = octMul (octMul q x) (octConj q) by
      simp only [g2_conj_formula, g2_mul_sub_right, octMul_smul_right, octMul_scalar_right, octMul_flexible],
    hqx, octMul_conj_right_cancel, hqn, one_smul]

theorem exists_octAutomorphism_to_i (I : Octonion) (hi : octRe I = 0) (hn : octNormSq I = 1) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ g.A I = octI := by
  have hin : octNormSq octI = 1 := by norm_num [octI, quatI, octNormSq, Quaternion.normSq_def']
  by_cases hz : I + octI = 0
  · have hI : I = -octI := eq_neg_iff_add_eq_zero.mpr hz
    have hjn : octNormSq octJ = 1 := by norm_num [octJ, quatJ, octNormSq, Quaternion.normSq_def']
    obtain ⟨g1, hg1, h1⟩ := exists_orderThree_map I octJ hi rfl hn hjn (by norm_num [hI, octDot_coordinates, octI, octJ, quatI, quatJ])
    obtain ⟨g2, hg2, h2⟩ := exists_orderThree_map octJ octI rfl rfl hjn hin (by norm_num [octDot_coordinates, octI, octJ, quatI, quatJ])
    exact ⟨g2.comp g1, diagonalOctTriple_comp g2 g1 hg2 hg1, by change g2.A (g1.A I) = octI; rw [h1, h2]⟩
  · obtain ⟨K, r, hr, hkn, hdecomp⟩ := octUnit_decomposition (I + octI) hz
    have hre : octRe K = 0 := by
      have h : octRe (I + octI) = octRe (r • K) := congrArg octRe hdecomp
      simp [hi, show octRe octI = 0 from rfl] at h
      exact h.resolve_left hr.ne'
    have ht : 0 < 1 + octDot I octI := by
      have hwpos : 0 < octNormSq (I + octI) := lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hz ((octNormSq_eq_zero _).mp h))
      rw [octNormSq_add, hn, hin] at hwpos; linarith
    have hdot1 : 0 < octDot I K := (mul_pos_iff_of_pos_left hr).mp <| by
      have h := congrArg (octDot I) hdecomp
      rw [octDot_comm, octDot_add_left, octDot_self, hn, octDot_comm octI, octDot_comm I (r • K), octDot_smul_left, octDot_comm K] at h
      linarith
    have hdot2 : 0 < octDot K octI := (mul_pos_iff_of_pos_left hr).mp <| by
      have h := congrArg (octDot · octI) hdecomp
      rw [octDot_add_left, octDot_self, hin, octDot_smul_left] at h; linarith
    obtain ⟨g1, hg1, h1⟩ := exists_orderThree_map I K hi hre hn hkn (by linarith)
    obtain ⟨g2, hg2, h2⟩ := exists_orderThree_map K octI hre rfl hkn hin (by linarith)
    exact ⟨g2.comp g1, diagonalOctTriple_comp g2 g1 hg2 hg1, by change g2.A (g1.A I) = octI; rw [h1, h2]⟩

end
end Glennie
