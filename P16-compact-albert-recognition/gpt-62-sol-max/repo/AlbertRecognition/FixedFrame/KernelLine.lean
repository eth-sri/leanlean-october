module

public import AlbertRecognition.FixedFrame.CyclicPullback
public import Glennie.Diagonalization
public import AlbertRecognition.CubicAlgebra
@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

set_option maxHeartbeats 100000
set_option maxSynthPendingDepth 3
attribute [local irreducible] KB

private theorem common_zero (x : V) (H : ∀ a, frameAction a x = 0) : ∃ b : ℝ, x = b • h 0 := by
  have hh (a) := congrArg (fun v : V => (v : Albert)) (H a)
  simp only [frameAction_apply, Submodule.coe_zero] at hh
  have h01 := congrArg Albert.o02 (hh (octScalar 1))
  have h02 := congrArg Albert.o01 (hh (octScalar 1))
  have h12 := congrArg Albert.d2 (hh (x : Albert).o12)
  have hdd := congrArg (fun v : Albert => v.o12.1.re) (hh (octScalar 1))
  norm_num [octScalar, smul_eq_zero] at hdd
  norm_num [smul_eq_zero, octNormSq_eq_zero] at h01 h02 h12
  refine ⟨(x : Albert).d1, Subtype.ext ?_⟩
  have ht := show (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 from trace_V x
  apply Albert.ext <;> simp [h, e, h01, h02, h12] <;> linarith

private theorem h0_eigen (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) :
    ∃ c : ℝ, KB B (h 0) (h 0) = c • h 0 := by
  apply common_zero
  intro a
  have H := congrArg (fun L : V →ₗ[ℝ] V => L (h 0)) (h0_frame_commutes_of_A_q_zero B hB a)
  have hfix : frameAction a (h 0) = 0 := by
    apply Subtype.ext
    simp [frameAction_apply, h, e, octDot_zero_right, octMul_zero_left] <;> rfl
  simpa only [operatorComm_apply, hfix, map_zero, zero_sub, neg_eq_zero, LinearMap.zero_apply] using H

private theorem h_orbit (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) (g : CompactAutomorphism) :
    ∃ c : ℝ, KB B (automorphismV g (h 0)) (automorphismV g (h 0)) = c • automorphismV g (h 0) := by
  obtain ⟨c,hc⟩ := h0_eigen _ (A_q_pullback_zero g B hB)
  exact ⟨c, by rw [← automorphismV_KB_pullback, hc, map_smul]⟩

private theorem h2_eq : h 2 = -(h 0 + h 1) := eq_neg_of_add_eq_zero_right h_sum_zero

private theorem diagonal_metric (i j : Fin 3) : gA (h i) (h j) = if i = j then 2 else -1 := by
  fin_cases i <;> fin_cases j <;> norm_num [gA, h, e, unit, inner_coordinates, octDot_coordinates, octNormSq_zero]

private theorem diagonal_eigen (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) :
    ∃ c : ℝ, ∀ i, KB B (h i) (h i) = c • h i := by
  have he (i : Fin 3) : ∃ c : ℝ, KB B (h i) (h i) = c • h i := by
    have hi : (Equiv.subRight i).symm 0 = i := zero_add i
    simpa only [permutation_h, hi] using h_orbit B hB (permutationAutomorphism (Equiv.subRight i))
  choose c hc using he
  have p (i j : Fin 3) : B.form (h i) (h i) (h j) = c i * (if i = j then 2 else -1) := by
    simp only [← KB_pairing, hc, ← metricBilin_apply (c i • h i) (h j), map_smul,
      LinearMap.smul_apply, smul_eq_mul, metricBilin_apply, diagonal_metric]
  have H (j : Fin 3) := p 2 j
  simp only [h2_eq, map_neg, map_add, LinearMap.neg_apply, LinearMap.add_apply,
    B.swap12 (h 1) (h 0)] at H
  have e₀ := H 0
  have e₁ := H 1
  rw [B.swap23 (h 0) (h 1) (h 0)] at e₀
  rw [B.swap12 (h 0) (h 1) (h 1), B.swap23 (h 1) (h 0) (h 1)] at e₁
  norm_num [p] at e₀ e₁
  refine ⟨c 2, fun i => ?_⟩
  rw [hc]
  congr 1
  fin_cases i <;> first | rfl | exact (show c 0 = c 2 by linarith) | exact (show c 1 = c 2 by linarith)

private theorem KA_h_sq (i : Fin 3) : KA (h i) (h i) = -h i := by
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    norm_num [KA_apply, project_coe, traceless, trace, h, e, unit, jordan_coord, oct_coord,
      octDot_coordinates]

private theorem diag_parallel (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) :
    ∃ r : ℝ, ∀ a b : ℝ, let x := a • h 0 + b • h 1; KB B x x = r • KA x x := by
  obtain ⟨c,hc⟩ := diagonal_eigen B hB
  let L := KB B + c • KA
  have hL (i : Fin 3) : L (h i) (h i) = 0 := by
    simp only [L, LinearMap.add_apply, LinearMap.smul_apply, hc, KA_h_sq, smul_neg, add_neg_cancel]
  have Lsym (x y : V) : L x y = L y x := by
    simp only [L, LinearMap.add_apply, LinearMap.smul_apply, KB_comm B x y, KA_comm x y]
  have h01 := hL 2
  simp only [h2_eq, map_neg, map_add, LinearMap.neg_apply, LinearMap.add_apply,
    Lsym (h 1) (h 0), hL, zero_add, add_zero] at h01
  refine ⟨-c, fun a b => ?_⟩
  let x := a • h 0 + b • h 1
  have H : L x x = 0 := by
    simp only [x, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hL, Lsym (h 1) (h 0), smul_zero, zero_add, add_zero]
    linear_combination (norm := module) (a*b) • h01
  change KB B x x = (-c) • KA x x
  simpa [L, neg_smul, eq_neg_iff_add_eq_zero] using H

private theorem diagonal_decompose (x : V) (hx : IsDiagonal (x : Albert)) :
    x = (((x : Albert).d2 - (x : Albert).d0) / 3) • h 0 +
      (((x : Albert).d2 - (x : Albert).d1) / 3) • h 1 := by
  rcases hx with ⟨h01,h02,h12⟩
  apply Subtype.ext
  apply Albert.ext <;> simp [h, e, h01, h02, h12] <;> linarith [show
    (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 from trace_V x]

private theorem square_parallel (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) (x : V) :
    ∃ c : ℝ, KB B x x = c • KA x x := by
  obtain ⟨g,hg⟩ := native_diagonalization (x : Albert)
  let y := automorphismV g x
  have hy : automorphismV g.symm y = x := Subtype.ext (g.equiv.symm_apply_apply (x : Albert))
  obtain ⟨c,hc⟩ := diag_parallel (pullbackCubic (automorphismV g.symm) B) (A_q_pullback_zero _ B hB)
  have p : KB (pullbackCubic (automorphismV g.symm) B) y y  = c • KA y y := by
    rw [diagonal_decompose y hg]
    exact hc ..
  refine ⟨c, ?_⟩
  simpa only [automorphismV_KB_pullback, map_smul, automorphismV_KA, hy] using
    congrArg (automorphismV g.symm) p

/-- The two lowest coefficients on each line through `v` propagate the scale at `v`. -/
private theorem proportional (B C : SymmetricCubic) (v : V) (hv : C.form v v v ≠ 0)
    (H : ∀ x, ∃ c : ℝ, KB B x x = c • KB C x x) : ∃ c, B = scalarCubic c C := by
  obtain ⟨c, hc⟩ := H v
  let F : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ := B.form - c • C.form
  have swap₁₂ (x y z : V) : F x y z = F y x z := by
    simp only [F, LinearMap.sub_apply, LinearMap.smul_apply, B.swap12 x y z, C.swap12 x y z]
  have swap₂₃ (x y z : V) : F x y z = F x z y := by
    simp only [F, LinearMap.sub_apply, LinearMap.smul_apply, B.swap23 x y z, C.swap23 x y z]
  have fac (x : V) (d : ℝ) (hd : KB B x x = d • KB C x x) (z : V) :
      F x x z = (d-c)*C.form x x z := by
    simp only [F, LinearMap.sub_apply, LinearMap.smul_apply, ← KB_pairing, hd,
      ← metricBilin_apply (d • KB C x x), map_smul, smul_eq_mul, metricBilin_apply]
    ring
  have vv (z : V) : F v v z = 0 := by rw [fac v c hc, sub_self, zero_mul]
  have cross (x z : V) : F x x z * C.form x x v = F x x v * C.form x x z := by
    obtain ⟨d,hd⟩ := H x
    rw [fac _ d hd z, fac _ d hd v]
    ring
  have rel (y z : V) (t : ℝ) := cross (v+t•y) z
  have fvv (y : V) : F v y v = 0 := (swap₂₃ ..).trans (vv y)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    swap₁₂ _ v, vv, fvv, mul_zero, zero_add, add_zero] at rel
  have yy (y z : V) : F y y z = 0 := by
    have vy (z : V) : F v y z = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hv
      linear_combination (8*(rel y z 1 - rel y z (-1)) - (rel y z 2 - rel y z (-2)))/24
    have R := rel y z
    simp only [vy, show F y y v = 0 by rw [swap₂₃, swap₁₂, vy], mul_zero, zero_add, zero_mul] at R
    apply (mul_eq_zero.mp ?_).resolve_right hv
    linear_combination (16*(R 1 + R (-1))-(R 2+R (-2)))/24
  refine ⟨c, symmetricCubic_eq_of_form_eq (sub_eq_zero.mp ?_)⟩
  change F = 0
  ext x y z : 3
  have P := yy (x+y) z
  simp only [map_add, LinearMap.add_apply, swap₁₂ y x, yy, zero_add, add_zero] at P
  simpa only [LinearMap.zero_apply] using (show F x y z = 0 by linarith)

theorem reference_nativeKernelLine (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : ∃ b : ℝ, B = scalarCubic b referenceCubic := by
  apply proportional B referenceCubic (h 0)
  · rw [← KB_pairing, KB_referenceCubic, KA_h_sq, ← metricBilin_apply, ← LinearMap.flip_apply, map_neg,
      LinearMap.flip_apply, metricBilin_apply, diagonal_metric]
    norm_num
  · simpa only [KB_referenceCubic] using square_parallel B hB

end
end AlbertRecognition.FixedFrame
