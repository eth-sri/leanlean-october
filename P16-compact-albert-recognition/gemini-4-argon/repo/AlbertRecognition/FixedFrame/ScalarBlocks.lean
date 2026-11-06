module

public import AlbertRecognition.FixedFrame.ReferenceBlocks

@[expose] public section
namespace AlbertRecognition
noncomputable section

@[simp] theorem operatorComm_apply (P Q : V →ₗ[ℝ] V) (v : V) :
    operatorComm P Q v = P (Q v) - Q (P v) := rfl

@[simp] theorem operatorComm_zero_right (P : V →ₗ[ℝ] V) :
    operatorComm P 0 = 0 := by
  apply LinearMap.ext; intro v; simp only [operatorComm_apply, LinearMap.zero_apply, map_zero, sub_self]

theorem operatorComm_add_right (P Q R : V →ₗ[ℝ] V) :
    operatorComm P (Q + R) = operatorComm P Q + operatorComm P R := by
  apply LinearMap.ext; intro v; simp only [operatorComm_apply, LinearMap.add_apply, map_add]; module

theorem operatorComm_swap (P Q : V →ₗ[ℝ] V) :
    operatorComm P Q = -operatorComm Q P := by
  apply LinearMap.ext; intro v; simp only [operatorComm_apply, LinearMap.neg_apply, neg_sub]

theorem wedge_swap (x y : V) : wedge x y = -wedge y x := by
  apply LinearMap.ext; intro v; exact (neg_sub (gA x v • y) (gA y v • x)).symm

/-- Total cubic symmetry cancels the entire wedge Jacobi term. -/
theorem A_wedge_eq_zero (B : SymmetricCubic) : A wedge B = 0 := by
  funext x y z; apply LinearMap.ext; intro v
  change
    ((KB B x) (gA z v • y - gA y v • z) -
      (gA z (KB B x v) • y - gA y (KB B x v) • z)) +
    ((KB B y) (gA x v • z - gA z v • x) -
      (gA x (KB B y v) • z - gA z (KB B y v) • x)) +
    ((KB B z) (gA y v • x - gA x v • y) -
      (gA y (KB B z v) • x - gA x (KB B z v) • y)) = 0
  simp only [map_sub, map_smul,
    ← KB_selfadjoint B x z v, ← KB_selfadjoint B x y v,
    ← KB_selfadjoint B y x v, ← KB_selfadjoint B y z v,
    ← KB_selfadjoint B z y v, ← KB_selfadjoint B z x v,
    KB_comm B x y, KB_comm B x z, KB_comm B y z]
  module

theorem A_add_target (T U : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic) :
    A (fun x y => T x y + U x y) B = A T B + A U B := by
  funext x y z; simp only [A, operatorComm_add_right, Pi.add_apply]; module

theorem A_D_eq_A_q (B : SymmetricCubic) :
    A D B = A (q referenceCubic) B := by
  change A (fun x y => wedge x y + q referenceCubic x y) B = _
  rw [A_add_target, A_wedge_eq_zero, zero_add]

theorem A_D_zero_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : A D B = 0 := by
  rw [A_D_eq_A_q]; exact hB

theorem D_swap (x y : V) : D y x = -D x y := by
  unfold D q
  rw [wedge_swap y x, operatorComm_swap (KB referenceCubic y) (KB referenceCubic x)]
  module

theorem commutes_of_A_D_zero_of_vanishing (B : SymmetricCubic)
    (hB : A D B = 0) (x y z : V)
    (hxy : D x y = 0) (hxz : D x z = 0) :
    operatorComm (KB B x) (D y z) = 0 := by
  have hzx : D z x = 0 := by rw [D_swap, hxz, neg_zero]
  have hcyclic : A D B x y z = 0 := congrArg (fun F => F x y z) hB
  simpa only [A, hzx, hxy, operatorComm_zero_right, zero_add, add_zero] using hcyclic

namespace FixedFrame
open Glennie

@[simp] private theorem octPair_zero : ((0, 0) : Octonion) = 0 := rfl

/-- Actual complementary diagonal curvature vanishes, on every native input. -/
theorem D_h0_h1_zero : D (h 0) (h 1) = 0 := by
  apply LinearMap.ext; intro x; apply Subtype.ext; rw [D_apply_native]
  apply Albert.ext <;>
    simp [h, e, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, octPair_zero, smul_smul, smul_eq_mul] <;>
    norm_num

/-- The distinguished h0 also commutes with the complementary slot12 action. -/
theorem D_h0_X12_zero (a : Octonion) : D (h 0) (X12 a) = 0 := by
  apply LinearMap.ext; intro x; apply Subtype.ext; rw [D_apply_native]
  apply Albert.ext
  all_goals simp [h, e, X12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
    octMul, octConj, octPair_zero, smul_smul, smul_add, smul_sub, smul_eq_mul]
  all_goals first
    | exact sub_self _
    | (solve | (norm_num <;> ring))
    | (apply Prod.ext <;> apply Quaternion.ext <;> simp [smul_eq_mul] <;> ring)

theorem h0_frame_commutes_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (a : Glennie.Octonion) :
    operatorComm (KB B (h 0)) (frameAction a) = 0 :=
  commutes_of_A_D_zero_of_vanishing B (A_D_zero_of_A_q_zero B hB)
    (h 0) (h 1) (X12 a) D_h0_h1_zero (D_h0_X12_zero a)

theorem h0_frame_action_intertwines_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (a : Glennie.Octonion) (v : V) :
    KB B (h 0) (frameAction a v) = frameAction a (KB B (h 0) v) :=
  sub_eq_zero.mp (congrArg (fun P : V →ₗ[ℝ] V => P v) (h0_frame_commutes_of_A_q_zero B hB a))

theorem octDot_basis_self (t : Fin 8) : octDot (octBasis t) (octBasis t) = 1 := by
  fin_cases t <;> norm_num [octBasis, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    octScalar, qi, qj, qk]

theorem octBasis_imag_square (t : Fin 8) (ht : t ≠ 0) :
    octMul (octBasis t) (octBasis t) = octScalar (-1) := by
  fin_cases t <;> simp_all [octBasis]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [octMul, octScalar, qi, qj, qk,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem spinJ_basis_square (t : Fin 8) (s : Spin) :
    spinJ (octBasis t) (spinJ (octBasis t) s) = -s := by
  rcases s with ⟨u,v⟩
  by_cases ht : t = 0
  · subst t; simp
  · rw [spinJ_imag_apply _ (octBasis_conj_imag t ht),
      spinJ_imag_apply _ (octBasis_conj_imag t ht)]
    have hsquare (z : Octonion) : octMul (octMul z (octBasis t)) (octBasis t) = -z := by
      rw [octMul_right_alternative, octBasis_imag_square t ht, octMul_scalar_right]; simp
    exact Prod.ext (hsquare u) (hsquare v)

theorem oct_basis_resolution (z : Octonion) :
    octDot (octBasis 0) z • octBasis 0 + octDot (octBasis 1) z • octBasis 1 +
      octDot (octBasis 2) z • octBasis 2 + octDot (octBasis 3) z • octBasis 3 +
      octDot (octBasis 4) z • octBasis 4 + octDot (octBasis 5) z • octBasis 5 +
      octDot (octBasis 6) z • octBasis 6 + octDot (octBasis 7) z • octBasis 7 = z := by
  simpa [octBasis, octDot_coordinates, octScalar, qi, qj, qk] using (oct_decompose z).symm

def frameSquare (a : Octonion) : Module.End ℝ V :=
  (frameAction a).comp (frameAction a)

def frameSquareSum : Module.End ℝ V :=
  frameSquare (octBasis 0) + frameSquare (octBasis 1) +
    frameSquare (octBasis 2) + frameSquare (octBasis 3) +
    frameSquare (octBasis 4) + frameSquare (octBasis 5) +
    frameSquare (octBasis 6) + frameSquare (octBasis 7)

theorem frameSquare_h0 (a : Octonion) : frameSquare a (h 0) = 0 := by
  simp [frameSquare, frameAction_h0]

theorem frameSquare_d (t : Fin 8) :
    frameSquare (octBasis t) frameD = -(9/4 : ℝ) • frameD := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_d, map_smul,
    frameAction_X12, octDot_basis_self]; module

theorem frameSquare_X12 (t : Fin 8) (z : Octonion) :
    frameSquare (octBasis t) (X12 z) =
      -(9/4 : ℝ) • X12 (octDot (octBasis t) z • octBasis t) := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_X12, map_smul, frameAction_d]; module

theorem frameSquare_spin (t : Fin 8) (s : Spin) :
    frameSquare (octBasis t) (frameSpin s) = -(9/16 : ℝ) • frameSpin s := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_spin, map_smul,
    spinJ_basis_square, map_neg]; module

theorem frameSquareSum_h0 : frameSquareSum (h 0) = 0 := by
  simp [frameSquareSum, frameSquare_h0]

theorem frameSquareSum_d : frameSquareSum frameD = -(18 : ℝ) • frameD := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_d]; module

theorem frameSquareSum_X12 (z : Octonion) :
    frameSquareSum (X12 z) = -(9/4 : ℝ) • X12 z := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_X12]
  simpa only [map_add, smul_add] using
    congrArg (fun x : V => -(9/4 : ℝ) • x) (congrArg X12 (oct_basis_resolution z))

theorem frameSquareSum_spin (s : Spin) :
    frameSquareSum (frameSpin s) = -(9/2 : ℝ) • frameSpin s := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_spin]; module

theorem frameSquareSum_frameEmbed (a b : ℝ) (z : Octonion) (s : Spin) :
    frameSquareSum (frameEmbed (a,b,z,s)) =
      frameEmbed (0,-18*b,-(9/4 : ℝ) • z,-(9/2 : ℝ) • s) := by
  rw [frameEmbed_eq, frameEmbed_eq]
  simp only [map_add, map_smul, frameSquareSum_h0, frameSquareSum_d,
    frameSquareSum_X12, frameSquareSum_spin, zero_smul, zero_add]; module

theorem frameSquareSum_coordinates (x : V) :
    frameCoordinates (frameSquareSum x) =
      (0,-18*(frameCoordinates x).2.1,-(9/4 : ℝ) • (frameCoordinates x).2.2.1,
        -(9/2 : ℝ) • (frameCoordinates x).2.2.2) := by
  let c := frameCoordinates x
  have hx : frameEmbed (c.1,c.2.1,c.2.2.1,c.2.2.2) = x := frameCoordinates.symm_apply_apply x
  calc frameCoordinates (frameSquareSum x)
    _ = frameCoordinates (frameSquareSum (frameEmbed (c.1,c.2.1,c.2.2.1,c.2.2.2))) :=
      congrArg (fun y : V => frameCoordinates (frameSquareSum y)) hx.symm
    _ = _ := by rw [frameSquareSum_frameEmbed]; exact frameCoordinates.apply_symm_apply _

theorem frame_eigen_equations (lambda : ℝ) (x : V)
    (hx : frameSquareSum x = lambda • x) :
    0 = lambda*(frameCoordinates x).1 ∧
      -18*(frameCoordinates x).2.1 = lambda*(frameCoordinates x).2.1 ∧
      -(9/4 : ℝ) • (frameCoordinates x).2.2.1 = lambda • (frameCoordinates x).2.2.1 ∧
      -(9/2 : ℝ) • (frameCoordinates x).2.2.2 = lambda • (frameCoordinates x).2.2.2 := by
  have h := congrArg frameCoordinates hx
  rw [frameSquareSum_coordinates, map_smul] at h
  exact ⟨congrArg (fun c : FrameCoordinates => c.1) h,
    congrArg (fun c : FrameCoordinates => c.2.1) h,
    congrArg (fun c : FrameCoordinates => c.2.2.1) h,
    congrArg (fun c : FrameCoordinates => c.2.2.2) h⟩

private theorem scalar_eigen_conflict {M : Type*} [AddCommGroup M] [Module ℝ M]
    (r s : ℝ) (x : M) (hx : r • x = s • x) (hrs : r ≠ s) : x = 0 := by
  have hzero : (r - s) • x = 0 := by rw [sub_smul, hx, sub_self]
  simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hrs), one_smul, smul_zero] using
    congrArg (fun y : M => (r - s)⁻¹ • y) hzero

theorem frameSquareSum_commutes (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G.comp frameSquareSum = frameSquareSum.comp G := by
  have hs (t : Fin 8) (x : V) :
      G (frameSquare (octBasis t) x) = frameSquare (octBasis t) (G x) := by
    have h (y : V) : G (frameAction (octBasis t) y) = frameAction (octBasis t) (G y) :=
      LinearMap.congr_fun (hG t) y
    change G (frameAction (octBasis t) (frameAction (octBasis t) x)) =
      frameAction (octBasis t) (frameAction (octBasis t) (G x))
    rw [h, h]
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, frameSquareSum, LinearMap.add_apply, map_add, hs]

section FrameBlockPreservation
attribute [local irreducible] frameSquareSum

private theorem frameSquareSum_G_eigen (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (lambda : ℝ) (x : V)
    (hx : frameSquareSum x = lambda • x) :
    0 = lambda*(frameCoordinates (G x)).1 ∧
      -18*(frameCoordinates (G x)).2.1 = lambda*(frameCoordinates (G x)).2.1 ∧
      (lambda ≠ -(9/4 : ℝ) → (frameCoordinates (G x)).2.2.1 = 0) ∧
      (lambda ≠ -(9/2 : ℝ) → (frameCoordinates (G x)).2.2.2 = 0) := by
  obtain ⟨ha, hb, hz, hs⟩ := frame_eigen_equations lambda (G x) (by
    have h := LinearMap.congr_fun (frameSquareSum_commutes G hG) x
    change G (frameSquareSum x) = frameSquareSum (G x) at h
    rw [← h, hx, map_smul])
  exact ⟨ha, hb,
    fun hne => scalar_eigen_conflict (M := Octonion) (-(9/4 : ℝ)) lambda (frameCoordinates (G x)).2.2.1 hz hne.symm,
    fun hne => scalar_eigen_conflict (M := Spin) (-(9/2 : ℝ)) lambda (frameCoordinates (G x)).2.2.2 hs hne.symm⟩

end FrameBlockPreservation

private theorem oct_domain_linear_ext {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (f g : Octonion →ₗ[ℝ] M)
    (h : ∀ t : Fin 8, f (octBasis t) = g (octBasis t)) : f = g := by
  apply LinearMap.ext; intro z; rw [oct_decompose z]; simp only [map_add, map_smul, h]

def frameSpinProjection : V →ₗ[ℝ] Spin :=
  (LinearMap.snd ℝ Octonion Spin).comp
    ((LinearMap.snd ℝ ℝ (Octonion × Spin)).comp
      ((LinearMap.snd ℝ ℝ (ℝ × Octonion × Spin)).comp frameCoordinates.toLinearMap))

@[simp] theorem frameSpinProjection_apply (x : V) :
    frameSpinProjection x = (frameCoordinates x).2.2.2 := rfl

@[simp] theorem frameSpinProjection_frameSpin (s : Spin) :
    frameSpinProjection (frameSpin s) = s := by
  rcases s with ⟨u,v⟩
  change (((frameSpin (u,v) : V) : Albert).o01, ((frameSpin (u,v) : V) : Albert).o02) = (u,v)
  simp [frameSpin, X01, X02]

theorem frameSpin_injective : Function.Injective frameSpin := fun _ _ h => by
  simpa only [frameSpinProjection_frameSpin] using congrArg frameSpinProjection h

theorem frame_commutant_h0_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G (h 0) = (frameCoordinates (G (h 0))).1 • h 0 := by
  obtain ⟨_, hb, hz, hs⟩ := frameSquareSum_G_eigen G hG 0 (h 0)
    (by rw [frameSquareSum_h0, zero_smul])
  have hd := frame_decompose (G (h 0))
  rw [show (frameCoordinates (G (h 0))).2.1 = 0 by linarith, hz (by norm_num), hs (by norm_num)] at hd
  simpa only [zero_smul, map_zero, add_zero] using hd

theorem frame_commutant_d_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G frameD = (frameCoordinates (G frameD)).2.1 • frameD := by
  obtain ⟨ha, _, hz, hs⟩ := frameSquareSum_G_eigen G hG (-18) frameD
    (by simpa only [neg_smul] using frameSquareSum_d)
  have hd := frame_decompose (G frameD)
  rw [show (frameCoordinates (G frameD)).1 = 0 by linarith, hz (by norm_num), hs (by norm_num)] at hd
  simpa only [zero_smul, map_zero, zero_add, add_zero] using hd

theorem frame_commutant_X12_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G)
    (b : ℝ) (hd : G frameD = b • frameD) (z : Octonion) :
    G (X12 z) = b • X12 z := by
  have hb (t : Fin 8) : G (X12 (octBasis t)) = b • X12 (octBasis t) := by
    have h := LinearMap.congr_fun (hG t) frameD
    change G (frameAction (octBasis t) frameD) = frameAction (octBasis t) (G frameD) at h
    rw [frameAction_d, map_smul, hd, map_smul, frameAction_d] at h
    have h' := congrArg (fun v : V => (2/3 : ℝ) • v) h
    simpa only [smul_smul, show (2/3 : ℝ)*(3/2) = 1 by norm_num,
      show (2/3 : ℝ)*(b*(3/2)) = b by ring, one_smul] using h'
  exact LinearMap.congr_fun (oct_domain_linear_ext (G.comp X12) (b • X12) hb) z

def nativeSpinRestriction (G : Module.End ℝ V) : Module.End ℝ Spin :=
  frameSpinProjection.comp (G.comp frameSpin)

theorem frame_commutant_spin_reconstruct (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (s : Spin) :
    G (frameSpin s) = frameSpin (nativeSpinRestriction G s) := by
  obtain ⟨ha, hb, hz, _⟩ := frameSquareSum_G_eigen G hG (-(9/2)) (frameSpin s)
    (by simpa only [neg_smul] using frameSquareSum_spin s)
  have hd := frame_decompose (G (frameSpin s))
  rw [show (frameCoordinates (G (frameSpin s))).1 = 0 by linarith,
    show (frameCoordinates (G (frameSpin s))).2.1 = 0 by linarith, hz (by norm_num)] at hd
  simpa only [zero_smul, zero_add, map_zero, nativeSpinRestriction,
    LinearMap.comp_apply, frameSpinProjection_apply] using hd

theorem nativeSpinRestriction_commutes (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (t : Fin 8) :
    (nativeSpinRestriction G).comp (spinJ (octBasis t)) =
      (spinJ (octBasis t)).comp (nativeSpinRestriction G) := by
  apply LinearMap.ext; intro s; apply frameSpin_injective
  have hscaled :
      (3/4 : ℝ) • frameSpin (nativeSpinRestriction G (spinJ (octBasis t) s)) =
        (3/4 : ℝ) • frameSpin (spinJ (octBasis t) (nativeSpinRestriction G s)) := by
    calc (3/4 : ℝ) • frameSpin (nativeSpinRestriction G (spinJ (octBasis t) s))
      _ = G (frameAction (octBasis t) (frameSpin s)) := by
        rw [frameAction_spin, map_smul, frame_commutant_spin_reconstruct G hG]
      _ = frameAction (octBasis t) (G (frameSpin s)) := LinearMap.congr_fun (hG t) (frameSpin s)
      _ = (3/4 : ℝ) • frameSpin (spinJ (octBasis t) (nativeSpinRestriction G s)) := by
        rw [frame_commutant_spin_reconstruct G hG, frameAction_spin]
  simpa only [LinearMap.comp_apply, smul_smul, show (4/3 : ℝ)*(3/4) = 1 by norm_num, one_smul] using
    congrArg (fun v : V => (4/3 : ℝ) • v) hscaled

theorem frame_commutant_spin_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    ∃ c : ℝ, ∀ s : Spin, G (frameSpin s) = c • frameSpin s := by
  obtain ⟨c,hc⟩ := spin_commutant_scalar (nativeSpinRestriction G)
    (nativeSpinRestriction_commutes G hG)
  exact ⟨c, fun s => by rw [frame_commutant_spin_reconstruct G hG, hc]; exact map_smul frameSpin c s⟩

theorem frame_commutant_scalar_blocks (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    ∃ a b c : ℝ, G (h 0) = a • h 0 ∧ G frameD = b • frameD ∧
      (∀ z : Octonion, G (X12 z) = b • X12 z) ∧
      (∀ s : Spin, G (frameSpin s) = c • frameSpin s) := by
  obtain ⟨c,hc⟩ := frame_commutant_spin_scalar G hG
  exact ⟨_, _, c, frame_commutant_h0_scalar G hG, frame_commutant_d_scalar G hG,
    frame_commutant_X12_scalar G hG _ (frame_commutant_d_scalar G hG), hc⟩

theorem h1_half_h0_eq_frameD :
    h 1 + (1/2 : ℝ) • h 0 = -(3/2 : ℝ) • frameD := by
  have hneg (x : Albert) : -x = ⟨-x.d0,-x.d1,-x.d2,-x.o01,-x.o02,-x.o12⟩ := rfl
  apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, unit, frameD, hneg]

theorem h2_half_h0_eq_frameD :
    h 2 + (1/2 : ℝ) • h 0 = (3/2 : ℝ) • frameD := by
  apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, unit, frameD]

theorem frame_commutant_h0_coarse_actions (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    ∃ a b c : ℝ, G (h 0) = a • h 0 ∧
      (∀ j : Fin 3, j ≠ 0 →
        G (h j + (1/2 : ℝ) • h 0) = b • (h j + (1/2 : ℝ) • h 0)) ∧
      (∀ u : Octonion, G (X01 u) = c • X01 u) ∧
      (∀ u : Octonion, G (X02 u) = c • X02 u) ∧
      (∀ u : Octonion, G (X12 u) = b • X12 u) := by
  obtain ⟨a,b,c,ha,hb,h12,hs⟩ := frame_commutant_scalar_blocks G hG
  refine ⟨a,b,c,ha,fun j hj => ?_,
    fun u => by simpa only [frameSpin_apply, map_zero, add_zero] using hs (u,0),
    fun u => by simpa only [frameSpin_apply, map_zero, zero_add] using hs (0,u), h12⟩
  fin_cases j
  · exact False.elim (hj rfl)
  · change G (h 1 + (1/2 : ℝ) • h 0) = b • (h 1 + (1/2 : ℝ) • h 0)
    rw [h1_half_h0_eq_frameD, map_smul, hb]; module
  · change G (h 2 + (1/2 : ℝ) • h 0) = b • (h 2 + (1/2 : ℝ) • h 0)
    rw [h2_half_h0_eq_frameD, map_smul, hb]; module

theorem h0_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 0) (h 0) = a • h 0 ∧
      (∀ j : Fin 3, j ≠ 0 →
        KB B (h 0) (h j + (1/2 : ℝ) • h 0) =
          b • (h j + (1/2 : ℝ) • h 0)) ∧
      (∀ u : Octonion, KB B (h 0) (X01 u) = c • X01 u) ∧
      (∀ u : Octonion, KB B (h 0) (X02 u) = c • X02 u) ∧
      (∀ u : Octonion, KB B (h 0) (X12 u) = b • X12 u) :=
  frame_commutant_h0_coarse_actions (KB B (h 0)) fun t =>
    LinearMap.ext (h0_frame_action_intertwines_of_A_q_zero B hB (octBasis t))

end FixedFrame
end
end AlbertRecognition
