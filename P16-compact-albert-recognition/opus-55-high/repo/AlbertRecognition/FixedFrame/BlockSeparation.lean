/- Finite native eigenvalue separation for the bounded fixed-frame gate.
-/
module

public import AlbertRecognition.FixedFrame.ReferenceBlocks

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

@[simp] theorem octPair_zero : ((0, 0) : Octonion) = 0 := rfl

/-- Actual complementary diagonal curvature vanishes, on every native input. -/
theorem D_h0_h1_zero : D (h 0) (h 1) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [D_apply_native]
  apply Albert.ext
  all_goals simp [h, e, oct_simps, octPair_zero, smul_smul]
  all_goals norm_num

/-- The distinguished h0 also commutes with the complementary slot12 action. -/
theorem D_h0_X12_zero (a : Octonion) : D (h 0) (X12 a) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [D_apply_native]
  apply Albert.ext
  all_goals simp [h, e, X12, oct_simps, octPair_zero, smul_smul, smul_add, smul_sub]
  all_goals first
    | exact sub_self _
    | (solve | (norm_num <;> ring))
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        simp [smul_eq_mul] <;> ring)

/-- Raw coordinate units have unit octDot norm; raw slots are not rescaled. -/
theorem octDot_basis_self (t : Fin 8) : octDot (octBasis t) (octBasis t) = 1 := by
  fin_cases t <;> norm_num [octBasis, oct_simps, qi, qj, qk]

theorem octBasis_imag_square (t : Fin 8) (ht : t ≠ 0) :
    octMul (octBasis t) (octBasis t) = octScalar (-1) := by
  fin_cases t <;> simp_all [octBasis]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [oct_simps, qi, qj, qk]

/-- Native brackets plus proved right alternativity give each J_t squared. -/
theorem spinJ_basis_square (t : Fin 8) (s : Spin) :
    spinJ (octBasis t) (spinJ (octBasis t) s) = -s := by
  rcases s with ⟨u,v⟩
  by_cases ht : t = 0
  · simp_all
  · rw [spinJ_imag_apply _ (octBasis_conj_imag t ht),
      spinJ_imag_apply _ (octBasis_conj_imag t ht)]
    have hsquare (z : Octonion) :
        octMul (octMul z (octBasis t)) (octBasis t) = -z := by
      rw [octMul_right_alternative, octBasis_imag_square t ht, octMul_scalar_right]
      simp
    apply Prod.ext <;> aesop

/-- The literal eight-coordinate resolution, with every coefficient native. -/
theorem oct_basis_resolution (z : Octonion) :
    octDot (octBasis 0) z • octBasis 0 + octDot (octBasis 1) z • octBasis 1 +
      octDot (octBasis 2) z • octBasis 2 + octDot (octBasis 3) z • octBasis 3 +
      octDot (octBasis 4) z • octBasis 4 + octDot (octBasis 5) z • octBasis 5 +
      octDot (octBasis 6) z • octBasis 6 + octDot (octBasis 7) z • octBasis 7 = z := by ext <;> simp [octBasis, oct_simps, qi, qj, qk]

def frameSquare (a : Octonion) : Module.End ℝ V :=
  (frameAction a).comp (frameAction a)

/-- Literal eight-term sum of the squared native operators, without renormalization. -/
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
    frameAction_X12, octDot_basis_self]
  module

theorem frameSquare_X12 (t : Fin 8) (z : Octonion) :
    frameSquare (octBasis t) (X12 z) =
      -(9/4 : ℝ) • X12 (octDot (octBasis t) z • octBasis t) := by
  simp [frameSquare, LinearMap.comp_apply, frameAction_X12, map_smul,
    frameAction_d]
  module

theorem frameSquare_spin (t : Fin 8) (s : Spin) :
    frameSquare (octBasis t) (frameSpin s) = -(9/16 : ℝ) • frameSpin s := by
  simp [frameSquare, LinearMap.comp_apply, frameAction_spin, map_smul,
    spinJ_basis_square, map_neg]
  module

theorem frameSquareSum_h0 : frameSquareSum (h 0) = 0 := by
  simp [frameSquareSum, frameSquare_h0]

theorem frameSquareSum_d : frameSquareSum frameD = -(18 : ℝ) • frameD := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_d]
  module

theorem frameSquareSum_X12 (z : Octonion) :
    frameSquareSum (X12 z) = -(9/4 : ℝ) • X12 z := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_X12]
  have h := congrArg (fun x => -(9/4 : ℝ) • x)
    (congrArg X12 (oct_basis_resolution z))
  simpa only [map_add, smul_add] using h

theorem frameSquareSum_spin (s : Spin) :
    frameSquareSum (frameSpin s) = -(9/2 : ℝ) • frameSpin s := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_spin]
  module

/-- Four actual rational eigenvalues, on the exact1+1+8+16 coordinates. -/
theorem frameSquareSum_frameEmbed (a b : ℝ) (z : Octonion) (s : Spin) :
    frameSquareSum (frameEmbed (a,b,z,s)) =
      frameEmbed (0,-18*b,-(9/4 : ℝ) • z,-(9/2 : ℝ) • s) := by
  rw [frameEmbed_eq, frameEmbed_eq]
  simp [map_add, map_smul, frameSquareSum_h0, frameSquareSum_d,
    frameSquareSum_X12, frameSquareSum_spin, zero_smul, zero_add]
  module

theorem frameSquareSum_coordinates (x : V) :
    frameCoordinates (frameSquareSum x) =
      (0,-18*(frameCoordinates x).2.1,-(9/4 : ℝ) • (frameCoordinates x).2.2.1,
        -(9/2 : ℝ) • (frameCoordinates x).2.2.2) := by
  let c := frameCoordinates x
  have hx := frameCoordinates.symm_apply_apply x
  calc
    frameCoordinates (frameSquareSum x) =
        frameCoordinates (frameSquareSum (frameEmbed (c.1,c.2.1,c.2.2.1,c.2.2.2))) :=
      congrArg (fun y => frameCoordinates (frameSquareSum y)) hx.symm
    _ = _ := by
      rw [frameSquareSum_frameEmbed]
      exact frameCoordinates.apply_symm_apply _

def frameLambda : Fin 4 → ℝ := ![0,-18,-(9/4),-(9/2)]

def FrameBlock (k : Fin 4) (x : V) : Prop :=
  ![(frameCoordinates x).2.1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
      (frameCoordinates x).2.2.2 = 0,
    (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
      (frameCoordinates x).2.2.2 = 0,
    (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
      (frameCoordinates x).2.2.2 = 0,
    (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
      (frameCoordinates x).2.2.1 = 0] k

/-- The four eigenspaces are exactly the four concrete native coordinate blocks. -/
theorem frame_eigen_iff (k : Fin 4) (x : V) :
    frameSquareSum x = frameLambda k • x ↔ FrameBlock k x := by
  rw [← frameCoordinates.injective.eq_iff, frameSquareSum_coordinates, map_smul]
  have se {M : Type} [AddCommGroup M] [Module ℝ M] (r t : ℝ) (v : M) :
      r • v = t • v ↔ r = t ∨ v = 0 := by
    rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero]
  fin_cases k <;> norm_num [FrameBlock, frameLambda, Prod.ext_iff, se]

/-- An arbitrary linear operator commuting with all8 native actions commutes
with their literal squared sum. No metric or self-adjointness premise is used. -/
theorem frameSquareSum_commutes (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G.comp frameSquareSum = frameSquareSum.comp G := by
  have h t y : G (frameAction (octBasis t) y) = frameAction (octBasis t) (G y) :=
    LinearMap.congr_fun (hG t) y
  ext1 x
  simp only [LinearMap.comp_apply, frameSquareSum, frameSquare, LinearMap.add_apply, map_add, h]

/-- Abstract linear eigenvector preservation, proved before specializing the
closed native eight-square operator. No spectral or metric premise is assumed. -/
theorem linear_commutant_preserves_eigenvector {M : Type*}
    [AddCommGroup M] [Module ℝ M] (G T : Module.End ℝ M)
    (hGT : G.comp T = T.comp G) (lambda : ℝ) (x : M)
    (hx : T x = lambda • x) : T (G x) = lambda • G x := by
  simpa [hx] using (LinearMap.congr_fun hGT x).symm

section FrameBlockPreservation

/- Keep the proved closed operator opaque only during this final proof's
elaboration; its definition and kernel-level body are unchanged. -/
attribute [local irreducible] frameSquareSum

/-- Finite block separation for every arbitrary real-linear commutant. -/
theorem frame_commutant_preserves_blocks (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (k : Fin 4) (x : V)
    (hx : FrameBlock k x) : FrameBlock k (G x) := by
  set_option backward.isDefEq.respectTransparency true in
    with_reducible
      apply (frame_eigen_iff k (G x)).mp
      exact @linear_commutant_preserves_eigenvector V inferInstance inferInstance
        G frameSquareSum (frameSquareSum_commutes G hG) (frameLambda k) x
        ((frame_eigen_iff k x).mpr hx)

end FrameBlockPreservation

end
end AlbertRecognition.FixedFrame
