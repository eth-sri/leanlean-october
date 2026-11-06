/- Finite native eigenvalue separation for the bounded fixed-frame gate.
-/
module
public import Glennie.Native.CoordinateSimp

public import AlbertRecognition.FixedFrame.ReferenceBlocks

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie
open scoped BigOperators

/-- Actual complementary diagonal curvature vanishes, on every native input. -/
theorem D_h0_h1_zero : D (h 0) (h 1) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [D_apply_native]
  apply Albert.ext
  all_goals simp [albert_coords, h, e, smul_smul]
  all_goals norm_num

/-- The distinguished h0 also commutes with the complementary slot12 action. -/
theorem D_h0_X12_zero (a : Octonion) : D (h 0) (X12 a) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [D_apply_native]
  apply Albert.ext
  all_goals simp [albert_coords, h, e, X12, smul_smul, smul_add, smul_sub]
  all_goals first
    | exact sub_self _
    | (solve | (norm_num <;> ring))
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        simp [smul_eq_mul] <;> ring)

/-- Raw coordinate units have unit octDot norm; raw slots are not rescaled. -/
theorem octDot_basis_self (t : Fin 8) : octDot (octBasis t) (octBasis t) = 1 := by
  fin_cases t <;> norm_num [octBasis, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    octScalar, qi, qj, qk]

theorem octBasis_imag_square (t : Fin 8) (ht : t ≠ 0) :
    octMul (octBasis t) (octBasis t) = octScalar (-1) := by
  fin_cases t <;> simp_all [octBasis]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [albert_coords, qi, qj, qk]

/-- Native brackets plus proved right alternativity give each J_t squared. -/
theorem spinJ_basis_square (t : Fin 8) (s : Spin) :
    spinJ (octBasis t) (spinJ (octBasis t) s) = -s := by
  rcases s with ⟨u,v⟩
  by_cases ht : t = 0
  · subst t
    simp [octBasis]
  · rw [spinJ_imag_apply _ (octBasis_conj_imag t ht),
      spinJ_imag_apply _ (octBasis_conj_imag t ht)]
    have hsquare (z : Octonion) :
        octMul (octMul z (octBasis t)) (octBasis t) = -z := by
      rw [octMul_right_alternative, octBasis_imag_square t ht, octMul_scalar_right]
      simp
    apply Prod.ext
    · exact hsquare u
    · exact hsquare v

def frameSquare (a : Octonion) : Module.End ℝ V :=
  (frameAction a).comp (frameAction a)

/-- Literal eight-term sum of the squared native operators, without renormalization. -/
def frameSquareSum : Module.End ℝ V := ∑ t : Fin 8, frameSquare (octBasis t)

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
  simp only [frameSquare, LinearMap.comp_apply, frameAction_X12, map_smul,
    frameAction_d]
  module

theorem frameSquare_spin (t : Fin 8) (s : Spin) :
    frameSquare (octBasis t) (frameSpin s) = -(9/16 : ℝ) • frameSpin s := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_spin, map_smul,
    spinJ_basis_square, map_neg]
  module

theorem frameSquareSum_h0 : frameSquareSum (h 0) = 0 := by
  simp [frameSquareSum, LinearMap.sum_apply, frameSquare_h0]

theorem frameSquareSum_d : frameSquareSum frameD = -(18 : ℝ) • frameD := by
  simp only [frameSquareSum, LinearMap.sum_apply, frameSquare_d, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

theorem frameSquareSum_X12 (z : Octonion) :
    frameSquareSum (X12 z) = -(9/4 : ℝ) • X12 z := by
  simp only [frameSquareSum, LinearMap.sum_apply, frameSquare_X12,
    ← Finset.smul_sum, ← map_sum, ← oct_decompose]

theorem frameSquareSum_spin (s : Spin) :
    frameSquareSum (frameSpin s) = -(9/2 : ℝ) • frameSpin s := by
  simp only [frameSquareSum, LinearMap.sum_apply, frameSquare_spin, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

/-- Four actual rational eigenvalues, on the exact1+1+8+16 coordinates. -/
theorem frameSquareSum_frameEmbed (a b : ℝ) (z : Octonion) (s : Spin) :
    frameSquareSum (frameEmbed (a,b,z,s)) =
      frameEmbed (0,-18*b,-(9/4 : ℝ) • z,-(9/2 : ℝ) • s) := by
  rw [frameEmbed_eq, frameEmbed_eq]
  simp only [map_add, map_smul, frameSquareSum_h0, frameSquareSum_d,
    frameSquareSum_X12, frameSquareSum_spin, zero_smul, zero_add]
  module

theorem frameSquareSum_coordinates (x : V) :
    frameCoordinates (frameSquareSum x) =
      (0,-18*(frameCoordinates x).2.1,-(9/4 : ℝ) • (frameCoordinates x).2.2.1,
        -(9/2 : ℝ) • (frameCoordinates x).2.2.2) := by
  obtain ⟨⟨a, b, z, s⟩, rfl⟩ := frameCoordinates.symm.surjective x
  simpa only [frameEmbed, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] using
    congrArg frameCoordinates (frameSquareSum_frameEmbed a b z s)

private theorem scalar_eigen_iff {M : Type*} [AddCommGroup M] [Module ℝ M]
    (r s : ℝ) (x : M) : r • x = s • x ↔ r = s ∨ x = 0 := by
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero]

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
  unfold FrameBlock
  generalize frameCoordinates x = c
  rcases c with ⟨a,b,z,s⟩
  fin_cases k <;> norm_num [frameLambda, Prod.smul_mk, Prod.neg_mk,
    Prod.mk.injEq, scalar_eigen_iff, mul_eq_mul_right_iff]

/-- An arbitrary linear operator commuting with all8 native actions commutes
with their literal squared sum. No metric or self-adjointness premise is used. -/
theorem frameSquareSum_commutes (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G.comp frameSquareSum = frameSquareSum.comp G := by
  change Commute G _
  apply Commute.sum_right
  intro t _
  exact (show Commute G (frameAction (octBasis t)) from hG t).mul_right (hG t)

/-- Abstract linear eigenvector preservation, proved before specializing the
closed native eight-square operator. No spectral or metric premise is assumed. -/
private theorem linear_commutant_preserves_eigenvector {M : Type*}
    [AddCommGroup M] [Module ℝ M] (G T : Module.End ℝ M)
    (hGT : G.comp T = T.comp G) (lambda : ℝ) (x : M)
    (hx : T x = lambda • x) : T (G x) = lambda • G x := by
  have h := LinearMap.congr_fun hGT x
  change G (T x) = T (G x) at h
  rw [hx, map_smul] at h
  exact h.symm

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
