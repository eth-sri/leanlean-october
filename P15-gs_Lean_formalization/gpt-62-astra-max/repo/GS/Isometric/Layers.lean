module

public import GS.Isometric.Cayley
public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-! A layer is any real star subalgebra of the ambient matrix algebra. Its unitary
factors form a compact group and its skew elements are global Cayley parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {s : Layer 𝕜 n} {A B C : Square 𝕜 n}

def skewSpace (s : Layer 𝕜 n) : Submodule ℝ (Square 𝕜 n) :=
  (s.toSubalgebra.toSubmodule ⊓ skewAdjoint.submodule ℝ _).copy {A | A ∈ s ∧ Skew A} rfl
abbrev Generator (s : Layer 𝕜 n) := ↥(skewSpace s)

def SharedFactor (s : Layer 𝕜 n) (A : Square 𝕜 n) := A ∈ s ∧ IsU A
lemma shared_factor_conjTranspose (hA : SharedFactor s A) : SharedFactor s Aᴴ :=
  ⟨star_mem hA.1, hA.2.conjTranspose⟩
lemma shared_factor_mul (hA : SharedFactor s A) (hB : SharedFactor s B) : SharedFactor s (A*B) :=
  ⟨mul_mem hA.1 hB.1, hA.2.mul hB.2⟩
lemma sharedSkew_conjugate (hA : SharedFactor s A) (hC : C ∈ skewSpace s) : A*C*Aᴴ ∈ skewSpace s :=
  ⟨mul_mem (mul_mem hA.1 hC.1) (star_mem hA.1), by simp [Skew, Matrix.mul_assoc, hC.2]⟩

/-- In a finite-dimensional unital algebra injective left multiplication is surjective. -/
lemma layer_inverse (hA : A ∈ s) (hd : IsUnit A) : A⁻¹ ∈ s := by
  haveI : FiniteDimensional ℝ s := FiniteDimensional.of_injective s.subtype.toLinearMap Subtype.val_injective
  let L : s →ₗ[ℝ] s := LinearMap.mulLeft ℝ (⟨A,hA⟩ : s)
  have hinj : Function.Injective L := fun X Y h => Subtype.ext (hd.mul_right_inj.mp (congrArg Subtype.val h))
  obtain ⟨X,hX⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact Matrix.inv_eq_right_inv (show A * X.val = 1 from congrArg Subtype.val hX) ▸ X.property
lemma cayley_mem_layer (hm : A ∈ s) (hd : admissible A) : cayley A ∈ s :=
  mul_mem (sub_mem (one_mem s) hm) (layer_inverse (add_mem (one_mem s) hm) hd)
lemma cayley_shared (hA : A ∈ skewSpace s) : SharedFactor s (cayley A) :=
  let hd := admissible_of_isSkew A hA.2
  ⟨cayley_mem_layer hA.1 hd, cayley_unitary A hA.2 hd⟩
lemma cayley_sharedSkew (hA : SharedFactor s A) (hd : admissible A) : cayley A ∈ skewSpace s :=
  ⟨cayley_mem_layer hA.1 hd, cayley_isSkew _ hA.2 hd⟩

def subgroup (s : Layer 𝕜 n) : Subgroup (unitary (Square 𝕜 n)) where
  carrier := {A | A.val ∈ s}
  one_mem' := one_mem s
  mul_mem' {x y} hx hy := show x.val * y.val ∈ s from s.mul_mem hx hy
  inv_mem' {x} hA := show star x.val ∈ s from star_mem (show x.val ∈ s from hA)
abbrev Factor (s : Layer 𝕜 n) := ↥(subgroup s)
abbrev Factors (right left : Layer 𝕜 n) := Factor left × Factor right
namespace Factor
def matrix (U : Factor s) : Square 𝕜 n := U.val.val
lemma matrix_shared (U : Factor s) : SharedFactor s (matrix U) := ⟨U.property, U.val.property⟩
lemma matrix_unitary (U : Factor s) : IsU (matrix U) := U.val.property
lemma matrix_injective : Function.Injective (matrix : Factor s → _) :=
  Subtype.val_injective.comp Subtype.val_injective
@[fun_prop] lemma continuous_matrix : Continuous (matrix : Factor s → _) := continuous_subtype_val.comp continuous_subtype_val

def ofMatrix (A : Square 𝕜 n) (hA : SharedFactor s A) : Factor s := ⟨⟨A,hA.2⟩,hA.1⟩
end Factor

lemma entry_bound (hA : IsU A) (i j : Fin n) : ‖A i j‖ ≤ 1 := by
  have he := congrArg RCLike.re (congrFun (congrFun hA.1 j) j)
  have hsum : ∑ k, ‖A k j‖ ^ 2 = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul,
      map_sum, RCLike.re_ofReal_pow, Matrix.one_apply_eq, RCLike.one_re] using he
  have h := Finset.single_le_sum (f := fun k => ‖A k j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith

instance unitaryCompact : CompactSpace (unitary (Square 𝕜 n)) := by
  apply isCompact_iff_compactSpace.mp
  have hb : IsCompact {A : Square 𝕜 n | ∀ i j, A i j ∈ Metric.closedBall (0 : 𝕜) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall _ _
  exact hb.of_isClosed_subset isClosed_unitary fun A h i j => by simpa using entry_bound h i j
instance factorCompactSpace (s : Layer 𝕜 n) : CompactSpace (Factor s) :=
  isCompact_iff_compactSpace.mp (s.toSubalgebra.toSubmodule.closed_of_finiteDimensional.preimage
    (continuous_subtype_val (p := (· ∈ unitary (Square 𝕜 n))))).isCompact

end GS.Isometric
