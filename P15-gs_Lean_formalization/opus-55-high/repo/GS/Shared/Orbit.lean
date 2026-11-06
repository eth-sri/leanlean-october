module

public import GS.Shared.Factors
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section


/-!
# The shared matrix family as a compact homogeneous space

The action is L X R*, with actual shared unitary factors and conjugate transpose R*.
Its orbit is
exactly the previously defined `InShared` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/


noncomputable section
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InShared (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : 𝕄) : Prop :=
  ∃ L R : 𝕄, SharedFactor b₂ τ₂ L ∧
    SharedFactor b₁ τ₁ R ∧ X = L * P * R

instance factorsMulAction (right left : Pattern 𝕜 n) :
    MulAction (Factors right left) (𝕄) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ
  one_smul X := by
    change (1 : 𝕄) * X * (1 : 𝕄)ᴴ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᴴ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᴴ) *
        (Factor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : 𝕄) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern 𝕜 n) :
    ContinuousSMul (Factors right left) (𝕄) where
  continuous_smul := by
    simp
    have := Factor.continuous_matrix (s := left)
    have := Factor.continuous_matrix (s := right)
    fun_prop

section
variable (right left : Pattern 𝕜 n) (P : 𝕄)
def orbitMap : Factors right left → 𝕄 :=
  fun g => g • P

abbrev MatrixOrbit :=
  ↥(MulAction.orbit (Factors right left) P)

abbrev PointStabilizer :=
  MulAction.stabilizer (Factors right left) P


end

theorem continuous_orbitMap (P : 𝕄) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : 𝕄) :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InShared right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᴴ, Factor.matrix_shared g.1,
      shared_factor_conjTranspose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᴴ (shared_factor_conjTranspose hR)), ?_⟩
    aesop

theorem orbit_set_eq_inShared (P : 𝕄) :
    MulAction.orbit (Factors right left) P =
      {X | InShared right.size left.size right.label left.label P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern 𝕜 n) (P : 𝕄) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, by tauto⟩

section
variable (P : 𝕄)
theorem surjective_orbitMapToOrbit :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩



end

theorem action_frob (g : Factors right left) (X Y : 𝕄) :
    frob (g • X) (g • Y) = frob X Y :=
  frob_unitary g.1.matrix_unitary g.2.matrix_unitary X Y


section
variable (P : 𝕄)
theorem orbit_fibre_iff (g h : Factors right left) :
    orbitMap right left P g = orbitMap right left P h ↔
      g⁻¹ * h ∈ PointStabilizer right left P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  rw [mul_smul, inv_smul_eq_iff, eq_comm]



theorem closed_of_orbit_preimage_closed (s : Set (MatrixOrbit right left P))
    (hs : IsClosed (orbitMapToOrbit right left P ⁻¹' s)) : IsClosed s := by
  have he : s = orbitMapToOrbit right left P '' (orbitMapToOrbit right left P ⁻¹' s) := by
    ext x
    constructor
    · obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      grind
    grind
  rw [he]
  exact (hs.isCompact.image ((continuous_orbitMap P).subtype_mk _)).isClosed

theorem orbit_saturation (s : Set (Factors right left)) :
    orbitMapToOrbit right left P ⁻¹' (orbitMapToOrbit right left P '' s) =
      ⋃ h : PointStabilizer right left P,
        (fun g : Factors right left => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer right left P := ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    aesop
  · intro hg
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
    refine ⟨g * h.val, hh, ?_⟩
    apply Subtype.ext
    change (g * h.val) • P = g • P
    rw [mul_smul, show h.val • P = P from h.property]

/-- Images of factor neighbourhoods are orbit neighbourhoods.  No continuous
or smooth section of the orbit map is asserted by this openness result. -/
theorem orbitMapToOrbit_isOpenMap :
    IsOpenMap (orbitMapToOrbit right left P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit right left P ⁻¹'
      (orbitMapToOrbit right left P '' s)) := by
    rw [orbit_saturation]
    exact isOpen_iUnion (fun h => hs.preimage (continuous_id.mul continuous_const))
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit right left P '' s)ᶜ (by simp_all)
  simp_all

end

end GS.Shared
