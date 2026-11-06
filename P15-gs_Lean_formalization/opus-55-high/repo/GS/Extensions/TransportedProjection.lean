module

public import GS.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact Frobenius projection after orthogonal changes of coordinates

Here `Admissible` is an explicitly defined
linear space. It is not renamed a manifold tangent space by fiat. Identification
with the derivative image of the two-factor parametrization is a later theorem;
identification with a manifold tangent bundle requires the orbit-manifold proof.
-/

noncomputable section
open Matrix
namespace GS.Extensions
variable {n : ℕ}

 def lift (L R X : Mat n) : Mat n := L * X * R
 def pull (L R Z : Mat n) : Mat n := Lᵀ * Z * Rᵀ

 def transportedProjection (p : Fin n → Fin n → Prop) [DecidableRel p]
    (L R Z : Mat n) : Mat n := lift L R (maskedSkew p (pull L R Z))

 def Admissible (p : Fin n → Fin n → Prop) (L R X : Mat n) : Prop :=
  ∃ Y : Mat n, HasSupport p Y ∧ IsSkew Y ∧ X = lift L R Y

 theorem pull_lift (L R Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    pull L R (lift L R Y) = Y := by
  calc
    pull L R (lift L R Y) = (Lᵀ*L)*Y*(R*Rᵀ) := by
      simp only [pull, lift, Matrix.mul_assoc]
    _ = Y := by rw [hL.1, hR.2]; simp

 theorem lift_pull (L R Z : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    lift L R (pull L R Z) = Z := by
  calc
    lift L R (pull L R Z) = (L*Lᵀ)*Z*(Rᵀ*R) := by
      simp only [pull, lift, Matrix.mul_assoc]
    _ = Z := by rw [hL.2, hR.1]; simp

 theorem lift_injective (L R : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    Function.Injective (lift L R) := by
  intro X Y h
  have := congrArg (pull L R) h
  simpa only [pull_lift L R _ hL hR] using this

 theorem lift_sub (L R X Y : Mat n) :
    lift L R (X-Y) = lift L R X - lift L R Y := by
  simp [lift, Matrix.mul_sub, Matrix.sub_mul]

 theorem pull_sub (L R X Y : Mat n) :
    pull L R (X-Y) = pull L R X - pull L R Y := by
  simp [pull, Matrix.mul_sub, Matrix.sub_mul]

 theorem lift_frobInner (L R X Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobInner (lift L R X) (lift L R Y) = frobInner X Y := by
  unfold lift
  rw [frobInner_right_orthogonal R hR, frobInner_left_orthogonal L hL]

 theorem frobInner_mul_right (A B C : Mat n) :
    frobInner (A*B) C = frobInner A (C*Bᵀ) := by
  calc
    frobInner (A*B) C = frobInner (A*B)ᵀ Cᵀ :=
      (frobInner_transpose _ _).symm
    _ = frobInner Aᵀ (B*Cᵀ) := by
      rw [Matrix.transpose_mul, frobInner_mul_left, Matrix.transpose_transpose]
    _ = frobInner A (C*Bᵀ) := by
      have h := frobInner_transpose A (C*Bᵀ)
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h

 theorem lift_adjoint (L R Z Y : Mat n) :
    frobInner Z (lift L R Y) = frobInner (pull L R Z) Y := by
  rw [frobInner_comm, lift, frobInner_mul_right, frobInner_mul_left,
    frobInner_comm]
  simp only [pull, Matrix.mul_assoc]

 theorem maskedSkew_fixed {p : Fin n → Fin n → Prop} [DecidableRel p]
    {X : Mat n} (hs : HasSupport p X) (hk : IsSkew X) : maskedSkew p X = X := by
  rw [maskedSkew, skew_of_isSkew hk, mask_fixed hs]

 theorem admissible_projection (p : Fin n → Fin n → Prop) [DecidableRel p]
    (hp : MaskSymmetric p) (L R Z : Mat n) :
    Admissible p L R (transportedProjection p L R Z) :=
  ⟨maskedSkew p (pull L R Z), mask_hasSupport p _,
    mask_isSkew hp (isSkew_skew _), rfl⟩

 theorem projection_fixed {p : Fin n → Fin n → Prop} [DecidableRel p]
    (L R X : Mat n) (hL : Orthogonal L) (hR : Orthogonal R)
    (hX : Admissible p L R X) : transportedProjection p L R X = X := by
  obtain ⟨Y,hs,hk,rfl⟩ := hX
  unfold transportedProjection
  rw [pull_lift L R Y hL hR, maskedSkew_fixed hs hk]

 theorem projection_residual_orthogonal {p : Fin n → Fin n → Prop} [DecidableRel p]
    (L R Z X : Mat n) (hL : Orthogonal L) (hR : Orthogonal R)
    (hX : Admissible p L R X) :
    frobInner (Z - transportedProjection p L R Z) X = 0 := by
  obtain ⟨Y,hs,hk,rfl⟩ := hX
  rw [lift_adjoint, pull_sub]
  unfold transportedProjection
  rw [pull_lift L R _ hL hR]
  exact maskedSkew_residual_orthogonal (pull L R Z) Y hs hk

 theorem projection_self_adjoint (p : Fin n → Fin n → Prop) [DecidableRel p]
    (hp : MaskSymmetric p) (L R A B : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobInner (transportedProjection p L R A) B =
      frobInner A (transportedProjection p L R B) := by
  have h₁ := projection_residual_orthogonal L R A
    (transportedProjection p L R B) hL hR (admissible_projection p hp L R B)
  have h₂ := projection_residual_orthogonal L R B
    (transportedProjection p L R A) hL hR (admissible_projection p hp L R A)
  rw [frobInner_sub_left] at h₁ h₂
  rw [frobInner_comm B _, frobInner_comm (transportedProjection p L R B) _] at h₂
  linarith

end GS.Extensions
