module
public import GS.Spectral.Slice
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
@[expose] public section

/-! Multiplication by `I` identifies the self-adjoint and skew-adjoint real
summands, so the complex dimension calculation needs no matrix-coordinate enumeration. -/
noncomputable section
open Matrix GS.Isometric
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace GS.Spectral
variable {q : ℕ}
private lemma twice_im (A : Type*) [AddCommGroup A] [Module ℂ A] [Module ℝ A]
    [StarAddMonoid A] [StarModule ℂ A] [StarModule ℝ A] [SMulCommClass ℝ ℂ A] [FiniteDimensional ℝ A] :
    2 * Module.finrank ℝ ↥(skewAdjoint.submodule ℝ A) = Module.finrank ℝ A := by
  let e : ↥(skewAdjoint.submodule ℝ A) ≃ₗ[ℝ] ↥(selfAdjoint.submodule ℝ A) := {
    toFun a := ⟨-Complex.I • a.val,(skewAdjoint.negISMul (a : skewAdjoint A)).property⟩
    invFun a := ⟨Complex.I • a.val,Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint.mpr a.property⟩
    left_inv a := Subtype.ext (by simp [smul_smul])
    right_inv a := Subtype.ext (by simp [smul_smul])
    map_add' _ _ := Subtype.ext (by simp)
    map_smul' _ _ := Subtype.ext (by simp [smul_comm]) }
  have h := (StarModule.decomposeProdAdjoint ℝ A).finrank_eq
  change _ = Module.finrank ℝ (↥(selfAdjoint.submodule ℝ A) × ↥(skewAdjoint.submodule ℝ A)) at h
  rw [Module.finrank_prod,← e.finrank_eq] at h; omega

lemma complex_width (Q : U ℂ q) (o : Fin q) (hne : ∀ i j, Q.val i j ≠ 0) : Width Q o = (q-1)^2 := by
  have H := twice_im (Square ℂ q); have h := twice_im ℂ
  simp only [Square,Module.finrank_matrix,Fintype.card_fin,Complex.finrank_real_complex] at H h
  have hs : skewSpace (⊤ : Layer ℂ q) = skewAdjoint.submodule ℝ (Square ℂ q) := by ext X; exact and_iff_right trivial
  have eq := width_add Q o hne
  unfold G Generator at eq; rw [hs] at eq
  have z : Module.finrank ℝ (Im ℂ) = 1 := by unfold Im; omega
  rw [z,mul_one] at eq
  have : q - 1 + 1 = q := by have ho := o.isLt; omega
  grind

lemma real_width (Q : U ℝ q) (o : Fin q) (hne : ∀ i j, Q.val i j ≠ 0) (hq : 3 ≤ q) : 2 ≤ Width Q o := by
  letI : Subsingleton (Im ℝ) := ⟨fun x y => Subtype.ext (by have hx : x.val = -x.val := x.property; have hy : y.val = -y.val := y.property; linarith)⟩
  have h := width_add Q o hne; simp [Module.finrank_zero_of_subsingleton] at h
  let a (i : Fin 3) := i.castLE hq
  let f : G ℝ q →ₗ[ℝ] (Fin 2 → ℝ) := { toFun X i := X.val (a 0) (a i.succ),map_add' _ _ := rfl,map_smul' _ _ := rfl }
  have sur : Function.Surjective f := by
    intro x; let A : Mat q := fun i j => if i=a 0 then (if j=a 1 then x 0 else x 1) else 0
    refine ⟨⟨A-Aᵀ,trivial,by simp [Skew]⟩,?_⟩
    ext i; fin_cases i <;> simp [f,A,a,Fin.ext_iff]
  have dim := LinearMap.finrank_le_finrank_of_surjective sur
  simpa [← h] using dim
end GS.Spectral
