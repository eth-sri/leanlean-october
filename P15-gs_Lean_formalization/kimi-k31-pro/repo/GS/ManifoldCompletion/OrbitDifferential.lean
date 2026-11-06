module

public import GS.ManifoldCompletion.OrbitSmooth
public import GS.CayleyCharts.Differential
public import GS.Extensions.GeodesicNormal

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- Obtain the derivative from the identity c(A)(1+A)=1-A. -/
theorem chartInv_line_hasDerivAt_zero (Q : BlockO block) (v : Model block) :
    HasDerivAt (fun t : ℝ => chartInv Q (t • v)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  let V := fderiv ℝ (chartInv Q) 0 v
  have hd : HasDerivAt (fun t : ℝ => chartInv Q (t • v)) V 0 := by
    have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hi.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • v.val) v.val 0 := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hm : HasDerivAt (fun t : ℝ => (1 : Mat n) - t • v.val) (-v.val) 0 := by
    simpa only [Pi.sub_def, id_eq, zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hleft := hasDerivAt_matrix_mul hd hp
  have hright := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) hm
  have hid : (fun t : ℝ => chartInv Q (t • v) * (1 + t • v.val)) =
      (fun t : ℝ => Q.val * (1 - t • v.val)) := by
    funext t
    change Q.val * cayley ((t • v).val) * (1 + (t • v).val) = _
    rw [Matrix.mul_assoc, cayley_mul _ (admissible_model (t • v))]
    rfl
  rw [hid] at hleft
  have hv : V + Q.val * v.val = -(Q.val * v.val) := by
    simpa only [zero_smul, add_zero, sub_zero, chartInv_zero, Matrix.mul_one,
      Matrix.zero_mul, zero_add, Matrix.mul_neg] using hleft.unique hright
  have he : V = (-2 : ℝ) • (Q.val * v.val) := by
    ext i j
    have hh := congrFun (congrFun hv i) j
    change V i j + (Q.val * v.val) i j = -(Q.val * v.val) i j at hh
    change V i j = (-2 : ℝ) * (Q.val * v.val) i j
    linarith
  rwa [he] at hd

/-- Translate the factor-side injectivity condition into disjoint supports. -/
theorem noOverlap_offDiagonalDisjoint (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm) := by
  intro i j h₂ h₁
  apply σ.symm.injective
  apply hn
  apply Prod.ext
  · exact h₁
  · simpa only [Equiv.apply_symm_apply] using h₂

end GS.ManifoldCompletion
