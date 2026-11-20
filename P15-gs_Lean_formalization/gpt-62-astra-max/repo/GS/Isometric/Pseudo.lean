module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section

/-! The minimum-norm least-squares lift on a constant-rank family. In a
frame `w` of the range, the normal equations for the lift are nonsingular:
write the lift as `f c`, with `f = u† w`, and solve `f† f c = w† z`.
This same solution works in every frame. A frame at one point extends
locally by applying the moving operator to fixed preimages of its basis. -/
noncomputable section
open ContinuousLinearMap Function Filter
open scoped InnerProduct Topology
namespace GS.Isometric.Pseudo
variable {G A E : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (u : G →L[ℝ] A) (w : E →L[ℝ] A)
def normal := let f := u† ∘L w; f† ∘L f
def candidate := (u† ∘L w) ∘L (normal u w).inverse ∘L w†
private lemma inj_range : Set.InjOn (u†) u.range := by
  apply LinearMap.disjoint_ker_iff_injOn.mp
  rw [← u.orthogonal_range]; exact u.range.orthogonal_disjoint
private lemma regular (i : Injective w) (r : w.range = u.range) : (normal u w).IsInvertible := by
  let f := u† ∘L w
  have h : Injective f := fun a b e => i (inj_range u (r ▸ LinearMap.mem_range_self w.toLinearMap a) (r ▸ LinearMap.mem_range_self w.toLinearMap b) e)
  have hi := f.adjoint_comp_self_injective_iff.mpr h
  exact ⟨(LinearEquiv.ofBijective (normal u w).toLinearMap ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv,rfl⟩
private lemma fit (r : w.range = u.range) (h : (normal u w).IsInvertible) (z : A) :
    u (candidate u w z) = u.range.starProjection z := by
  symm; apply Submodule.eq_starProjection_of_mem_orthogonal (LinearMap.mem_range_self u.toLinearMap _)
  rw [← r,w.orthogonal_range]; change (w†) (z - u (candidate u w z)) = 0
  rw [map_sub,sub_eq_zero]; simpa [normal,candidate,adjoint_comp] using (h.self_apply_inverse ((w†) z)).symm

def lift := candidate u u.range.subtypeL
lemma lift_spec (z : A) : u (lift u z) = u.range.starProjection z :=
  fit u u.range.subtypeL (by simp) (regular u u.range.subtypeL Subtype.val_injective (by simp)) z
private lemma frame_eq (r : w.range = u.range) (h : (normal u w).IsInvertible) : lift u = candidate u w := by
  ext z
  have hi := inj_range (u†); rw [adjoint_adjoint] at hi
  exact hi ⟨_,rfl⟩ ⟨_,rfl⟩ ((lift_spec u z).trans (fit u w r h z).symm)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
@[fun_prop] private lemma smooth_adj {f : V → E →L[ℝ] A} (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (fun x => (f x)†) :=
  (adjoint : (E →L[ℝ] A) ≃ₗᵢ[ℝ] (A →L[ℝ] E)).toContinuousLinearEquiv.contDiff.comp hf

lemma smooth {u : V → G →L[ℝ] A} (hu : ContDiff ℝ ⊤ u) {k : ℕ} (hr : ∀ x, Module.finrank ℝ (u x).range = k) :
    ContDiff ℝ ⊤ (fun x => lift (u x)) := by
  apply contDiff_iff_contDiffAt.2; intro x
  let S := (u x).range
  obtain ⟨a,ha⟩ := (u x).toLinearMap.rangeRestrict.exists_rightInverse_of_surjective (u x).toLinearMap.range_rangeRestrict
  let w (y : V) := u y ∘L a.toContinuousLinearMap
  have hw : w x = S.subtypeL := ext fun z => congrArg Subtype.val (DFunLike.congr_fun ha z)
  have fit₀ := regular (u x) (S.subtypeL) Subtype.val_injective (by simp [S])
  have wn : ContDiff ℝ ⊤ w := hu.clm_comp contDiff_const
  have hn : ContDiff ℝ ⊤ (fun y => normal (u y) (w y)) := by unfold normal; fun_prop
  rw [← hw] at fit₀
  apply ContDiffAt.congr_of_eventuallyEq (f := fun y => candidate (u y) (w y))
  · have inv : ContDiffAt ℝ ⊤ (fun y => (normal (u y) (w y)).inverse) x := fit₀.contDiffAt_map_inverse.comp (f := fun y => normal (u y) (w y)) x hn.contDiffAt
    exact ((smooth_adj hu).clm_comp wn).contDiffAt.clm_comp (inv.clm_comp (smooth_adj wn).contDiffAt)
  · filter_upwards [hn.continuous.continuousAt.eventually fit₀.eventually_nhds] with y hy
    apply frame_eq _ _ _ hy
    have hi : Injective (w y) := by
      intro a b hab; apply hy.injective; simp [normal,hab]
    apply Submodule.eq_of_le_of_finrank_le (LinearMap.range_comp_le_range ..)
    change Module.finrank ℝ (u y).range ≤ Module.finrank ℝ (w y).range
    rw [LinearMap.finrank_range_of_inj hi,hr y,hr x]
end GS.Isometric.Pseudo
