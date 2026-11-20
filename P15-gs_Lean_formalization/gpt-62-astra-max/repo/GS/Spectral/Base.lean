module
public import GS.Spectral.Normalize
@[expose] public section

/-! Every representative over the scalar point belongs to the same dephased
chart. This uses positivity only at the anchors, not uniqueness of a basis. -/
noncomputable section
open Matrix GS.Isometric
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace GS.Spectral
variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ} (Q : U 𝕜 q) (o : Fin q)
def base : Box 𝕜 q := fun i j => Q.val i j • 1
lemma build_base (s : U 𝕜 2) : build (1 : Outer 𝕜 o) s (fun _ => Q) = base Q := by
  funext i j; have he : right (1 : Outer 𝕜 o) j = 1 := by by_cases h : j=o <;> simp [right,h]
  have hd : diagonal (fun _ : Fin 2 => Q.val i j) = Q.val i j • (1 : Square 𝕜 2) := by
    ext a b; by_cases h : a=b <;> simp [diagonal_apply,one_apply,h]
  simp [build,middle,mix,base,he,hd,mul_assoc]

lemma good_base (p : Raw 𝕜 q) (he : eval p = base Q) (hne : ∀ i j, Q.val i j ≠ 0) : ∀ k, Good Q o (p.2.1 k) := by
  have h (i j) : ∏ k, (p.2.1 k).val i j ≠ 0 := by
    have eq := congrArg det (congrFun (congrFun he i) j)
    simp only [eval,base,det_mul,det_diagonal,det_smul,det_one,mul_one] at eq
    exact fun hz => pow_ne_zero 2 (hne i j) (by simp_all)
  have e i j k := div_ne_zero ((Finset.prod_ne_zero_iff.mp (h i j)) k (Finset.mem_univ _)) (hne i j)
  exact fun k => ⟨fun i => e i o k,fun j => e o j k⟩

lemma ref_anchored (hne : ∀ i j, Q.val i j ≠ 0) : Anchored Q o Q :=
  ⟨fun i => by simp [hne], fun j => by simp [hne]⟩

lemma clean_base (p : Raw 𝕜 q) (he : eval p = base Q) (hne : ∀ i j, Q.val i j ≠ 0) (k : Fin 2) :
    clean Q o (p.2.1 k) = Q := by
  have E := ((build_fibres Q o (fun l => clean_anchored Q o (good_base Q o p he hne l))
    (fun _ => ref_anchored Q o hne)).1 ((build_clean Q o p).trans (he.trans (build_base Q o (p.2.2 o)).symm))).2
  apply Subtype.ext; ext i j
  exact mix_eq.mp (congrFun (congrFun E i) j) k k (by simp)
end GS.Spectral
