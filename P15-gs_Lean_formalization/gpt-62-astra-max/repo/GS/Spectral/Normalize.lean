module
public import GS.Spectral.Phases
@[expose] public section

/-! Separate the two independent outer frames using positive anchor blocks.
Only this separation uses polar uniqueness; it does not require singular
vectors to depend continuously on the matrix. -/
noncomputable section
open Matrix GS.Isometric
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace GS.Spectral
variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}
section
variable {o : Fin q}
abbrev Outer (𝕜 : Type*) [RCLike 𝕜] {q} (o : Fin q) := (Fin q → U 𝕜 2) × ({j // j ≠ o} → U 𝕜 2)
def right (g : Outer 𝕜 o) (j : Fin q) : U 𝕜 2 := if h : j = o then 1 else g.2 ⟨j,h⟩
@[simp] lemma right_anchor (g : Outer 𝕜 o) : right g o = 1 := dif_pos rfl
@[fun_prop] lemma continuous_right (j : Fin q) : Continuous (fun g : Outer 𝕜 o => right g j) := by
  by_cases h : j = o <;> simp [right,h] <;> fun_prop

def middle (s : U 𝕜 2) (B : Fin 2 → U 𝕜 q) : Box 𝕜 q := fun i j => mix s (fun k => (B k).val i j)
def build (g : Outer 𝕜 o) (s : U 𝕜 2) (B : Fin 2 → U 𝕜 q) : Box 𝕜 q :=
  fun i j => (g.1 i).val * middle s B i j * (right g j).val
lemma build_mem (g : Outer 𝕜 o) (s : U 𝕜 2) (B : Fin 2 → U 𝕜 q) : build g s B ∈ Set.range eval := by
  refine ⟨(fun i => g.1 i*s⁻¹,B,fun j => s*right g j),?_⟩
  funext i j; simp only [eval,build,middle,mix,Submonoid.coe_mul,mul_assoc]; rfl
lemma build_cont : Continuous (fun p : Outer 𝕜 o × U 𝕜 2 × (Fin 2 → U 𝕜 q) => build p.1 p.2.1 p.2.2) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold build middle mix
  have hl : Continuous (fun p : Outer 𝕜 o × U 𝕜 2 × (Fin 2 → U 𝕜 q) => diagonal (fun k => (p.2.2 k).val i j)) :=
    (continuous_pi fun k => (continuous_entry i j).comp ((continuous_apply k).comp (continuous_snd.comp continuous_snd))).matrix_diagonal
  fun_prop

end
variable (Q : U 𝕜 q) (o : Fin q)
def rowD (p : Raw 𝕜 q) (i : Fin q) := diagU (fun k => row Q o (p.2.1 k) i)
def colD (p : Raw 𝕜 q) (j : Fin q) := diagU (fun k => col Q o (p.2.1 k) j)
def frames (p : Raw 𝕜 q) : Outer 𝕜 o :=
  (fun i => p.1 i * rowD Q o p i * p.2.2 o, fun j => (p.2.2 o)⁻¹ * colD Q o p j * p.2.2 j)
lemma right_frames (p : Raw 𝕜 q) (j) : right (frames Q o p) j = (p.2.2 o)⁻¹ * colD Q o p j * p.2.2 j := by
  by_cases h : j = o
  · subst j; have one : colD Q o p o = 1 := by apply Subtype.ext; simp [colD,diagU,diagonal_one]
    simp [one]
  · exact dif_neg h

lemma build_clean (p : Raw 𝕜 q) : build (frames Q o p) (p.2.2 o) (clean Q o ∘ p.2.1) = eval p := by
  funext i j
  have hd : diagonal (fun k => (clean Q o (p.2.1 k)).val i j) =
      (rowD Q o p i).valᴴ * diagonal (fun k => (p.2.1 k).val i j) * (colD Q o p j).valᴴ := by
    simp [rowD,colD,diagU,clean_entry]
  simp only [build,middle,mix,Function.comp_apply,hd,right_frames]
  change (p.1 i).val * _ * (p.2.2 o).val * ((p.2.2 o).valᴴ * _ * _) * ((p.2.2 o).valᴴ * _ * _) = _
  simp [eval,mul_assoc]

lemma mix_pos (c : 𝕜) {v : Fin 2 → 𝕜} (s : U 𝕜 2) (hv : ∀ k, 0 < v k / c) : (c⁻¹ • mix s v).PosDef := by
  have e : c⁻¹ • mix s v = mix s (c⁻¹ • v) := by simp [mix,diagonal_smul]
  rw [e]; exact (posDef_diagonal_iff.mpr (fun k => by simpa [div_eq_inv_mul] using hv k)).conjTranspose_mul_mul_same (mulVec_injective_of_isUnit Unitary.isUnit_coe)

lemma polar_right {u v : U 𝕜 2} {A B : Square 𝕜 2} (ha : A.PosDef) (hb : B.PosDef) (h : A*u.val = B*v.val) : u = v := by
  apply inv_injective
  apply polar ha hb
  simpa [conjTranspose_mul,ha.isHermitian.eq,hb.isHermitian.eq] using! congrArg conjTranspose h

lemma build_fibres {g h : Outer 𝕜 o} {s t : U 𝕜 2} {a b : Fin 2 → U 𝕜 q}
    (ha : ∀ k, Anchored Q o (a k)) (hb : ∀ k, Anchored Q o (b k)) :
    build g s a = build h t b ↔ g = h ∧ middle s a = middle t b := by
  refine ⟨fun eq => ?_,fun ⟨hg,hm⟩ => by funext i j; simp [build,hg,hm]⟩
  have H (i j) := congrFun (congrFun eq i) j
  simp only [build] at H
  have L : g.1 = h.1 := by
    funext i; apply polar (mix_pos _ s (fun k => (ha k).1 i)) (mix_pos _ t (fun k => (hb k).1 i))
    simpa [right_anchor,middle,mul_smul] using! congrArg ((Q.val i o)⁻¹ • ·) (H i o)
  have R : g.2 = h.2 := by
    funext j; apply polar_right (mix_pos _ s (fun k => (ha k).2 j.val)) (mix_pos _ t (fun k => (hb k).2 j.val))
    have e := H o j.val; rw [L,mul_assoc,mul_assoc] at e
    simpa [right,j.property,smul_mul,middle] using! congrArg ((Q.val o j.val)⁻¹ • ·) (Unitary.isUnit_coe.mul_left_cancel e)
  obtain rfl : g = h := Prod.ext L R
  exact ⟨rfl,funext fun i => funext fun j => Unitary.isUnit_coe.mul_left_cancel (Unitary.isUnit_coe.mul_right_cancel (H i j))⟩
end GS.Spectral
