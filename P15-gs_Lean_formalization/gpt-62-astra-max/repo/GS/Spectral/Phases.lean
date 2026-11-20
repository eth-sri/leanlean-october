module
public import GS.Spectral.Blocks
@[expose] public section

/-! Dephase each middle matrix by two diagonal unitaries. The column gauge
at the distinguished index is always one. -/
noncomputable section
open Matrix GS.Isometric
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace GS.Spectral
variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}
abbrev Phase (𝕜 : Type*) [RCLike 𝕜] := unitary 𝕜

def phase (z : 𝕜) : Phase 𝕜 := if h : z = 0 then 1 else
  ⟨z/(‖z‖ : 𝕜), by
    have eq : ‖z/(‖z‖ : 𝕜)‖ = 1 := by simp [h]
    simpa only [Unitary.mem_iff, RCLike.star_def,RCLike.conj_mul,RCLike.mul_conj,eq,map_one,one_pow,and_self]⟩
lemma phase_abs (z : 𝕜) : star (phase z).val * z = (‖z‖ : 𝕜) := by
  by_cases h : z = 0 <;> simp [phase,h,RCLike.star_def,div_mul_eq_mul_div,RCLike.conj_mul,pow_two]
lemma continuousAt_phase {z : 𝕜} (h : z ≠ 0) : ContinuousAt phase z := by
  apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
  apply (continuousAt_id.div (RCLike.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt) (by simpa using h)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds h] with w hw; simp [phase,hw]

def diagU {n : ℕ} (a : Fin n → Phase 𝕜) : U 𝕜 n := ⟨diagonal (fun i => (a i).val), IsU.of_left (by
  simpa using congrArg diagonal (funext fun i => (a i).property.1))⟩
@[fun_prop] lemma continuous_diagU (n : ℕ) : Continuous (@diagU 𝕜 _ n) :=
  ((continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).matrix_diagonal).subtype_mk _

variable (Q : U 𝕜 q) (o : Fin q)
def Anchored (A : U 𝕜 q) := (∀ i, 0 < A.val i o / Q.val i o) ∧ ∀ j, 0 < A.val o j / Q.val o j
def Good (A : U 𝕜 q) := (∀ i, A.val i o / Q.val i o ≠ 0) ∧ ∀ j, A.val o j / Q.val o j ≠ 0
abbrev Slice := {A : U 𝕜 q // Anchored Q o A}

def row (A : U 𝕜 q) (i : Fin q) := phase (A.val i o / Q.val i o)
def col (A : U 𝕜 q) (j : Fin q) := (row Q o A o)⁻¹ * phase (A.val o j / Q.val o j)
@[simp] lemma col_anchor (A : U 𝕜 q) : col Q o A o = 1 := inv_mul_cancel _
def clean (A : U 𝕜 q) : U 𝕜 q := (diagU (row Q o A))⁻¹ * A * (diagU (col Q o A))⁻¹

lemma clean_entry (A : U 𝕜 q) (i j) : (clean Q o A).val i j =
    star (row Q o A i).val * A.val i j * star (col Q o A j).val := by
  change ((diagonal (fun i => (row Q o A i).val))ᴴ * A.val * (diagonal (fun j => (col Q o A j).val))ᴴ) i j = _
  simp [mul_diagonal,diagonal_mul]

lemma clean_anchored {A : U 𝕜 q} (h : Good Q o A) : Anchored Q o (clean Q o A) := by
  constructor <;> intro i <;> rw [clean_entry]
  · simp only [col_anchor,OneMemClass.coe_one,star_one,mul_one,mul_div_assoc,row,phase_abs]; exact RCLike.ofReal_pos.mpr (norm_pos_iff.mpr (h.1 i))
  · let a := row Q o A o; let b := phase (A.val o i / Q.val o i)
    change 0 < star a.val * _ * star (star a.val * b.val) / _
    rw [star_mul,star_star]; have ha := a.property.1
    rw [show star a.val * A.val o i * (star b.val * a.val) / Q.val o i = (star a.val*a.val)*(star b.val*(A.val o i/Q.val o i)) by ring,ha,one_mul,phase_abs]
    exact RCLike.ofReal_pos.mpr (norm_pos_iff.mpr (h.2 i))

@[fun_prop] lemma continuous_entry (i j : Fin q) : Continuous (fun A : U 𝕜 q => A.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

lemma good_open : IsOpen {A : U 𝕜 q | Good Q o A} := by
  have ho (a b : Fin q) : IsOpen {A : U 𝕜 q | A.val a b / Q.val a b ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  simp only [Good,Set.setOf_and,Set.setOf_forall]
  exact (isOpen_iInter_of_finite fun i => ho i o).inter (isOpen_iInter_of_finite fun j => ho o j)
lemma clean_continuousAt {A : U 𝕜 q} (h : Good Q o A) : ContinuousAt (clean Q o) A := by
  have hp (i j : Fin q) (hne : A.val i j / Q.val i j ≠ 0) : ContinuousAt (fun B : U 𝕜 q => phase (B.val i j / Q.val i j)) A :=
    (continuousAt_phase hne).comp (f := fun B : U 𝕜 q => B.val i j / Q.val i j) (((continuous_entry i j).div_const _).continuousAt)
  have hr : ContinuousAt (row Q o) A := continuousAt_pi.mpr fun i => hp i o (h.1 i)
  have hc : ContinuousAt (col Q o) A := continuousAt_pi.mpr fun j => (hp o o (h.1 o)).inv.mul (hp o j (h.2 j))
  exact (((continuous_diagU q).continuousAt.comp hr).inv.mul continuousAt_id).mul (((continuous_diagU q).continuousAt.comp hc).inv)
end GS.Spectral
