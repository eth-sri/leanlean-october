module
public import GS.Isometric.Directions
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
@[expose] public section

/-! The same normalized Cayley coordinates serve as a chart on each group and
as a global parametrization of the step. Their true orbit differential is the
spatial generator map. Its kernel exponentiates by Cayley into the stabilizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {r l s : Layer 𝕜 n}
local notation "A" => Square 𝕜 n
local notation "V" => PairGenerator r l

def frame (v : Generator s) : Factor s := Factor.ofMatrix (unitCayley v.val)
  (cayley_shared ((skewSpace s).smul_mem (-1/2:ℝ) v.property))
@[simp] lemma frame_zero : frame (0 : Generator s) = 1 := Factor.matrix_injective unitCayley_zero
@[fun_prop] lemma frame_smooth : ContDiff ℝ ⊤ (fun v : Generator s => (frame v).matrix) :=
  unitCayley_smooth_comp _ (skewSpace s).subtypeL.contDiff fun v => v.property.2
@[fun_prop] lemma frame_continuous : Continuous (frame : Generator s → _) :=
  ((frame_smooth (s := s)).continuous.subtype_mk _).subtype_mk _

def retractGen (s : Layer 𝕜 n) := (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
  (f := (skewSpace s).subtypeL) Subtype.val_injective).leftInverse
lemma retractGen_val (v : Generator s) : retractGen s v.val = v :=
  ContinuousLinearMap.HasLeftInverse.leftInverse_leftInverse _ v

def coord (s : Layer 𝕜 n) (X : A) := (-2 : ℝ) • retractGen s (cayley X)
lemma coord_smooth {X : A} (h : admissible X) : ContDiffAt ℝ ⊤ (coord s) X :=
  (((retractGen s).contDiff.contDiffAt.comp X (smooth_cayley_at X h)).const_smul _)
@[simp] lemma coord_frame (v : Generator s) : coord s (frame v).matrix = v := by
  let w := (-1/2:ℝ) • v
  change (-2:ℝ) • retractGen s (cayley (cayley w.val)) = v
  rw [cayley_involutive _ (admissible_of_isSkew _ w.property.2),retractGen_val,smul_smul]; norm_num

/-- A chart at the identity is all that the local product argument needs. -/
def frameChart (s : Layer 𝕜 n) : OpenPartialHomeomorph (Generator s) (Factor s) where
  toFun := frame
  invFun U := coord s U.matrix
  source := univ
  target := {U | admissible U.matrix}
  map_source' v _ := admissible_cayley _ (admissible_of_isSkew _ (skew_smul _ v.property.2))
  map_target' _ _ := trivial
  left_inv' v _ := coord_frame v
  right_inv' U h := by
    let v : Generator s := ⟨_,cayley_sharedSkew U.matrix_shared h⟩
    apply Factor.matrix_injective
    change cayley ((-1/2:ℝ) • ((-2:ℝ) • retractGen s v.val).val) = U.matrix
    rw [retractGen_val,Submodule.coe_smul,smul_smul]; norm_num [v,cayley_involutive _ h]
  open_source := isOpen_univ
  open_target := admissible_open.preimage Factor.continuous_matrix
  continuousOn_toFun := frame_continuous.continuousOn
  continuousOn_invFun := fun U h => ((coord_smooth h).continuousAt.comp Factor.continuous_matrix.continuousAt).continuousWithinAt

def pairChart (r l : Layer 𝕜 n) := (frameChart l).prod (frameChart r)
abbrev frames (v : V) : Factors r l := (frame v.1,frame v.2)
@[simp] lemma frames_zero : frames (0 : V) = 1 := Prod.ext frame_zero frame_zero

def move (r l : Layer 𝕜 n) (p : A × PairGenerator r l) := frames p.2 • p.1
lemma move_smooth : ContDiff ℝ ⊤ (move r l) := by
  apply contDiff_iff_contDiffAt.mpr; intro p
  exact smooth_mul_at (smooth_mul_at (frame_smooth.contDiffAt.comp p contDiffAt_snd.fst) contDiffAt_fst)
    (smooth_conjTranspose_at (frame_smooth.contDiffAt.comp p contDiffAt_snd.snd))
lemma move_line (X : A) (v : V) : HasDerivAt (fun t : ℝ => frames (t • v) • X) (pointMap r l X v) 0 := by
  simpa [pointMap,sub_eq_add_neg,v.2.property.2] using! hasDerivAt_product2 X
    (unitCayley_line_derivative v.1.val) (hasDerivAt_matrix_conjTranspose (unitCayley_line_derivative v.2.val))
lemma deriv_on_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : DifferentiableAt ℝ f 0) {v : E} {w : F} (h : HasDerivAt (fun t : ℝ => f (t • v)) w 0) :
    fderiv ℝ f 0 v = w := by
  simpa using (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id (0:ℝ)).smul_const v) (by simp)).unique h
lemma move_deriv (X : A) : HasFDerivAt (fun v : V => frames v • X) (pointMap r l X).toContinuousLinearMap 0 := by
  have hs : ContDiff ℝ ⊤ (fun v : V => frames v • X) := (move_smooth (r := r) (l := l)).comp (f := fun v : V => (X,v)) (contDiff_const.prodMk contDiff_id)
  have d := (hs.differentiable (by simp) 0).hasFDerivAt
  suffices (pointMap r l X).toContinuousLinearMap = fderiv ℝ (fun v : V => frames v • X) 0 by rwa [this]
  exact ContinuousLinearMap.ext fun v => (deriv_on_line (hs.differentiable (by simp) 0) (move_line X v)).symm
lemma stabilizes (X : A) (v : V) (h : pointMap r l X v = 0) : frames v • X = X := by
  have eq := sub_eq_zero.mp h
  have t := cayley_intertwine _ _ X (admissible_of_isSkew _ (skew_smul (-1/2:ℝ) v.1.property.2))
    (admissible_of_isSkew _ (skew_smul (-1/2:ℝ) v.2.property.2)) (by simp [eq])
  change unitCayley v.1.val * X * (unitCayley v.2.val)ᴴ = X
  rw [show unitCayley v.1.val * X = X * unitCayley v.2.val from t,mul_assoc,show unitCayley v.2.val * (unitCayley v.2.val)ᴴ = 1 from (frame v.2).matrix_unitary.2,mul_one]
end GS.Isometric
