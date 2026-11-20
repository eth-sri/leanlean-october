module
public import Glennie.Compact.Flows
public import Glennie.Compact.ExactCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
@[expose] public section
namespace Glennie.Compact.FlowFamily
noncomputable section
open Flows NormedSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
abbrev Param := Fin 20 → ℝ
abbrev Frames3 := Fin 3 → Fin 3 → Albert

/-- The twenty selected ordered triple-ledger rows. -/
def rowIndex (i : Fin 20) : Fin 3 × Fin 3 × Fin 3 :=
  #v[(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (0,1,2),
    (0,2,0), (0,2,1), (1,0,0), (1,0,1), (1,0,2), (1,1,0),
    (1,1,1), (1,1,2), (1,2,0), (1,2,1), (2,0,0), (2,0,1),
    (2,1,0), (2,1,1)][i]

/-- Directions of the minor: commute a fixed traceless diagonal multiplication
with one off-diagonal coordinate multiplication, in the indicated frame. -/
def partnerIndex (i : Fin 20) : Fin 24 :=
  #v[0,1,8,9,18,19,10,11,2,3,20,21,12,13,4,5,10,11,2,3][i]
def contextIndex (i : Fin 20) : Fin 3 := if i.val < 16 then 0 else 1

def axis {R : Type*} [CommRing R] : Exact.A R := (1,-1,0,0,0,0)
def partner {R : Type*} [CommRing R] (i : Fin 20) : Exact.A R :=
  let v (k : ℕ) : R := if (partnerIndex i).val = k then 1 else 0
  let c (k : ℕ) : Quaternion R := ⟨v k,v (k+1),v (k+2),v (k+3)⟩
  (0,0,0,(c 0,c 4),(c 8,c 12),(c 16,c 20))

def direction (n : Fin 20) := innerDerLinear (Exact.realize (RingHom.id ℝ) axis) (Exact.realize (RingHom.id ℝ) (partner n))
def step (a : Fin 3) (n : Fin 20) := if a = contextIndex n then direction n else 0
def atomTangent (T : Frames3) (n : Fin 20) (a i : Fin 3) := step a n (T a i)
/-- The literal scalar `jacobianEntry`, with its `let`s inlined. -/
def jacobianEntry (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) : ℝ :=
  trace (jordan (jordan (atomTangent T n 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (atomTangent T n 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (atomTangent T n 2 (rowIndex r).2.2))

/-- Generator in each frame, linear in the flow parameters. -/
def generator (a : Fin 3) : Param →L[ℝ] EndA := ∑ n : Fin 20,
  (ContinuousLinearMap.proj n : Param →L[ℝ] ℝ).smulRight (LinearMap.toContinuousLinearMap (step a n))

theorem generator_sum (a : Fin 3) (s : Param) : (generator a s).toLinearMap = ∑ n, s n • step a n := by
  ext1 x; simp [generator]

private theorem motion_aut (s : Param) (a : Fin 3) : ∃ g : CompactAutomorphism,
    ∀ x, g.equiv x = opExp (generator a s) x := by
  have j (n : Fin 20) : IsJordanDerivation (step a n) := by
    unfold step; split
    · unfold direction; apply isJordanDerivation_innerDerLinear
    · exact IsJordanDerivation.zero
  have t (n : Fin 20) : TraceFree (step a n) := by
    unfold step; split
    · unfold direction; apply traceFree_innerDerLinear
    · exact TraceFree.zero
  refine ⟨flowAut _ ?_ ?_,fun _ => rfl⟩ <;> rw [generator_sum]
  · exact IsJordanDerivation.sum _ _ fun n _ => (j n).smul _
  · exact TraceFree.sum _ _ fun n _ => (t n).smul _

def motion (T : Frames3) (s : Param) : Frames3 := fun a i => opExp (generator a s) (T a i)

theorem motion_zero (T : Frames3) : motion T 0 = T := by funext a i; simp [motion]
theorem motion_frame (T : Frames3) (ht : ∀ a, Frame (T a)) (s : Param) (a : Fin 3) : Frame (motion T s a) := by
  obtain ⟨g,h⟩ := motion_aut s a
  change Frame (fun i => opExp (generator a s) (T a i))
  simpa only [h] using g.map_frame _ (ht a)

theorem continuous_motion (T : Frames3) (a i : Fin 3) : Continuous fun s => motion T s a i :=
  (continuous_opExp.comp (generator a).continuous).clm_apply continuous_const

private theorem motion_deriv (T : Frames3) (a i : Fin 3) :
    HasStrictFDerivAt (fun s => motion T s a i) ((generator a).flip (T a i)) 0 := by
  have he : HasStrictFDerivAt (opExp : EndA → EndA) (1 : EndA →L[ℝ] EndA) (generator a 0) := by
    rw [map_zero]; exact deriv_opExp
  exact ((he.comp 0 (generator a).hasStrictFDerivAt).clm_apply (hasStrictFDerivAt_const (T a i) 0)).congr_fderiv (by simp; rfl)

def rowLedger (T : Frames3) (s : Param) : Param := fun r =>
  let (i,j,k) := rowIndex r; let U := motion T s; ledger (U 0) (U 1) (U 2) i j k

def rowLedgerDeriv (T : Frames3) : Param →L[ℝ] Param :=
  ContinuousLinearMap.pi fun r => fderiv ℝ (fun s => rowLedger T s r) 0

/-- Apply the product rule to the three slots. Reading a single standard
basis vector of the derivative selects exactly one commutator generator. -/
private theorem product_rule {X Y Z W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (j : Y →L[ℝ] Z →L[ℝ] W) {x : X}
    {f : X → Y} {g : X → Z} {u : X →L[ℝ] Y} {v : X →L[ℝ] Z}
    (hu : HasStrictFDerivAt f u x) (hv : HasStrictFDerivAt g v x) :
    HasStrictFDerivAt (fun s => j (f s) (g s)) ((j (f x)).comp v + (j.comp u).flip (g x)) x :=
  (j.hasStrictFDerivAt.comp x hu).clm_apply hv

private theorem row_deriv (T : Frames3) (r : Fin 20) : ∃ L : Param →L[ℝ] ℝ,
    HasStrictFDerivAt (fun s => rowLedger T s r) L 0 ∧ ∀ n, L (Pi.single n 1) = jacobianEntry T r n := by
  let i := (rowIndex r).1; let j := (rowIndex r).2.1; let k := (rowIndex r).2.2
  have h := product_rule nativeInnerContinuous
    (product_rule jordanContinuous (motion_deriv T 0 i) (motion_deriv T 1 j)) (motion_deriv T 2 k)
  refine ⟨_,h,?_⟩; intro n
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    motion_zero, jordanContinuous_apply, jacobianEntry, trace_add, atomTangent]
  have hin (x y : Albert) : nativeInnerContinuous x y = trace (jordan x y) := rfl
  simp [generator, hin, trace_add, i,j,k] <;> ring

theorem hasStrictFDerivAt_rowLedger (T : Frames3) : HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 := by
  apply hasStrictFDerivAt_pi.mpr; intro r
  obtain ⟨L,h,_⟩ := row_deriv T r; exact h.hasFDerivAt.fderiv ▸ h

theorem rowLedgerDeriv_single (T : Frames3) (r n : Fin 20) : rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n := by
  obtain ⟨L,h,e⟩ := row_deriv T r; simpa only [rowLedgerDeriv,ContinuousLinearMap.pi_apply,h.hasFDerivAt.fderiv] using e n

end
end Glennie.Compact.FlowFamily
