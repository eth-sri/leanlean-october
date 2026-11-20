module
public import AlbertRecognition.JacobiBridge
public import AlbertRecognition.FixedFrame.CyclicPullback
public import Glennie.Diagonalization

/-! It suffices to recover the product *on* a diagonal plane, not on all
Peirce spaces. Jacobi forces each centred idempotent to be an eigenvector
of its own multiplication. Symmetry couples the three eigenvalues. -/
@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie FixedFrame
set_option maxHeartbeats 2000000

private theorem square_zero_slot (x : V) (zero : ∀ a, frameAction a x = 0) :
    ∃ r : ℝ, x = r • h 0 := by
  have hc (a) := (frameAction_coordinates a x).symm.trans (congrArg Subtype.val (zero a))
  have u := congrArg Albert.d1 (hc (x:Albert).o12)
  have v := congrArg Albert.o01 (hc (octScalar 1))
  have w := congrArg Albert.o02 (hc (octScalar 1))
  have t := congrArg (fun z : Albert => z.o12.1.re) (hc (octScalar 1))
  norm_num [smul_eq_zero, octNormSq_eq_zero] at u v w
  norm_num [octScalar] at t
  have tr := trace_V x
  change (x:Albert).d0 + (x:Albert).d1 + (x:Albert).d2 = 0 at tr
  refine ⟨(x:Albert).d1, Subtype.ext ?_⟩
  change (x:Albert) = (x:Albert).d1 • ((h 0):Albert)
  apply Albert.ext <;> simp [h, e, *] <;> linarith

private theorem self_on_slot {B : SymmetricCubic} (hq : q B = q referenceCubic) (i : Fin 3) :
    ∃ r : ℝ, B.K (h i) (h i) = r • h i := by
  obtain ⟨g,hi⟩ := move_h i
  rw [←hi]
  obtain ⟨r,hr⟩ := square_zero_slot _ (frame_zero _ (q_pullback hq g))
  exact ⟨r,by simpa only [pull_K,map_smul] using congrArg (automorphismV g) hr⟩

private theorem gram_h (i j : Fin 3) : gA (h i) (h j) = if i = j then 2 else -1 := by
  fin_cases i <;> fin_cases j <;> norm_num [gA,inner_coordinates,h,e,unit,octNormSq]

private abbrev Table (B : SymmetricCubic) (s : ℝ) :=
   B.K (h 0) (h 0) = -s • h 0 ∧ B.K (h 1) (h 1) = -s • h 1 ∧
    B.K (h 0) (h 1) = s • (h 0 + h 1)

private theorem on_plane {B : SymmetricCubic} (hq : q B = q referenceCubic) : ∃ s : ℝ, Table B s := by
  obtain ⟨a,ha⟩ := self_on_slot hq 0
  obtain ⟨b,hb⟩ := self_on_slot hq 1
  obtain ⟨c,hc⟩ := self_on_slot hq 2
  have h2 : h 2 = -(h 0 + h 1) := eq_neg_of_add_eq_zero_right h_sum_zero
  rw [h2] at hc
  simp only [map_neg, map_add, LinearMap.neg_apply, LinearMap.add_apply,
    B.comm (h 1) (h 0), ha, hb] at hc
  let v := B.K (h 0) (h 1)
  have hv : (2:ℝ) • v = (-c-a) • h 0 + (-c-b) • h 1 := by
    change (2:ℝ) • (B.K (h 0) (h 1)) = _; linear_combination (norm := module) hc
  have va : gA v (h 0) = -a := by
    rw [B.symm, ha, gA_smul_left, gram_h]; norm_num
  have vb : gA v (h 1) = -b := by
    dsimp only [v]; rw [B.comm (h 0) (h 1),B.symm,hb, gA_smul_left, gram_h]; norm_num
  have e0 := congrArg (fun x => gA x (h 0)) hv
  have e1 := congrArg (fun x => gA x (h 1)) hv
  norm_num [gA_add_left, gA_smul_left, gram_h, va, vb] at e0 e1
  have ba : b = a := by linarith
  have ca : c = a := by linarith
  subst b; subst c
  refine ⟨-a, by simpa using ha, by simpa using hb, ?_⟩
  change v = _
  linear_combination (norm := module) (1/2:ℝ) • hv
private theorem q_plane {B : SymmetricCubic} {s : ℝ} (ht : Table B s) :
    q B (h 0) (h 1) (h 0) = s^2 • (h 0 + 2 • h 1) := by
  simp only [q_apply, B.comm (h 1) (h 0), ht.1, ht.2.2, map_smul, map_add]
  module

private theorem eval_plane {B : SymmetricCubic} {s : ℝ} (ht : Table B s) (u v : ℝ) :
    let x := u • h 0 + v • h 1
    B.form x x x = s * gA ((-u^2) • h 0 + (-v^2) • h 1 + (2*u*v) • (h 0 + h 1)) x := by
  intro x; change gA (B.K x x) x = _; rw [← gA_smul_left]; congr 1
  dsimp only [x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, B.comm (h 1) (h 0), ht.1, ht.2.1, ht.2.2]
  module

private theorem diagonal_sign {B C : SymmetricCubic} (hb : q B = q referenceCubic)
    (hc : q C = q referenceCubic) {x : V} (hx : IsDiagonal x) :
    B.form x x x = C.form x x x ∨ B.form x x x = - C.form x x x := by
  obtain ⟨s,hs⟩ := on_plane hb
  obtain ⟨t,ht⟩ := on_plane hc
  have eq := congrArg (fun Q : V → V → Module.End ℝ V => gA (Q (h 0) (h 1) (h 0)) (h 1))
    (hb.trans hc.symm)
  simp only [q_plane hs, q_plane ht, gA_smul_left] at eq
  have ne : gA (h 0 + 2 • h 1) (h 1) ≠ 0 := by
    norm_num [two_smul,gA_add_left,gram_h]
  have rel := sq_eq_sq_iff_eq_or_eq_neg.mp (mul_right_cancel₀ ne eq)
  obtain ⟨u,v,hx⟩ : ∃ u v : ℝ, x = u • h 0 + v • h 1 := by
    obtain ⟨i,j,k⟩ := hx
    refine ⟨((x:Albert).d2-(x:Albert).d0)/3, ((x:Albert).d2-(x:Albert).d1)/3, Subtype.ext ?_⟩
    have tr := trace_V x
    change (x:Albert).d0+(x:Albert).d1+(x:Albert).d2=0 at tr
    apply Albert.ext <;> simp [h,e,i,j,k] <;> linarith
  rw [hx, eval_plane hs, eval_plane ht]; rcases rel with h | h <;> simp [h]

theorem point_sign {B : SymmetricCubic} (hq : q B = q referenceCubic) (x : V) :
    B.form x x x = referenceCubic.form x x x ∨ B.form x x x = -referenceCubic.form x x x := by
  obtain ⟨g,hg⟩ := native_diagonalization x
  let y := automorphismV g x
  have inv : automorphismV g.symm y = x := Subtype.ext (g.equiv.symm_apply_apply _)
  have H := diagonal_sign (q_pullback hq g.symm) (q_pullback (B := referenceCubic) rfl g.symm) (x := y) hg
  simpa only [pull_form,inv] using H

end
end AlbertRecognition
