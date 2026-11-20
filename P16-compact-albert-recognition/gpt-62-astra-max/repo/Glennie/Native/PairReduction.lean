module
public import Glennie.Diagonalization
public import Glennie.Native.Triality
public import Mathlib.Analysis.Quaternion

/-! Quaternionic elimination in the three triality slots. Left and right
unit-quaternion factors and two signed basis changes suffice. No roots in the
octonions, nor a transitivity theorem for Spin(8) or G₂, are required. -/
@[expose] public section
namespace Glennie
noncomputable section
open OctRelatedTriple
private abbrev H := Quaternion ℝ
private abbrev Q := unitary H
private def L (p : Q) := (Unitary.toUnits p).mulLeftLinearEquiv ℝ H
private def R (p : Q) := (Unitary.toUnits p).mulRightLinearEquiv ℝ
private theorem nQ (p : Q) : Quaternion.normSq (p:H) = 1 := by
  simpa only [Quaternion.star_mul_self, Quaternion.re_coe, Quaternion.re_one] using congrArg QuaternionAlgebra.re p.property.1

private def spin (p t s : Q) : OctRelatedTriple where
  A := (L p).prodCongr ((L s).trans (R t))
  B := (R t).prodCongr ((L s).trans (R (star p)))
  C := ((L p).trans (R t)).prodCongr (L s)
  norm_A x := by change Quaternion.normSq ((p:H)*_) + Quaternion.normSq ((s:H)*_*(t:H)) = _; simp [octNormSq,nQ]
  norm_B x := by change Quaternion.normSq (_*(t:H)) + Quaternion.normSq ((s:H)*_*star (p:H)) = _; simp [octNormSq,nQ]
  norm_C x := by change Quaternion.normSq ((p:H)*_*(t:H)) + Quaternion.normSq ((s:H)*_) = _; simp [octNormSq,nQ]
  product x y := by
    have ls (z : H) : star (s:H)*((s:H)*z) = z := by rw [← mul_assoc,s.property.1,one_mul]
    have lp (z : H) : star (p:H)*((p:H)*z) = z := by rw [← mul_assoc,p.property.1,one_mul]
    have rt (z : H) : (t:H)*(star (t:H)*z) = z := by rw [← mul_assoc,t.property.2,one_mul]
    change octMul ((p:H)*x.1,(s:H)*x.2*(t:H)) (y.1*(t:H),(s:H)*y.2*star (p:H)) = ((p:H)*(octMul x y).1*(t:H),(s:H)*(octMul x y).2)
    simp [octMul, mul_assoc,mul_sub,sub_mul,mul_add,ls,lp,rt]

/-- Rotate the three hidden complex coordinate pairs, fixing the standard i. -/
private def cycle (x : Octonion) : Octonion :=
  (⟨x.1.re,x.1.imI,x.2.imJ,-x.2.imK⟩,⟨x.1.imJ,x.1.imK,x.2.re,-x.2.imI⟩)
/-- Change quaternion chart so i becomes the real coordinate of the second quaternion. -/
private def tilt (x : Octonion) : Octonion :=
  (⟨x.1.re,x.2.re,x.1.imK,-x.2.imK⟩,⟨x.1.imI,-x.2.imI,x.1.imJ,x.2.imJ⟩)
private def untilt (x : Octonion) : Octonion :=
  (⟨x.1.re,x.2.re,x.2.imJ,x.1.imJ⟩,⟨x.1.imI,-x.2.imI,x.2.imK,-x.1.imK⟩)
local macro "coords" : tactic => `(tactic| (try ext) <;> simp [Function.comp_apply,cycle,tilt,untilt,octNormSq,Quaternion.normSq_def',octMul,
  Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring)
private def diagonal (e : Octonion ≃ₗ[ℝ] Octonion) (n : ∀ x, octNormSq (e x) = octNormSq x)
    (h : ∀ x y, octMul (e x) (e y) = e (octMul x y)) : OctRelatedTriple := ⟨e,e,e,n,n,n,h⟩
private def P : OctRelatedTriple := diagonal
  {toFun := cycle, invFun := cycle ∘ cycle, left_inv := by intro; coords, right_inv := by intro; coords,
   map_add' := by intros; coords, map_smul' := by intros; coords} (by intro; coords) (by intros; coords)
private def T : OctRelatedTriple := diagonal
  {toFun := tilt, invFun := untilt, left_inv := by intro; coords, right_inv := by intro; coords,
   map_add' := by intros; coords, map_smul' := by intros; coords} (by intro; coords) (by intros; coords)
private def Ti : OctRelatedTriple := diagonal T.A.symm
  (fun x => by simpa using (T.norm_A (T.A.symm x)).symm)
  (fun x y => T.A.injective (by rw [LinearEquiv.apply_symm_apply]; change T.C (octMul _ _) = _; rw [← T.product]; exact congrArg₂ octMul (T.A.apply_symm_apply x) (T.A.apply_symm_apply y)))

private theorem rotate (x : H) : ∃ (p : Q) (r : ℝ), 0 ≤ r ∧ (p:H)*x = r ∧ x*(p:H) = r := by
  by_cases h : x = 0
  · exact ⟨1,0,le_rfl,by simp [h],by simp [h]⟩
  let q := ‖x‖⁻¹ • star x
  have n : Quaternion.normSq q = 1 := by simp [q, Quaternion.normSq_smul,Quaternion.normSq_eq_norm_mul_self, norm_ne_zero_iff.mpr h]; field_simp
  have nq : q ∈ unitary H := ⟨by simp [Quaternion.star_mul_self,n],by simp [Quaternion.self_mul_star,n]⟩
  refine ⟨⟨q,nq⟩,‖x‖,norm_nonneg _,?_,?_⟩ <;> change _ = (‖x‖:H)
  · change q * x = _; dsimp only [q]; rw [smul_mul_assoc,Quaternion.star_mul_self,Quaternion.normSq_eq_norm_mul_self]; ext <;> simp [norm_ne_zero_iff.mpr h]
  · change x * q = _; dsimp only [q]; rw [mul_smul_comm,Quaternion.self_mul_star,Quaternion.normSq_eq_norm_mul_self]; ext <;> simp [norm_ne_zero_iff.mpr h]

private def act (k : Fin 3) (g : OctRelatedTriple) := ![g.A,g.B,g.C] k
private theorem act_comp (k) (g h : OctRelatedTriple) (x) : act k (g.comp h) x = act k g (act k h x) := by fin_cases k <;> rfl
private def prior (k : Fin 3) (g : OctRelatedTriple) := ∀ j < k, ∀ r, act j g (octScalar r) = octScalar r
private def pass (k : Fin 3) (r : ℝ) (x : Octonion) := cycle (if k = 2 then untilt ((tilt x).1,(r:H)) else ((r:H),x.2))
private theorem step (k : Fin 3) (x : Octonion) : ∃ g r, prior k g ∧ 0 ≤ r ∧ act k g x = pass k r x := by
  fin_cases k
  · obtain ⟨p,r,hr,he,_⟩ := rotate x.1
    refine ⟨P.comp (spin p 1 1),r,fun j hj => by change j < 0 at hj; exact (Fin.not_lt_zero j hj).elim,hr,?_⟩
    change cycle ((p:H)*x.1,(1:H)*x.2*1) = _; simp [he,pass]
  · obtain ⟨p,r,hr,_,he⟩ := rotate x.1
    refine ⟨P.comp (spin 1 p 1),r,?_,hr,?_⟩
    · intro j h r; change j < 1 at h; have : j = 0 := by omega
      subst j; change cycle ((1:H)*(r:H),(1:H)*0*(p:H)) = _; ext <;> simp [cycle,octScalar]
    change cycle (x.1*(p:H),(1:H)*x.2*star 1) = _; simp [he,pass]
  · obtain ⟨p,r,hr,he,_⟩ := rotate (tilt x).2
    refine ⟨P.comp (Ti.comp ((spin 1 1 p).comp T)),r,?_,hr,?_⟩
    · intro j h r; fin_cases j
      · change cycle (untilt ((1:H)*(tilt (octScalar r)).1,(p:H)*(tilt (octScalar r)).2*1)) = _; ext <;> simp [cycle,tilt,untilt,octScalar]
      · change cycle (untilt ((tilt (octScalar r)).1*(1:H),(p:H)*(tilt (octScalar r)).2*star 1)) = _; ext <;> simp [cycle,tilt,untilt,octScalar]
      · exact ((by decide : ¬(2:Fin 3)<2) h).elim
    change cycle (untilt ((1:H)*(tilt x).1*1,(p:H)*(tilt x).2)) = _; simp [he,pass]

private def normal (k : Fin 3) (r : ℝ) (x : Octonion) : Octonion :=
  if k = 2 then (⟨x.1.re,r,0,0⟩,0) else octScalar r
private theorem sweep (k : Fin 3) (x : Octonion) : ∃ g r, prior k g ∧ 0 ≤ r ∧ act k g x = normal k r x := by
  obtain ⟨a,u,ha,_,h1⟩ := step k x
  obtain ⟨b,v,hb,_,h2⟩ := step k (pass k u x)
  obtain ⟨c,r,hc,hr,h3⟩ := step k (pass k v (pass k u x))
  refine ⟨c.comp (b.comp a),r,fun j h r => by simp only [act_comp,ha j h,hb j h,hc j h],hr,?_⟩
  rw [act_comp,act_comp,h1,h2,h3]; fin_cases k <;> ext <;> simp [pass,normal,cycle,untilt,tilt,octScalar]

/-- Any actual related-triple Albert map preserves the entire diagonal subspace. -/
theorem relatedTriple_isDiagonal (g : OctRelatedTriple) (x : Albert)
    (hx : IsDiagonal x) : IsDiagonal (g.compactAutomorphism.equiv x) := by
  change g.A x.o01 = 0 ∧ g.C x.o02 = 0 ∧ g.B x.o12 = 0
  simp [hx.1, hx.2.1, hx.2.2, and_self]

/-- Normalize the three octonion slots without moving the diagonal. Choose the
positive imaginary ray in the remaining complex slot. -/
theorem positive_slots (y : Albert) : ∃ t : OctRelatedTriple, ∃ a b : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧ t.A y.o01 = octScalar a ∧ t.B y.o12 = octScalar b ∧
    InComplexSector (t.compactAutomorphism.equiv y) ∧ 0 ≤ (t.C y.o02).1.imI := by
  obtain ⟨f,a,_,ha,hu⟩ := sweep 0 y.o01
  obtain ⟨g,b,hg,hb,hw⟩ := sweep 1 (f.B y.o12)
  obtain ⟨h,r,hh,hr,hv⟩ := sweep 2 (g.C (f.C y.o02))
  let t := h.comp (g.comp f)
  change f.A y.o01 = octScalar a at hu
  change g.B (f.B y.o12) = octScalar b at hw
  have u : t.A y.o01 = octScalar a := by
    change h.A (g.A (f.A _)) = _; rw [hu,show g.A _ = octScalar a from hg 0 (by decide) a]; exact hh 0 (by decide) a
  have w : t.B y.o12 = octScalar b := by
    change h.B (g.B (f.B _)) = _; rw [hw]; exact hh 1 (by decide) b
  have v : t.C y.o02 = (⟨_,r,0,0⟩,0) := hv
  refine ⟨t,a,b,ha,hb,u,w,?_,?_⟩
  · change OctInComplex (t.A _) ∧ OctInComplex (t.C _) ∧ OctInComplex (t.B _); simp [u,v,w,OctInComplex,octScalar]
  · rw [v]; exact hr

theorem universal_pair_reduction : UniversalPairReduction := by
  intro x y
  obtain ⟨g,hg⟩ := native_diagonalization x
  obtain ⟨t,_,_,_,_,_,_,ht,_⟩ := positive_slots (g.equiv y)
  exact ⟨t.compactAutomorphism.comp g, relatedTriple_isDiagonal t _ hg,ht⟩

end
end Glennie
