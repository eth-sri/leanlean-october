/- Universal Jacobi bridge for an unrestricted symmetric cubic.
The wedge cancellation is derived from the actual metric-raised KB, and the
concrete frame step uses native reference vanishing identities.  This is an
algebraic prerequisite, not the log-Hessian/Levi-Civita recognition endpoint. -/
module

public import AlbertRecognition.FixedFrame.ReferenceBlocks

@[expose] public section
namespace AlbertRecognition
noncomputable section

/-- The cubic symmetry cancels the wedges; the three remaining differences
are Jacobi for commutators of endomorphisms. -/
private theorem jacobi (B : SymmetricCubic) (hq : q B = q referenceCubic) (x y z v : V) :
    (B.K x (D y z v) - D y z (B.K x v)) + (B.K y (D z x v) - D z x (B.K y v)) +
    (B.K z (D x y v) - D x y (B.K z v)) = 0 := by
  have w (a b c : V) : wedge a b c = gA b c • a - gA a c • b := rfl
  have sa (a b c : V) : gA a (B.K b c) = gA (B.K a b) c := by rw [gA_comm,B.symm,B.comm b a]
  simp only [D,LinearMap.add_apply,←hq,q_apply,w,map_add,map_sub,map_smul,sa,B.comm]
  abel

open FixedFrame in
theorem frame_zero (B : SymmetricCubic) (hq : q B = q referenceCubic) (a : Glennie.Octonion) :
    frameAction a (B.K (h 0) (h 0)) = 0 := by
  change D (h 1) (X12 a) _ = 0
  simpa only [D_X12_h0_zero,D_h0_h1_zero,show D (h 1) (X12 a) (h 0) = 0 from frameAction_h0 a,LinearMap.zero_apply,map_zero,sub_self,zero_sub,add_zero,neg_eq_zero] using jacobi B hq (h 0) (h 1) (X12 a) (h 0)
end
end AlbertRecognition
