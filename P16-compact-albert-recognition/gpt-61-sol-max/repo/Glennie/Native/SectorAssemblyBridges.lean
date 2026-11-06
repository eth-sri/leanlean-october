/- Small assembly bridges from actual native sector APIs.
No tracelessness, invertibility, scalar factor, covariance or endpoint premise. -/
module
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop
public import Glennie.Native.SectorAction
public import Glennie.Native.SectorArgumentAction
public import Glennie.Theorems.SectorContraction

@[expose] public section
namespace Glennie.SectorAssemblyBridges
noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

                                                                           
                                                                                 
                                                                       
                                                               

/- The two literal definitions differ only by commutative scalar order. -/

/- The actual native product supplies the pure-complex argument for U_z. -/






/- Native Hermitian adjugates give the forward anti-Hermitian commutator. -/
theorem adjugate_commutator_antiHermitian (D H : Mat)
    (hD : D.IsHermitian) (hH : H.IsHermitian) :
    (H.adjugate * D.adjugate - D.adjugate * H.adjugate).conjTranspose =
      -(H.adjugate * D.adjugate - D.adjugate * H.adjugate) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    hH.adjugate.eq, hD.adjugate.eq, neg_sub]


/- Cyclic trace, rather than product Hermiticity, proves this scalar is real. -/
theorem trace_mul_im_zero (K B : Mat)
    (hK : K.IsHermitian) (hB : B.IsHermitian) : (K*B).trace.im = 0 := by
  have hs : star (K*B).trace = (K*B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hK.eq]
    exact Matrix.trace_mul_comm B K
  have hi : -(K*B).trace.im = (K*B).trace.im := congrArg Complex.im hs
  linarith

theorem hidden_gram_isHermitian (M : Mat) :
    (M.conjTranspose*M).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self M

/- Pure-complex cancellation for arbitrary matrices, retaining all traces.
The only nontrivial scalar cancellation is the existing cyclic-trace lemma. -/
theorem pure_complex_trace (D H K : Mat) :
    ((D*H*K*H*D-H*D*K*D*H) *
      (K*((1/2:ℂ) • (D*H+H*D))*K)).trace = 0 := by
  let A := D*H*K
  let B := H*D*K
  calc
    _ = ((1/2:ℂ) • ((A*B-B*A)*(A+B))).trace := by
      congr 1
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      dsimp [A, B]
      noncomm_ring
    _ = 0 := by rw [Matrix.trace_smul, SectorContraction.trace_comm_mul_sum]; simp

end
end Glennie.SectorAssemblyBridges
