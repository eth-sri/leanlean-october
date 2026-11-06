/- Complete small real mixed-trace cancellation.
No coordinate polynomial expansion, missing cancellation premise, inverse,
spectral or norm reconstruction.
All native Hermitian premises are supplied by explicit proved source APIs. -/
module

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Aesop
public import Glennie.Native.SectorAssemblyBridges

@[expose] public section
namespace Glennie.SectorMixedTrace
noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/- Anti-Hermitian times Hermitian has purely imaginary trace, using cyclicity. -/
theorem antiHermitian_trace_re_zero (S G : Mat)
    (hS : S.conjTranspose = -S) (hG : G.IsHermitian) :
    (S*G).trace.re = 0 := by
  have hs : star (S*G).trace = -(S*G).trace := by
    calc
      _ = (S*G).conjTranspose.trace := (Matrix.trace_conjTranspose (S*G)).symm
      _ = -(G*S).trace := by
        simp only [Matrix.conjTranspose_mul, hG.eq, hS,
          Matrix.mul_neg, Matrix.trace_neg]
      _ = _ := by rw [Matrix.trace_mul_comm G S]
  have hr : (S*G).trace.re = -(S*G).trace.re := congrArg Complex.re hs
  linarith

/- Conjugation reverses every factor; the two-factor cyclic rotation retains
precisely the S*B*K order on the right, including its minus sign. -/
theorem star_trace_four (S G K B : Mat)
    (hS : S.conjTranspose = -S) (hG : G.IsHermitian)
    (hK : K.IsHermitian) (hB : B.IsHermitian) :
    star (S*G*K*B).trace = -(G*S*B*K).trace := by
  calc
    _ = (S*G*K*B).conjTranspose.trace :=
      (Matrix.trace_conjTranspose (S*G*K*B)).symm
    _ = -(B*K*G*S).trace := by
      simp only [Matrix.conjTranspose_mul, hB.eq, hK.eq, hG.eq, hS,
        Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_assoc]
    _ = _ := by
      simpa only [Matrix.mul_assoc] using
        congrArg (fun t : ℂ => -t) (Matrix.trace_mul_comm (B*K) (G*S))

/- The scalar t=tr(KB) is real by the explicit Hermitian trace bridge. Its
product with the purely imaginary tr(SG) contributes zero real part. -/
theorem hidden_real_trace (M S K B : Mat)
    (hS : S.conjTranspose = -S) (hK : K.IsHermitian) (hB : B.IsHermitian) :
    ((M*S).conjTranspose *
      (M*((K*B).trace • (1:Mat)-K*B))).trace.re =
        (S*(M.conjTranspose*M)*K*B).trace.re := by
  have hG                                   :=
    SectorAssemblyBridges.hidden_gram_isHermitian M
  have hsg := antiHermitian_trace_re_zero S (M.conjTranspose*M) hS hG
  have ht := SectorAssemblyBridges.trace_mul_im_zero K B hK hB
  simp only [Matrix.conjTranspose_mul, hS, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc]
  simp [Complex.mul_re, hsg, ht]

/- Exact real mixed cancellation. All singular M are covered. No missing
mixed matrix identity or scalar cancellation is supplied as a premise. -/
theorem mixed_trace_cancel (M S K B : Mat)
    (hS : S.conjTranspose = -S) (hK : K.IsHermitian) (hB : B.IsHermitian) :
    ((M.conjTranspose*M)*(S*B*K-K*B*S)).trace.re +
      2*((M*S).conjTranspose *
        (M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0 := by
  let G : Mat := M.conjTranspose*M
  have hG                 := SectorAssemblyBridges.hidden_gram_isHermitian M
  have hcyc : (G*K*B*S).trace = (S*G*K*B).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (G*K) B S
  have hr := congrArg Complex.re (star_trace_four S G K B hS hG hK hB)
  rw [hidden_real_trace M S K B hS hK hB]
  change (G*(S*B*K-K*B*S)).trace.re + 2*(S*G*K*B).trace.re = 0
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, ← Matrix.mul_assoc, hcyc]
  simp at hr
  linarith only [hr]

end
end Glennie.SectorMixedTrace
