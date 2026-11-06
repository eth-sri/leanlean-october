module
public import OAI.NumberTheory.DirichletL.Descent.ShortCompletionEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CubeCompletedEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve InverseTerminalWidths InverseReflectedPhase CompletedHeight
universe v

def tupleDivisibilityMark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ) (A:Ideal Eis):ℂ :=
  ∑p:∀i,lists i,(∏i,w i (p i))*∏i,if (p i).val∣A then (1:ℂ) else 0

theorem completed_tuple_mark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ)
    (Ψ:Eis→*ℂ) (W:ℝ→ℂ) (hW:HasCompactSupport W)
    (X:ℝ) (hX:0<X) (H:Ideal Eis):
    markedCompletedT Ψ W X (fun A=>tupleDivisibilityMark lists w (H^3*A))=
      ∑p:∀i,lists i,(∏i,w i (p i))*markedCompletedT Ψ W X
        (fun A=>∏i,if (p i).val∣H^3*A then (1:ℂ) else 0) := by
  unfold tupleDivisibilityMark
  rw [markedCompletedT_finset_sum Finset.univ Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

theorem short_cube_exact_scale (Z N:ℝ) (hZ:1<Z) (H:Ideal Eis) (hH:H≠0):
    Z^(N-3*Real.logb Z (Ideal.absNorm H:ℝ))=Z^N/(Ideal.absNorm H:ℝ)^3 := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(Ideal.absNorm H:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hH (Ideal.absNorm_eq_zero_iff.mp hn))
  rw [Real.rpow_sub hz,show 3*Real.logb Z (Ideal.absNorm H:ℝ)=Real.logb Z (Ideal.absNorm H:ℝ)*3 by ring,
    show Z^(Real.logb Z (Ideal.absNorm H:ℝ)*3)=(Z^(Real.logb Z (Ideal.absNorm H:ℝ)))^3 from
      Real.rpow_mul_natCast hz.le _ 3,Real.rpow_logb hz (ne_of_gt hZ) hn]
