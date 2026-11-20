module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.CanonicalRankMoments

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[OAI.PrincipalFamily.Maximal p]
variable (hcop:OAI.PrincipalFamily.Coprime p)
variable (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

omit [DecidableEq σ] in
theorem canonical_rank_negative (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ)(hM:Mmax<0):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mmax Fcap z c eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc
  exfalso
  linarith

omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤M₂)(hF:F₁≤F₂)(hc:c₂≤c₁)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  refine h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) ?_ hnorm ss hss labels hlabels s
  unfold CanonicalMargins at *
  constructor <;> linarith [hmargin.1,hmargin.2]

omit [DecidableEq σ] in
theorem canonical_rank_height_constant (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A B:ℝ)(K degree J:ℕ)
    (hZ:0<Z)(hA:0≤A)(hAB:A≤B)(hJ:degree≤J)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps B K J :=by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  have hB:0≤B:=hA.trans hAB
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hZ.le _)
  · exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.mul_le_mul_left 2 hJ)
  · positivity
  · positivity

end SevenEighths.InverseMoment

end

end OAI
