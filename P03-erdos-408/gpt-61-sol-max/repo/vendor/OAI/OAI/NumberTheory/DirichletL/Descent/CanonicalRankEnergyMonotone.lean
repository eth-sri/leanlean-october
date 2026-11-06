module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData

@[expose] public section

namespace OAI



open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns


theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→ActualEisensteinCubic.O) hp [∀i,(Ideal.span {p i}).IsMaximal]
     hcop 
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
     pool  base (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
     W (Z M F z c eps eps' A:ℝ) K degree 
    (hZ:1≤Z)(hA:0≤A)(he:eps≤eps')
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  gcongr <;> first | assumption | positivity | linarith

end SevenEighths.InverseMoment



end OAI
