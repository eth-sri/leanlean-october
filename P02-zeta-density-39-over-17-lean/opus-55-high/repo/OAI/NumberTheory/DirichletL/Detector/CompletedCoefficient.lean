module
public import OAI.NumberTheory.DirichletL.Detector.ReciprocityCRT
public import OAI.NumberTheory.DirichletL.Detector.CubicGaussCRT
public import OAI.NumberTheory.DirichletL.Detector.CompletedCRTPhase
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

lemma supported_completed (c n : O) (hc : Supported (Ideal.span {c}))
    (hn : Supported (Ideal.span {n})) : Supported (Ideal.span {c*n^3}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  apply (supported_mul_iff _ _).mpr
  refine ⟨hc,?_⟩
  have hn2 := (supported_mul_iff _ _).mpr ⟨hn,hn⟩
  have hn3 := (supported_mul_iff _ _).mpr ⟨hn2,hn⟩
  simpa only [pow_succ, pow_zero, one_mul] using hn3

lemma primary_completed (c n : O) (hc : goodLambda^2∣c-1)
    (hn : goodLambda^2∣n-1) : goodLambda^2∣c*n^3-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left hc (n^3))
    (dvd_mul_of_dvd_left hn (n^2+n+1))
  convert h using 1 ; ring

def correctedFiniteCoefficient (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : A≠0) (H : O) : ℂ :=
  gaussTwo I hI * star (G A) * reciprocityCoefficient A s hA H

theorem correctedFiniteCoefficient_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (H : O) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    correctedFiniteCoefficient (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      correctedFiniteCoefficient I hI.2 A s hA H * correctedFiniteCoefficient J hJ.2 B r hB H := by
  dsimp only
  let c := primaryGenerator I
  let d := primaryGenerator J
  let A := c*n^3
  let B := d*m^3
  have hAs := supported_completed c n hc hn
  have hBs := supported_completed d m hd hm
  have hAB : IsCoprime A B := hcop.of_mul_left_left.of_mul_right_left
  pm_8607 hnA n A c
  pm_8607 hmB m B d
  have hcA : c∣A := dvd_mul_right c (n^3)
  have hdB : d∣B := dvd_mul_right d (m^3)
  pm_8608 hcd c hcA hcm
  pm_8608 hnd n hnA hnm
  have hphase := completed_cubic_cross_cancel c n d m hc hn hd hm hpc hpn hpd hpm hcd hcm hnd hnm
  change sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)=1 at hphase
  change gaussTwo (I*J) hIJ.2 * star (G (A*B)) *
      reciprocityCoefficient (A*B) (s*r) _ H =
    (gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
    (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)
  rw [gaussTwo_coprime_product_sextic I J hI hJ hIJ hIJcop,
    G_mul A B (supported_residue_odd A hAs) (supported_residue_odd B hBs),
    reciprocityCoefficient_product A B s r hAs hBs hs hr
      (primary_completed c n hpc hpn) (primary_completed d m hpd hpm) hps hpr hcop H]
  simp only [star_mul]
  change (sexticPair c d^2 * gaussTwo I hI.2 * gaussTwo J hJ.2) *
    (star (reciprocitySign A B)*(star (G B)*star (G A))) *
    (sexticPair A B * reciprocityCoefficient A s _ H * reciprocityCoefficient B r _ H) = _
  grind

end SevenEighths.ProbePhysical
end

end OAI
