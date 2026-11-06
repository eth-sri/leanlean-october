module
public import GafniTao.WooleySourceMixed
public import GafniTao.WooleyPolynomialLemma63
public import GafniTao.WooleySection8
import WeylPort.Analytic.RealLaplace

public section

/-!
# Source-sequence consumers for Wooley Sections 6 and 8

The analytic inequalities were first proved on a finite box.  The exact
boxing equalities now allow those results to be stated and consumed on the
source's finitely supported integer sequences.  Every displayed mean below
is the literal source mean from (3.7), (3.8), or (3.19).
-/

namespace GafniTao


section
variable {k : ℕ} (phi : WooleyPolynomialSystem k)
include k phi
/-- Literal source-sequence form of the easy branch `B' ≤ nu` in Wooley
Lemma 7.1. -/
theorem wooleySourcePolynomial_section7_easy
    (p nu a b B s r gammaVal : ℕ)
    [NeZero p] [NeZero (p ^ B)]
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hnua : nu ≤ a) (hnub : nu ≤ b)
    (haa' : a ≤ wooleySection7NextB k r b)
    (hgamma : gammaVal < nu)
    (hBPrime : wooleySection7BPrimeInt k r a b gammaVal ≤ (nu : ℤ))
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
      (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleySection7NextB k r b) b nu gamma := by
  have hnuNext : nu ≤ wooleySection7NextB k r b := hnua.trans haa'
  pm_5035
  have hfinite := wooleyPolynomial_section7_easy
    (Q := wooleySourceBoxLength gamma) (p := p) (nu := nu)
    (a := a) (b := b) (B := B) (k := k) (s := s)
    (r := r) (gammaVal := gammaVal)
    phiBox hp hr hrk hnu hnua haa' hgamma hBPrime gammaBox
  simpa only [phiBox, gammaBox,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi s r p B a b nu hnua hnub gamma,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi s r p B (wooleySection7NextB k r b) b nu
        hnuNext hnub gamma] using hfinite

/-- Source-sequence form of the two-factor Hölder estimate (8.3). -/
theorem wooleySourcePolynomial_equation_8_3
    (p B r bPrime b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hr : 1 ≤ r) (hrk : r < k) (hnuPrime : nu ≤ bPrime)
    (hnub : nu ≤ b) (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) r p B bPrime b nu gamma ≤
      (wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma) ^
        (1 / ((k - r + 1 : ℕ) : ℝ)) *
      (wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma) ^
        (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) := by
  pm_5035
  have hfinite := wooleyPolynomial_equation_8_3
    (Q := wooleySourceBoxLength gamma) (p := p) (B := B)
    (k := k) (r := r) (bPrime := bPrime) (b := b) (nu := nu)
    phiBox hr hrk gammaBox
  simpa only [phiBox, gammaBox,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) r p B bPrime b nu hnuPrime hnub gamma,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) (k - r) p B b bPrime nu hnub hnuPrime gamma,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) (r - 1) p B bPrime b nu hnuPrime hnub gamma]
    using hfinite
end


end GafniTao
