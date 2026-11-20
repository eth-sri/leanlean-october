module
public import GafniTao.WooleySection7
public import GafniTao.WooleySection9Source

@[expose] public section

/-!
# The admissibility ledger entering Wooley Section 9

This file packages exactly the hypotheses needed to invoke Lemma 7.1 at one
node of the multigrade tree.  It also extracts one constant and one threshold
uniformly over the finitely many grades `1,...,k-1`; no asymptotic constant is
silently allowed to depend on the grade selected later.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Exact finite conditions needed by the Lemma-7.1 consumer at grade `r`
and scales `(a,b)`. -/
def WooleySection9Admissible
    (k r B a b nu B0 : ℕ) (tau epsilon : ℝ) : Prop :=
  1 ≤ nu ∧
  nu ≤ a ∧
  nu ≤ b ∧
  r * a ≤ (k - r + 1) * b ∧
  (k - r + 1) * b ≤ B ∧
  (∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a) ∧
  (∀ gammaVal : ℕ, gammaVal < nu →
    tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
      (a - (k - r) * gammaVal : ℕ)) ∧
  (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
    (nu : ℝ) ∧
  ((∀ gammaVal : ℕ, gammaVal < nu →
      (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal) →
    ∀ gammaVal : ℕ, gammaVal < nu →
      B0 ≤ wooleySection7BPrimeNat k r a b gammaVal)

/-- Lemma 7.1 with a grade-specific constant, restated using the exact
Section-9 admissibility record. -/
theorem wooleySourcePolynomial_lemma_7_1_of_admissible
    {k r p B s a b nu c B0 : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C tau epsilon : ℝ)
    (hc : 1 ≤ c) (hphi : phi.Spaced p c) (hgamma : gamma.Admissible)
    (hadm : WooleySection9Admissible k r B a b nu B0 tau epsilon)
    (hbound : ∀ {B s a b nu c : ℕ}, [NeZero (p ^ B)] →
      1 ≤ c → 1 ≤ nu → nu ≤ a → nu ≤ b →
      r * a ≤ (k - r + 1) * b → (k - r + 1) * b ≤ B →
      (∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a) →
      (∀ gammaVal : ℕ, gammaVal < nu →
        tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
          (a - (k - r) * gammaVal : ℕ)) →
      (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
        (nu : ℝ) →
      ((∀ gammaVal : ℕ, gammaVal < nu →
          (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal) →
        ∀ gammaVal : ℕ, gammaVal < nu →
          B0 ≤ wooleySection7BPrimeNat k r a b gammaVal) →
      ∀ (phi : WooleyPolynomialSystem k), phi.Spaced p c →
      ∀ (gamma : WooleySourceSequence), gamma.Admissible →
        wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
          C * (p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
      C * (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleyNextB k r b) b nu gamma := by
  rcases hadm with
    ⟨hnu, hnua, hnub, hab, hMB, hgammaK, hPhiTau, hEpsilonZero, hB0⟩
  simpa only [wooleySection7NextB_eq_wooleyNextB] using
    hbound (B := B) (s := s) (a := a) (b := b) (nu := nu) (c := c)
      hc hnu hnua hnub hab hMB hgammaK hPhiTau hEpsilonZero hB0
      phi hphi gamma hgamma

/-- One Lemma-7.1 constant and threshold, uniform not only in the grade but
also in the ambient modulus, polynomial system, coefficient sequence, and
all later Section-10 scales.  This quantifier order is the one needed before
choosing the arbitrarily large counterexample in Section 6. -/
theorem wooleySourcePolynomial_lemma_7_1_uniform_global
    {k p : ℕ} [NeZero p]
    (hpPrime : p.Prime) (hkp : k < p)
    (hlower : ∀ r, 1 ≤ r → r < k → WooleyPolynomialCorollary32At r p)
    (tau epsilon : ℝ) (htau : 0 < tau) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B0 : ℕ,
      ∀ {r B s a b nu c : ℕ}, [NeZero (p ^ B)] →
        1 ≤ r → r < k →
        ∀ (phi : WooleyPolynomialSystem k)
          (gamma : WooleySourceSequence),
          1 ≤ c → phi.Spaced p c → gamma.Admissible →
          WooleySection9Admissible k r B a b nu B0 tau epsilon →
          wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
            C * (p : ℝ) ^ (k ^ 2 * nu) *
              wooleySourcePolynomialMixedMean phi s r p B
                (wooleyNextB k r b) b nu gamma := by
  let I := {r : ℕ // r ∈ wooleyGradeRange (k - 1)}
  let : Fintype I := Fintype.ofFinset
    (wooleyGradeRange (k - 1)) (by intro i; rfl)
  have hex : ∀ i : I,
      ∃ C : ℝ, 1 ≤ C ∧ ∃ B0 : ℕ,
        ∀ {B s a b nu c : ℕ}, [NeZero (p ^ B)] →
          1 ≤ c → 1 ≤ nu → nu ≤ a → nu ≤ b →
          i.1 * a ≤ (k - i.1 + 1) * b →
          (k - i.1 + 1) * b ≤ B →
          (∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a) →
          (∀ gammaVal : ℕ, gammaVal < nu →
            tau * (wooleySection7BPrimeNat k i.1 a b gammaVal : ℝ) ≤
              (a - (k - i.1) * gammaVal : ℕ)) →
          (wooleySection7BPrimeNat k i.1 a b 0 : ℝ) * epsilon ^ 2 <
            (nu : ℝ) →
          ((∀ gammaVal : ℕ, gammaVal < nu →
              (nu : ℤ) < wooleySection7BPrimeInt k i.1 a b gammaVal) →
            ∀ gammaVal : ℕ, gammaVal < nu →
              B0 ≤ wooleySection7BPrimeNat k i.1 a b gammaVal) →
          ∀ (phi : WooleyPolynomialSystem k), phi.Spaced p c →
          ∀ (gamma : WooleySourceSequence), gamma.Admissible →
            wooleySourcePolynomialMixedMean phi s i.1 p B a b nu gamma ≤
              C * (p : ℝ) ^ (k ^ 2 * nu) *
                wooleySourcePolynomialMixedMean phi s i.1 p B
                  (wooleySection7NextB k i.1 b) b nu gamma := by
    intro i
    have hrBounds : 1 ≤ i.1 ∧ i.1 ≤ k - 1 := by
      simpa only [wooleyGradeRange, mem_Icc] using i.2
    exact wooleySourcePolynomial_lemma_7_1 hpPrime hrBounds.1 (by omega)
      hkp (hlower i.1 hrBounds.1 (by omega)) tau epsilon htau hepsilon
  choose Cr hCr B0r hbound using hex
  let C : ℝ := ∑ i : I, Cr i
  let B0 : ℕ := ∑ i : I, B0r i
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with hk0 | hk1 | hk
  · subst k
    exact ⟨1, le_rfl, 0, by omega⟩
  · subst k
    exact ⟨1, le_rfl, 0, by omega⟩
  · have hgrades : Nonempty I := by
      obtain ⟨r0, hr0⟩ := wooleyGradeRange_nonempty (r := k - 1) (by omega)
      exact ⟨⟨r0, hr0⟩⟩
    have hCOne : 1 ≤ C := by
      let i0 : I := Classical.choice hgrades
      exact (hCr i0).trans (by
        dsimp [C]
        exact Finset.single_le_sum
          (fun i _ => (hCr i).trans' (by norm_num)) (Finset.mem_univ i0))
    refine ⟨C, hCOne, B0, ?_⟩
    intro r B s a b nu c instPow hr hrk phi gamma hc hphi hgamma hadm
    have hrange : r ∈ wooleyGradeRange (k - 1) := by
      simp only [wooleyGradeRange, mem_Icc]
      omega
    let i : I := ⟨r, hrange⟩
    have hCrC : Cr i ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum
        (fun j _ => (hCr j).trans' (by norm_num)) (Finset.mem_univ i)
    have hB0 : B0r i ≤ B0 := by
      dsimp [B0]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hadmR : WooleySection9Admissible
        k r B a b nu (B0r i) tau epsilon := by
      rcases hadm with
        ⟨hnu, hnua, hnub, hab, hMB, hgammaK, hPhiTau,
          hEpsilonZero, hhard⟩
      refine ⟨hnu, hnua, hnub, hab, hMB, hgammaK, hPhiTau,
        hEpsilonZero, ?_⟩
      intro hall gammaVal hgammaVal
      exact hB0.trans (hhard hall gammaVal hgammaVal)
    have hrBound := wooleySourcePolynomial_lemma_7_1_of_admissible
      (k := k) (r := r) (p := p) (B := B) (s := s) (a := a)
      (b := b) (nu := nu) (c := c) (B0 := B0r i)
      phi gamma (Cr i) tau epsilon hc hphi hgamma hadmR
        (by
          intro B' s' a' b' nu' c' instPow'
          simpa only [i] using
            (@hbound i B' s' a' b' nu' c' instPow'))
    have hrest : 0 ≤ (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleyNextB k r b) b nu gamma :=
      mul_nonneg (by positivity)
        (wooleySourcePolynomialMixedMean_nonneg phi s r p B
          (wooleyNextB k r b) b nu gamma)
    calc
      _ ≤ Cr i * (p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma := hrBound
      _ = Cr i * ((p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma) := by ring
      _ ≤ C * ((p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma) :=
        mul_le_mul_of_nonneg_right hCrC hrest
      _ = C * (p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma := by ring

end

end GafniTao
