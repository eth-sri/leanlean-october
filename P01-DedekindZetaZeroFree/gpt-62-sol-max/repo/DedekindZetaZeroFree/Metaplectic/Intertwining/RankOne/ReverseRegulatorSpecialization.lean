module

public import DedekindZetaZeroFree.Algebra.RationalEvaluation

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseRegulatorSpecialization

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShells

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def IsShellExpansion (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : H₀ → ShellNumerator) : Prop :=
  ∀ (r : ℂˣ), IsRegular F q r → ∀ lam : ℂ, ConvergenceRegion F q r lam →
    ∀ h : H₀,
      H F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h =
        evaluateNumerator (p h) r (Q F q lam) /
          shellDenominator F q r (Q F q lam)

def actualDoubleCoefficient (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (h : H₀) : ℂ :=
  ((J.op .minus (additiveParameter F q r)
    (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r)).val
      (openCoordinate F ζ hζ q 0)).val h

open RationalEvaluation

private theorem good_restriction (p : ShellNumerator) (r : ℂˣ)
    (hd : shellDenominator F q (r : ℂ) 1 ≠ 0) :
    Evaluates₂ (RingHom.id ℂ) (r : ℂ) (restrictionAtOne F q p)
      (evaluateNumerator p r 1 / shellDenominator F q r 1) := by
  have hq : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (ValuativeRel.valuation (LocalField F q)).integer)).ne'
  have ht : t F q (r : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hq) (pow_ne_zero _ r.ne_zero)
  have hn : Evaluates₂ (RingHom.id ℂ) (r : ℂ)
      (p.sum (fun ij c => RatFunc.C c * (RatFunc.X : Rr)^ij.1))
      (evaluateNumerator p r 1) := by
    classical
    simp only [evaluateNumerator, one_zpow, mul_one, Finsupp.sum]
    apply Evaluates₂.sum
    intro ij hij
    exact Evaluates₂.mul (Evaluates₂.const _) (Evaluates₂.zpow Evaluates₂.var r.ne_zero _)
  have hT : Evaluates₂ (RingHom.id ℂ) (r : ℂ)
      (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)
      (t F q (r : ℂ)) := Evaluates₂.mul (Evaluates₂.const _) (Evaluates₂.pow Evaluates₂.var _)
  have hD := Evaluates₂.mul (Evaluates₂.mul (Evaluates₂.sub Evaluates₂.one hT)
    (Evaluates₂.sub Evaluates₂.one (Evaluates₂.inv hT ht)))
    (Evaluates₂.sub Evaluates₂.one (Evaluates₂.const ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ))))
  rw [restrictionAtOne_eq]
  simpa only [shellDenominator, one_pow, one_zpow, mul_one, RingHom.id_apply] using Evaluates₂.div hn hD (by simpa only [shellDenominator, one_pow, one_zpow, mul_one, RingHom.id_apply] using hd)

theorem restriction_regular (p : ShellNumerator) (r : ℂˣ)
    (hr : IsRegular F q r) :
    Polynomial.eval (r : ℂ) (RatFunc.denom (restrictionAtOne F q p)) ≠ 0 := by
  have hq : (1 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
      (ValuativeRel.valuation (LocalField F q)).integer))
  have hq3 : (residueCardinality (LocalField F q) : ℂ)^3 ≠ 1 := by
    exact_mod_cast (one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)).ne'
  have ht : t F q (r : ℂ) ≠ 1 := by
    intro he
    exact hr (by rw [he]; exact sub_self 1)
  have hd : shellDenominator F q r 1 ≠ 0 := by
    simp only [shellDenominator, one_pow, one_zpow, mul_one]
    apply mul_ne_zero (mul_ne_zero hr _) _
    · exact sub_ne_zero.mpr (fun he => ht (inv_eq_one.mp he.symm))
    · simp only [zpow_neg, zpow_ofNat]
      exact sub_ne_zero.mpr (fun he => hq3 (inv_eq_one.mp he.symm))
  exact (good_restriction F q p r hd).1

end
end DedekindZetaZeroFree.KPRankOneReverseRegulatorSpecialization
