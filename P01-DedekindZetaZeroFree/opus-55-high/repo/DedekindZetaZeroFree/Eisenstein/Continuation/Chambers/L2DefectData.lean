module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData
public import DedekindZetaZeroFree.Eisenstein.Induction.ConvergenceChamberAndConstantTerms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPChamberL2Defect

open MeasureTheory
open scoped ENNReal

abbrev chamber : Set ℂ := KPEisensteinChamber.chamber

theorem chamber_isOpen : IsOpen chamber := 
  isOpen_lt continuous_const Complex.continuous_re

section ScalarFormula
variable {G Q X H A : Type*} [Group G] [Fintype A]
  [AddCommGroup H] [Module ℂ H]

def series (lift : Q → G) (representative : X → G)
    (realize : ℂ → H →ₗ[ℂ] (G → ℂ)) (f : ℂ → H) (s : ℂ) (x : X) : ℂ :=
  ∑' q, realize s (f s) (lift q * representative x)

end ScalarFormula

def scalarJet {X : Type*} (g : ℂ → X → ℂ) (k : ℕ) (s : ℂ) : X → ℂ :=
  fun x => iteratedDerivWithin k (fun z => g z x) chamber s

def spectralCorrection {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (d : ℕ) (u : ℕ → ℂ → H) (k : ℕ) (s : ℂ) : H :=
  ∑ j ∈ Finset.Icc 1 (min k 2),
    ((Nat.choose k j : ℂ) *
      iteratedDerivWithin j (KPContinuation.spectralCoordinate (d : ℤ)) chamber s) •
        u (k - j) s

def graphNorm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (u : Δ.domain) : ℝ := ‖(u : H)‖ + ‖Δ u‖
