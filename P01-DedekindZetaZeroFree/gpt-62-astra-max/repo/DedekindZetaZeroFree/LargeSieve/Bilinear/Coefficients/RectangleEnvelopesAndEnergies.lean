module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

variable (C : Context Q)

def rectangles (B : ℝ) : Finset (ℝ × ℝ) :=
  (ErrorRectangles.rectangles C).filter (fun P => P.1 * P.2 ≤
    (8 * max 1 (norm c)) * (C.N / Real.sqrt (B * C.M)) *
      Real.rpow (C.M * C.N) C.δ)

def envelope (B : ℝ) : ℝ :=
  ErrorRectangles.finiteSup (rectangles C B) (fun P =>
    Real.sqrt (P.1 * P.2) *
      Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
        ErrorRectangles.U Q B (C.N / (norm C.d * P.2))))

def coefficientForm (B : ℝ) (unit : Bool) : ℂ :=
  C.pairSum fun p hp =>
    (C.coefficient p / (Real.sqrt (norm (p.1 * p.2)) : ℂ)) *
      ∑ e ∈ C.mobiusDivisors,
        ((UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e /
          (norm e : ℂ)) *
          ∑ a ∈ C.reflectedRows B unit,
            C.primitive p hp a * Context.originDivisors (p.1 * p.2) (C.Z1 B e)

def weightedEnergy : ℝ :=
  ∑ u ∈ C.columns, ‖C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)‖ ^ 2

def incidenceEnergy : ℝ :=
  ∑ u ∈ C.columns,
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
      ((idealDivisors u).card : ℝ) *
        ‖C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)‖ ^ 2

def assemblyCost : ℝ :=
  (C.mobiusDivisors.card : ℝ) *
    ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ^ 2

theorem envelope_nonneg (B : ℝ) : 0 ≤ envelope C B := Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin

end
