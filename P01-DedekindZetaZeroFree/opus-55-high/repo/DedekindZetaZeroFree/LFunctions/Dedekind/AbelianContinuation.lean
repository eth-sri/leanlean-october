module

public import DedekindZetaZeroFree.LFunctions.Dedekind.EntireAbelianQuotient

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_continuation
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s := by apply DedekindZetaZeroFree.AbelianQuotient.zetaContinuation <;> assumption
