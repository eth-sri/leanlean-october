module

public import DedekindZetaZeroFree.Main

@[expose] public section

namespace DedekindZetaZeroFree.HeckeCorollary

theorem factor_ne_zero_off_one
    (L : Type) [Field L] [NumberField L] (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfactor : ∀ s : ℂ, 1 < s.re → f s * g s = NumberField.dedekindZeta L s)
    (s : ℂ) (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) : f s ≠ 0 := by
  obtain ⟨z, hz, hzeq, hzne⟩ := dedekindZeta_ne_zero L
  intro hzero
  have hprod := (continuation_unique_off_one _ _ (hf.mul hg) hz
    (fun t ht => (hfactor t ht).trans (hzeq t ht).symm)) (show s ∈ ({1}ᶜ : Set ℂ) from hs1)
  change f s * g s = z s at hprod
  rw [hzero, zero_mul] at hprod
  exact hzne s hs hs1 hprod.symm

end DedekindZetaZeroFree.HeckeCorollary
