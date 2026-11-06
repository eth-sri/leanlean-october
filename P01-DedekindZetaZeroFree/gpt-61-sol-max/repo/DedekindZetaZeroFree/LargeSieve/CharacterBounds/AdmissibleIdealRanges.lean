module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

section
variable (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F))
include F c
noncomputable def idealAdmissibleFinset   (X : ℝ)  :=
  (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).filter (fun I => Squarefree I ∧ I ⊔ c = ⊤)

noncomputable def paperShell   (T : ℝ)  :=
  (idealAdmissibleFinset F c (2 * T)).filter (fun I => T < (Ideal.absNorm I : ℝ))

theorem mem_idealAdmissibleFinset   (X : ℝ) (I : Ideal (𝓞 F)) :
    I ∈ idealAdmissibleFinset F c X ↔
      Squarefree I ∧ I ⊔ c = ⊤ ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealAdmissibleFinset, Finset.mem_filter, DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
  tauto

theorem mem_paperShell   (T : ℝ) (I : Ideal (𝓞 F)) :
    I ∈ paperShell F c T ↔
      Squarefree I ∧ I ⊔ c = ⊤ ∧ T < (Ideal.absNorm I : ℝ) ∧
        (Ideal.absNorm I : ℝ) ≤ 2 * T := by
  rw [paperShell, Finset.mem_filter, mem_idealAdmissibleFinset]
  tauto
end


end DedekindZetaZeroFree.LargeSieve.Sieve
