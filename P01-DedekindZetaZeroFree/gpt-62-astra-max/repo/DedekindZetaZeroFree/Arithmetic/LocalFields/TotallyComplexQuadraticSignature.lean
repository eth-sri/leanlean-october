module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem quadraticExtension_signature
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (hF : NumberField.IsTotallyComplex F) (hdeg : Module.finrank F E = 2) :
    NumberField.IsTotallyComplex E ∧
      NumberField.InfinitePlace.nrComplexPlaces E =
        2 * NumberField.InfinitePlace.nrComplexPlaces F := by
  haveI hFc := hF
  haveI : NumberField.IsTotallyComplex E :=
    NumberField.isTotallyComplex_of_algebra F E
  refine ⟨inferInstance, ?_⟩
  have hmult :=
    (Module.finrank_mul_finrank ℚ F E).symm
  rw [hdeg, (NumberField.IsTotallyComplex.finrank F)] at hmult
  have h2 : 2 * NumberField.InfinitePlace.nrComplexPlaces E =
      2 * (2 * NumberField.InfinitePlace.nrComplexPlaces F) := by
    rw [← (NumberField.IsTotallyComplex.finrank E), hmult]
    ring
  exact Nat.mul_left_cancel (by norm_num) h2

end DedekindZetaZeroFree.LargeSieve
