module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductor
public import DedekindZetaZeroFree.Adeles.Characters.SLocalTraceRestriction

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))

variable (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))

include hS in
theorem sLocalTraceCharacter_sIntegerDiagonal_eq_one
    (t : sIntegerRing F S) :
    sLocalTraceCharacter F S (sIntegerDiagonal F S t) = 1 := by

  rw [sLocalTraceCharacter_apply]
  simp only [sIntegerDiagonal_apply, sLocalDiagonal_infinite, sLocalDiagonal_finite]
  rw [((Finset.prod_subtype S (fun _ => Iff.rfl)
    (fun w => localFiniteCharacter F w (algebraMap F (w.adicCompletion F) (t : F)))).symm), ← (finprod_eq_prod_of_mulSupport_subset _ (Function.mulSupport_subset_iff'.2 fun v hv => (fun v hv =>
    localFiniteCharacter_eq_one_of_mem_integers F v _
      ((mem_sIntegerRing_iff F S (t : F)).1 t.2 v hv)) v hv))]
  exact traceCharacter_diagonal_product_formula F (t : F)

include hS in
theorem sLocalTraceCharacter_sIntegerDiagonal_mul_eq_one
    (m n : sIntegerRing F S) :
    sLocalTraceCharacter F S
      (sIntegerDiagonal F S m * sIntegerDiagonal F S n) = 1 := by
  rw [← map_mul]
  exact sLocalTraceCharacter_sIntegerDiagonal_eq_one F S hS (m * n)

end DedekindZetaZeroFree

end
