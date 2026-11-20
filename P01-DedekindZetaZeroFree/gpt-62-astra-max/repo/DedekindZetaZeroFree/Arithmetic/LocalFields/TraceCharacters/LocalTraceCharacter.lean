module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.CompletionTraceComparison
public import DedekindZetaZeroFree.Adeles.Characters.RationalPadicCharacter

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

variable (v : HeightOneSpectrum (𝓞 F))

def localFiniteCharacter :
    AddChar (v.adicCompletion F) Circle :=
  (rationalPadicCharacter (PlaceTraceAdapter.prime F v)).compAddMonoidHom
    (PlaceTraceAdapter.trace F v).toAddMonoidHom

theorem localFiniteCharacter_apply
    (x : v.adicCompletion F) :
    localFiniteCharacter F v x =
      rationalPadicCharacter (PlaceTraceAdapter.prime F v)
        (PlaceTraceAdapter.trace F v x) := rfl

private theorem continuous_rationalCompletionEquiv_symm :
    Continuous (PlaceTraceAdapter.rationalCompletionEquiv F v).symm := by
  letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ
      (PlaceTraceAdapter.rationalPlace F v)
  have hfun : (PlaceTraceAdapter.rationalCompletionEquiv F v).symm =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
        (PlaceTraceAdapter.rationalPlace F v)).symm.toAlgEquiv.toRingEquiv := by
    ext x; rfl
  rw [hfun]
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
    (PlaceTraceAdapter.rationalPlace F v)).symm.continuous_toFun

private theorem continuous_padicMap :
    Continuous (PlaceTraceAdapter.padicMap F v) := by
  rw [PlaceTraceAdapter.padicMap]
  exact (finitePlaceAdicCompletionMap_continuous ℚ F
      (PlaceTraceAdapter.rationalPlace F v) ⟨v, rfl⟩).comp
    (continuous_rationalCompletionEquiv_symm F v)

theorem continuous_localFiniteCharacter :
    Continuous (localFiniteCharacter F v : v.adicCompletion F → Circle) := by
  haveI : ContinuousSMul ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) := by
    constructor
    exact ((continuous_padicMap F v).comp continuous_fst).mul continuous_snd
  exact (continuous_rationalPadicCharacter (PlaceTraceAdapter.prime F v)).comp ((PlaceTraceAdapter.trace F v).continuous_of_finiteDimensional)

theorem localFiniteCharacter_add
    (x y : v.adicCompletion F) :
    localFiniteCharacter F v (x + y) =
      localFiniteCharacter F v x * localFiniteCharacter F v y :=
  AddChar.map_add_eq_mul _ x y

theorem localFiniteCharacter_eq_one_iff
    (x : v.adicCompletion F) :
    localFiniteCharacter F v x = 1 ↔
      PlaceTraceAdapter.trace F v x ∈
        Set.range (fun z : ℤ_[PlaceTraceAdapter.prime F v] =>
          (z : ℚ_[PlaceTraceAdapter.prime F v])) := by
  rw [localFiniteCharacter_apply]
  exact rationalPadicCharacter_eq_one_iff (PlaceTraceAdapter.prime F v) _

theorem localFiniteCharacter_eq_one_of_mem_integers (a : v.adicCompletion F)
    (ha : a ∈ v.adicCompletionIntegers F) :
    localFiniteCharacter F v a = 1 := by
  rw [localFiniteCharacter_eq_one_iff]
  exact PlaceTraceAdapter.trace_mem_padicIntegers F v a ha

end DedekindZetaZeroFree

end
