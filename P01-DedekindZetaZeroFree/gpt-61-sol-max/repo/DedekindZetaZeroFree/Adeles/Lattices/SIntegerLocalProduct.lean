module

public import Mathlib

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.SInteger

@[expose] public section


noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain

section
variable (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
include F S
abbrev SLocalProduct   :=
  InfiniteAdeleRing F × ((v : S) → v.1.adicCompletion F)

def sLocalDiagonal   :
    F →+* SLocalProduct F S :=
  algebraMap F (SLocalProduct F S)

@[simp] theorem sLocalDiagonal_infinite  
    (t : F) (v : InfinitePlace F) :
    (sLocalDiagonal F S t).1 v = algebraMap F v.Completion t := by
  simp only [sLocalDiagonal]
  apply InfiniteAdeleRing.algebraMap_apply

@[simp] theorem sLocalDiagonal_finite   (t : F) (v : S) :
    (sLocalDiagonal F S t).2 v = algebraMap F (v.1.adicCompletion F) t := rfl

abbrev sIntegerRing   : Subring F :=
  ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F).toSubring
end


private theorem valued_algebraMap_adicCompletion (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [show algebraMap F (v.adicCompletion F) t = (t : v.adicCompletion F) from rfl]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe

section
variable (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
include F S
private theorem mem_sIntegerRing_iff_valuation   (t : F) :
    t ∈ sIntegerRing F S ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S → v.valuation F t ≤ 1 := by
  rw [sIntegerRing, Set.integer_eq]
  simp only [Subring.mem_iInf, ValuationSubring.mem_toSubring, Valuation.mem_valuationSubring_iff,
    Finset.mem_coe]

theorem mem_sIntegerRing_iff   (t : F) :
    t ∈ sIntegerRing F S ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S →
        algebraMap F (v.adicCompletion F) t ∈ v.adicCompletionIntegers F := by
  rw [mem_sIntegerRing_iff_valuation]
  constructor
  · intro h v hv
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      valued_algebraMap_adicCompletion]
    exact h v hv
  · intro h v hv
    have := h v hv
    rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      valued_algebraMap_adicCompletion] at this

def sIntegerDiagonal    :=
  (sLocalDiagonal F S).comp (sIntegerRing F S).subtype

@[simp] theorem sIntegerDiagonal_apply   (t : sIntegerRing F S) :
    sIntegerDiagonal F S t = sLocalDiagonal F S (t : F) := rfl
end


end DedekindZetaZeroFree

end
