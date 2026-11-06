module

public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerTensorCosets

@[expose] public section

noncomputable section

open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

theorem mem_sIntegerRing_iff_valuation' (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (t : F) :
    t ∈ sIntegerRing F S ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S → v.valuation F t ≤ 1 := by
  rfl

def sGlobalBoundedIdealSet (F : Type) [Field F] [NumberField F]
    (P : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : P → ℤ) : Set F :=
  {x | x ∈ sIntegerRing F P ∧
    ∀ v : P, v.val.valuation F x ≤ WithZero.exp (-k v)}

theorem mem_sGlobalBoundedIdealSet_iff (F : Type) [Field F] [NumberField F]
    (P : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : P → ℤ) (x : F) :
    x ∈ sGlobalBoundedIdealSet F P k ↔
      ∀ w : HeightOneSpectrum (RingOfIntegers F),
        w.valuation F x ≤ WithZero.exp (-(if h : w ∈ P then k ⟨w, h⟩ else 0)) := by
  rw [sGlobalBoundedIdealSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hb⟩ w
    by_cases hw : w ∈ P
    · simp_all
    · rw [dif_neg hw]
      have := (mem_sIntegerRing_iff_valuation' F P x).mp hx w hw
      simpa using this
  · intro h
    refine ⟨?_, ?_⟩
    · rw [mem_sIntegerRing_iff_valuation']
      intro w hw
      have hw' := h w
      simp_all
    · intro v
      have hv := h v.val
      rwa [dif_pos v.property] at hv

theorem sGlobalBoundedIdealSet_eq_ballFractionalIdeal
    (F : Type) [Field F] [NumberField F]
    (P : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : P → ℤ) :
    sGlobalBoundedIdealSet F P k = (PoissonS.ballFractionalIdeal F P k : Set F) := by
  ext x
  rw [mem_sGlobalBoundedIdealSet_iff, SetLike.mem_coe,
    PoissonS.ScaleShift.fractionalIdeal_mem_iff_valuations F _
      (PoissonS.ballFractionalIdeal_ne_zero F P k) x]
  simp only [PoissonS.ScaleShift.count_ballFractionalIdeal]
