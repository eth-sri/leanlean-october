module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments

@[expose] public section

namespace OAI


open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeHighRowFamily

lemma rawMoment_mono_constant  {data}   {W}  {c κ C D : ℝ}
    (h : RawMoment data W c κ C) (hCD : C≤D) : RawMoment data W c κ D := by
  intro H X hH hX hsize rows hrows
  apply (h H X hH hX hsize rows hrows).trans
  bound

lemma moments_mono_constant {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ c κ C D height εm : ℝ} (hU : 0≤U) (h : Moments F Δ c κ C height εm) (hCD : C≤D) :
    Moments F Δ c κ D height εm := by
  constructor
  · intro n hn s hs t ht
    exact ⟨rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).1 hCD,
      rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).2 hCD⟩
  · intro selected hsel hcap1 hcap2 n hn s hs t ht
    exact (h.inverse_marked selected hsel hcap1 hcap2 n hn s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  · intro selected hsel hcap j k hj s hs t ht
    exact (h.plain_marked selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  · intro j k hj s hs t ht
    exact (h.plain_unmarked j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))

lemma sourceMomentsAt_mono_constant  M  [NeZero M]
     H   hH 
    {N : ℕ}  S   hS 
     η   rows  (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
     Z d a ε τ dmax b slotMesh binWidth   i   z 
    (Δ c κ C D height εm : ℝ) (hZ : 0≤Z) (hCD : C≤D)
    (h : SourceMomentsAt M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z Δ c κ C height εm) :
    SourceMomentsAt M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z Δ c κ D height εm := fun q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne => OAI.SevenEighths.ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ d) (h q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne) hCD

end SevenEighths.ProbeFinalAssembly



end OAI
