module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal HeckeFamily.O :=
  F.modulus⊓Ideal.span {(72:HeckeFamily.O)}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (by simp)

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:HeckeFamily.O)}} : Finset (Ideal HeckeFamily.O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal HeckeFamily.O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:HeckeFamily.O)} := inf_le_right

def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
