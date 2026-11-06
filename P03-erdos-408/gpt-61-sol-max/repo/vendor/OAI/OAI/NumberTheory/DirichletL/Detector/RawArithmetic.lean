module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.RawIndexGrouping

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve


def rawArithmeticSeries (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ)  :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

lemma rawHighCoefficient_outer_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    simp_all [fullHighCoefficient, rawHighEmbedding, markedIdealHighSummand, bareIdealHighSummand]
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw  S   D   η 
     C   x w z  :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := Eq.symm (tsum_subtype_eq_of_support_subset (OAI.SevenEighths.ProbePhysical.rawHighCoefficient_outer_support S D η (fun H => Star.star (C.residueMonoid ↑H)) x w z))

end SevenEighths.ProbePhysical
end

end OAI
