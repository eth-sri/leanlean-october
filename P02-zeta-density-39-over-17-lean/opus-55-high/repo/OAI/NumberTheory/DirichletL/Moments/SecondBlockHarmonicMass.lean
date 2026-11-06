module
public import OAI.NumberTheory.DirichletL.Moments.SecondBlockCount
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondBlockHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  (p : ActiveLabel S β) × Finset (CommonIndex p.val.1 p.val.2)

abbrev ActiveBlocks (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :=
  (q : ActiveSubsets S β) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

def pairWeight (C D : Ideal O) : ℝ := 1/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)

lemma pairWeight_nonneg (C D : Ideal O) : 0≤pairWeight C D := by
  unfold pairWeight
  positivity

def activeSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (q : ActiveSubsets S β) : Label := (q.1.val,q.2.image Subtype.val)

section
variable (S : Finset (Ideal O)) (β : Ideal O→ℂ)
include S β
lemma activeSubsetLabel_injective :
    Function.Injective (activeSubsetLabel S β) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=>x.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective
    (congrArg (fun x=>x.2) he)
  cases hU
  rfl

lemma active_common_shell (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (p : ActiveLabel S β) :
    p.val∈commonShell S β Y := by
  have hs := commonLabels_supported (activeSource S β) _ _ p.property
  have hn := commonLabel_norm_bounds S β Y hN _ _ p.property
  exact Finset.mem_filter.mpr ⟨p.property,
    (commonRadical_norm_le _ _ hs.1.1 hs.2.1).trans ((min_le_left _ _).trans hn.1)⟩

lemma activeSubsetLabel_mem (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (q : ActiveSubsets S β) :
    activeSubsetLabel S β q∈partitionLabels S β Y := by
  exact (mem_partitionLabels S β Y _).mpr
    ⟨active_common_shell S β Y hN q.1,commonSubset_support _ _ q.2⟩
end

section
variable (S : Finset (Ideal O)) (β : Ideal O→ℂ)
include S β
lemma active_mass_le_partition (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      pairWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,pairWeight v.1.1 v.1.2 := by pm_2872 pairWeight pairWeight_nonneg

lemma active_blocks_sum_eq (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*pairWeight p.val.1 p.val.2 := by
  pm_3812 Fintype.sum_sigma Finset.sum_const Finset.card_univ nsmul_eq_mul
  exact Fintype.sum_sigma _
end

theorem actual_active_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z ^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2)≤C*Z ^δ/(seed.absNorm:ℝ) := by pm_2873 common_harmonic_mass

theorem actual_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z ^B) →
      ∀K R H:ℝ,0<K → R≤Cr*Z ^L → H≤Z ^B →
      (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z ^ε/(seed.absNorm:ℝ) := by pm_2874 actual_active_harmonic_mass pairWeight pairWeight_nonneg

end SevenEighths.CenteredMomentSecondBlockHarmonicMass

end

end OAI
