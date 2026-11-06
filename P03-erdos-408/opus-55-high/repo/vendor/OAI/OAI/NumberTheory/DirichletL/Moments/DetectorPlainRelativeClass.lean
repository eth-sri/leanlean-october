module

public import OAI.NumberTheory.DirichletL.Energy.Bands
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainRelativeClass
open HeckeFamily CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
variable (M:Ideal HeckeFamily.O)[NeZero M]
local instance:Finite (HeckeFamily.O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance:IsPrincipalIdealRing HeckeFamily.O:=IsCyclotomicExtension.Rat.three_pid K
variable (H:Subgroup (HeckeFamily.O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma ray_identity (θ:RayQuotient.Characters M H)(I:Ideal HeckeFamily.O)
    (hI:I∈RayQuotient.identityClass M H):
    idealCoeff (HeckeRayQuotient.character M H hH θ) I=1:=by
  rcases hI with ⟨hI,a,ha,u,hu,huH⟩
  rw [HeckeRayQuotient.idealCoeff_character]
  change IdealCharacter.ofResidue M θ (RayQuotient.character_unitInvariant M H hH θ) I=1
  rw [IdealCharacter.ofResidue_of_generator M θ _ hI ha,←hu]
  exact (RayOrthogonality.mem_characters_iff H θ).mp θ.property u huH

lemma relative_pool (η₀:Character)(θ:RayQuotient.Characters M H)(b P:ℝ)
    (I:Ideal HeckeFamily.O)(hI:I∈primePool M H b P):
    idealCoeff (relativeCharacter M H hH η₀ θ) I=idealCoeff η₀.inverse I:=by
  rw [relativeCharacter_ideal,ray_identity M H hH θ I (Finset.mem_filter.mp hI).2.2,one_mul]

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem positive_row (η η₀:Character)(θ:ι→RayQuotient.Characters M H)(m A z:HeckeFamily.O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→Ideal HeckeFamily.O→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*β i I) P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P t X₁ X₂:=by
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [relative_pool M H hH η₀ (θ i) (b i) (P i) I hI]

omit [DecidableEq ι] in
theorem energy_eq (η η₀:Character)(θ:ι→RayQuotient.Characters M H)(m A:HeckeFamily.O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→Ideal HeckeFamily.O→ℂ)(t X₁ X₂:ℝ)
    (keep:HeckeFamily.O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*β i I) P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row M H hH η η₀ θ m A z W₁ W₂ b P β t X₁ X₂]

end SevenEighths.CenteredMomentDetectorPlainRelativeClass

end

end OAI
