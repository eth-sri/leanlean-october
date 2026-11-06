module

public import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
public import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
public import OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

def effectiveRadial (r:Radial):Radial:=
  {r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}

lemma radialEnergy_effective (r:Radial)(f:O→ℂ):
    radialEnergy f (effectiveRadial r).keep r.profile r.scale=
      radialEnergy f r.keep r.profile r.scale:=by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hz:r.profile (‖eisEmbedding z‖^2/r.scale)=0 <;>
    simp [effectiveRadial,hk,hz]

def effectiveState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z Bmask bΦ:=
  {s with radial:=effectiveRadial s.radial
          row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
          nonexceptional:=fun z hz=>s.nonexceptional z hz.1}

lemma effective_row_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth:=by
  rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
  exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hz.2)

lemma effective_character_nonprincipal {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    (naturalCharacter s.character z).residue≠1:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  exact (naturalRow s.character z hn).nonprincipal hn s.fixedModulus s.puncture
    s.puncture_ne_zero (s.nonexceptional z hz.1)

lemma effective_character_cap {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hbΦ:0≤bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*bΦ*Z^s.width:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  have h:=(naturalRow s.character z hn).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans_le s.base_ge_one) hbΦ s.modulus_bound (effective_row_norm s z hz)
  simpa only [NaturalState.width,add_comm s.characterWidth s.rowWidth] using h

def comparisonFirst (Z M:ℝ):ℝ:=Z^(M/4)
def comparisonSecond (Z M X₁ X₂:ℝ):ℝ:=X₁*X₂/comparisonFirst Z M

lemma comparison_positive (Z M X₁ X₂:ℝ)(hZ:0<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    0<comparisonFirst Z M ∧ 0<comparisonSecond Z M X₁ X₂:=
  ⟨Real.rpow_pos_of_pos hZ _,div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos hZ _)⟩

lemma comparison_same_product (Z M X₁ X₂:ℝ)(hZ:0<Z):
    comparisonFirst Z M*comparisonSecond Z M X₁ X₂=X₁*X₂:=by
  unfold comparisonSecond
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hZ (M/4)).ne'

lemma comparison_second_power (Z M X₁ X₂:ℝ)(hZ:1<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    comparisonSecond Z M X₁ X₂=Z^(Real.logb Z (X₁*X₂)-M/4):=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos hX₁ hX₂)]
  rfl

end SevenEighths.CenteredMomentEnergyReferenceState

end

end OAI
