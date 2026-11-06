module
public import OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysical
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedDictionary
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentEnergyReferenceState CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData CenteredMomentSourceRow CenteredMomentEnergyOriginalSource CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput CenteredMomentFirstSourceReduction
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "zeroInput"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂


variable (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)(w σ freq:Fin 0→ℝ)
def positiveEmptyInput : Input (Fin 0):=
  CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
  (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
  (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
  s p ha t X₁ X₂ hX₁ hX₂

local notation "positiveInput"=>positiveEmptyInput M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq

theorem declared_capacity (hZ:1<Z):
    let Mdecl:=max s.width (length Z X₁+length Z X₂);
    Real.logb Z (volume zeroInput)≤Mdecl ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width ∧
    volume zeroInput≤Z^Mdecl:=by
  have hlog (X:ℝ)(hX:0<X):Real.logb Z X≤length Z X:=by
    rw [CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX]
    exact le_max_right _ _
  have hV:Real.logb Z (volume zeroInput)≤length Z X₁+length Z X₂:=by
    rw [CenteredMomentEnergyZeroReferencePhysical.balanced_volume,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact add_le_add (hlog X₁ hX₁) (hlog X₂ hX₂)
  have hdecl:=hV.trans (le_max_right s.width (length Z X₁+length Z X₂))
  refine ⟨hdecl,CenteredMomentEnergyPositiveHighParameters.actual_width_le s hZ,
    CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos zeroInput)).mp hdecl

lemma declared_capacity_upper (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal):
    max s.width (length Z X₁+length Z X₂)≤max Mcap (2*Lgoal):=by
  have hlen (X:ℝ)(hcap:X≤Z^Lgoal):length Z X≤Lgoal:=by
    unfold length
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mpr
      (max_le (Real.one_le_rpow hZ.le hL) hcap)
  exact max_le_max hs (by linarith [hlen X₁ hc₁,hlen X₂ hc₂])
