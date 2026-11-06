module
public import OAI.NumberTheory.DirichletL.Energy.Floor
public import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorState
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def length (Z X:ℝ):ℝ:=Real.logb Z (max 1 X)

lemma length_nonneg (Z X:ℝ)(hZ:1<Z):0≤length Z X:=
  Real.logb_nonneg hZ (le_max_left _ _)

def ZeroAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→ s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→ X₁≤Z ^L→ X₂≤Z ^L→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z ^(s.width+ε)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→ RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→ X₁≤Z ^L→ X₂≤Z ^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z ^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z ^(w i)) (σ i) (v i) I)
      (fun i=>Z ^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z ^(s.width+ε)

theorem exists_positive_bottom (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L Lslot lo hi ε κ:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε)(hLs:0≤Lslot)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
          (ε/16) ε κ Z η₀ Q degree S C:=by
  have hs (T:Finset α):=CenteredMomentRayMaskedFloor.exists_positive_floor (α:=T)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask ε Lslot lo hi κ
    ha hb hbΦ hmask hε hLs hbeta hκ
  choose J S C hC hbound using hs
  pm_3362 S₀ S
  pm_5096 C₀ T α C
  pm_3360 hC₀ C₀ T hC
  refine ⟨∑T:Finset α,J T,S₀,C₀,hC₀,?_⟩
  intro η₀
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr (fun T=>hbound T η₀)
  pm_550 hall eventually_gt_atTop hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hslots:6*κ*(∑i,w i)≤ s.width:=by
    linarith [length_nonneg Z X₁ hZ1,length_nonneg Z X₂ hZ1]
  have hh:=hZ T θ w σ v t height hw hwL hσlo hσhi hheight hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hsub:S T⊆S₀:=by
    pm_864 T
  have hpc:p.control (S T)≤p.control S₀:=by
    pm_3359
  have hc:C T≤C₀:=by
    pm_3361 hC C₀
  have hj:J T≤∑T:Finset α,J T:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hpow:(1+|t|+height)^(J T)≤(1+|t|+height)^(∑T:Finset α,J T):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=p.control_nonneg S₀
  have hpt:=p.control_nonneg (S T)
  apply hh.trans
  gcongr
end SevenEighths.CenteredMomentEnergyBands

end

end OAI
