module

public import OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
public import OAI.NumberTheory.DirichletL.Detector.RayPoolGood

@[expose] public section

namespace OAI


open scoped Classical Topology
open Filter
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

section
variable (η : Character) (a D ell : ℝ) (ha : 0<a)

include ha in
lemma annular_prime_coprime       (hD : 0<D)
    (hlarge : (η.modulus.absNorm:ℝ)/a<D)
    (W : ℝ→ℂ) (hs : Function.support W⊆Set.Ici a)
     P  (hp : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P η.modulus := by
  apply ProbeRaySlots.prime_coprime_of_norm_gt η ⟨P,hp⟩
  have hlo : a*D≤(P.absNorm:ℝ) := (le_div_iff₀ hD).mp (hs hW)
  have hh : (η.modulus.absNorm:ℝ)<a*D := by
    have hh := (div_lt_iff₀ ha).mp hlarge
    nlinarith
  exact hh.trans_le hlo

include ha in
theorem eventually_primePool_coprime       :
    ∀ᶠD : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a)] with D hD hlarge
  intro M H W b hs P hP hW
  exact annular_prime_coprime η a D ha hD hlarge W hs P (Finset.mem_filter.mp hP).2.1 hW

include ha in
theorem eventually_primePool_power_coprime       (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b (Z^ell),W ((P.absNorm:ℝ)/(Z^ell))≠0→IsCoprime P η.modulus :=
  (tendsto_rpow_atTop hell).eventually (eventually_primePool_coprime η a ha)

end

end SevenEighths.CenteredMomentDetectorDictionary



end OAI
