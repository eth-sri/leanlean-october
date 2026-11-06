module

public import OAI.NumberTheory.DirichletL.RayPrimeNormalizer
public import OAI.NumberTheory.DirichletL.Detector.PrincipalResidueActual

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open ProbePhysical PNT.AnnularPrimeMass
local notation "Id" => Ideal HeckeFamily.O

def pool (C : Set Id) (S : Finset Id) (a b x : ℝ) : Finset PrimeIdeal :=
  (annularPrimeIdeals C a b x \ S).subtype (fun P=>Prime P)

@[simp] theorem mem_pool (C : Set Id) (S : Finset Id) (a b x : ℝ) (P : PrimeIdeal) :
    P∈pool C S a b x ↔ P.val∈C ∧ ⌊x*a⌋₊<Ideal.absNorm P.val ∧
      Ideal.absNorm P.val≤⌊x*b⌋₊ ∧ P.val∉S := by
  simp only [pool,Finset.mem_subtype,Finset.mem_sdiff,mem_annularPrimeIdeals,P.property]
  tauto

theorem pool_norm_bounds (C : Set Id) (S : Finset Id) {a b x : ℝ}
    (ha : 0≤a) (hab : a≤b) (hx : 0<x) (P : PrimeIdeal) (hP : P∈pool C S a b x) :
    x*a<(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤x*b :=
  norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hP)).1

lemma pool_sum (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℝ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=>P.val)
  · simp_all
  · simp
  · simp_all
  simp

theorem pool_mass_eq_deleted (C : Set Id) (S : Finset Id) (W : ℝ→ℝ)
    {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support W⊆Set.Ioo a b) (hx : 0<x) :
    (∑P∈pool C S a b x,W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)))=
      weightedPrimeSumDeleted C S W x := by
  rw [pool_sum C S a b x (fun P=>W ((Ideal.absNorm P:ℝ)/x)*(Ideal.absNorm P:ℝ)^(-(5/6:ℝ))),
    weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  norm_num

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem ray_pool_mass_eventually_positive (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) :
    ∀ᶠx : ℝ in atTop,0<∑P∈pool (RayQuotient.identityClass M H) S a b x,
      W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  filter_upwards [RayPrimeNormalizer.eventually_pos M H hH S W hW hc hp hW0 hWne,
    eventually_gt_atTop (0:ℝ)] with x hx hx0
  rw [pool_mass_eq_deleted _ _ _ ha hab hsupp hx0]
  positivity

theorem ray_pool_mass_eventually_lower_bound (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) :
    ∃c : ℝ,0<c ∧ ∀ᶠx : ℝ in atTop,c*x^(1/6:ℝ)/Real.log x≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b x,
        W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  refine ⟨c,hc0,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with x hx hx0
  rw [pool_mass_eq_deleted _ _ _ ha hab hsupp hx0]
  exact hx

end SevenEighths.ProbeRaySlots
end

end OAI
