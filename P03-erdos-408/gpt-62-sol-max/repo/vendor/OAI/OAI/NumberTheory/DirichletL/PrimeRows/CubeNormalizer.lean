module

public import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (mw : MellinWindows)
    (hr0 : ∀y,(mw.left y).im=0) (hr1 : ∀y,(mw.right y).im=0)
    (hp0 : ∀y,0≤(mw.left y).re) (hp1 : ∀y,0≤(mw.right y).re) (hn0 : mw.left≠0) (hn1 : mw.right≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant mw.left mw.right (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant mw.left mw.right (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    mw hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=>Z^(ell j))) Z (1/6) hZ (fun j _=>hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant mw.left mw.right (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6)
        (slotMass (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=>Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end SevenEighths.ProbeHighRowFamily

end

end OAI
