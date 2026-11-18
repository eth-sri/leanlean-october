module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagation

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set


/-- The physical sampling cylinder is the affine image of its literal reference cylinder. -/
theorem physical_sampling_image {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (m : ℕ) :
    kineticAffine P0 scale '' samplingCylinder d m =
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale := by
  rw [samplingCylinder, kineticAffine_image_cylinder P0 _ scale 1 hscale zero_lt_one,
    mul_one]

/-- Every physical sampling subcylinder has an exact positive-radius reference preimage. -/
theorem physical_sampling_subcylinder {d : ℕ} (P0 P : KineticPoint d)
    {scale r : ℝ} (hscale : 0 < scale) (hr : 0 < r) (m : ℕ)
    (hsub : backwardCylinder P r ⊆
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) :
    backwardCylinder (kineticAffineInverse P0 scale P) (r / scale) ⊆
      samplingCylinder d m := by
  have hi := kineticAffine_image_cylinder P0 (kineticAffineInverse P0 scale P)
    scale (r / scale) hscale (div_pos hr hscale)
  rw [kineticAffine_apply_inverse P0 hscale.ne', mul_div_cancel₀ r hscale.ne'] at hi
  intro Z hZ
  have hp := hsub (hi ▸ (mem_image_of_mem (kineticAffine P0 scale) hZ))
  rw [← physical_sampling_image P0 hscale m] at hp
  have hp' := (mem_kineticAffine_image_iff P0 _ hscale.ne' _).mp hp
  simpa only [kineticAffineInverse_apply P0 hscale.ne'] using hp'

/-- The local stack-comparison closure lies in the same physical reference closure. -/
theorem physical_sampling_comparison_image_subset {d : ℕ} (P0 P : KineticPoint d)
    {scale r : ℝ} (hscale : 0 < scale) (hr : 0 < r) (m : ℕ)
    (hsub : backwardCylinder P r ⊆
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) :
    kineticAffine P r '' stackComparisonRegion d m ⊆
      kineticAffine P0 scale '' referenceRegion d m (referenceBound m) := by
  let Q := kineticAffineInverse P0 scale P
  have hQ := physical_sampling_subcylinder P0 P hscale hr m hsub
  have hi := sampling_comparison_image_subset m Q (div_pos hr hscale) hQ
  have hc : kineticAffine P r = kineticAffine P0 scale ∘ kineticAffine Q (r / scale) := by
    rw [kineticAffine_comp, kineticAffine_apply_inverse P0 hscale.ne',
      mul_div_cancel₀ r hscale.ne']
  rw [hc]
  rintro Z ⟨Y, hY, rfl⟩
  exact ⟨kineticAffine Q (r / scale) Y, hi ⟨Y, hY, rfl⟩, rfl⟩

/-- The comparison region contains each entire forward stack, including its top face. -/
theorem forwardStack_subset_comparison {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (m : ℕ) :
    forwardStack P r m ⊆ kineticAffine P r '' stackComparisonRegion d m := by
  rw [← kineticAffine_image_forwardStack P hr m]
  apply image_mono
  exact subset_closure.trans (stackComparisonRegion_geometry d m).2.2.2

/-- Sampling-cylinder closures remain inside the buffered comparison closure. -/
theorem physical_sampling_closure_subset {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (m : ℕ) :
    closure (backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) ⊆
      closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) := by
  rw [← physical_sampling_image P0 hscale m]
  apply closure_mono
  apply image_mono
  exact subset_closure.trans (sampling_closure_subset_reference d m (referenceBound_large m))



/-- The uniform cap comparison applies to every physical sampling subcylinder above cutoff. -/
theorem exists_physical_macroscopic_cap_constant (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (m : ℕ) (r0 : ℝ)
    (hr0 : 0 < r0) (hr01 : r0 < 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (scale : ℝ), 0 < scale →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
        IsAdmissibleSupersolution A O p C_A u →
      ∀ (Q : KineticPoint d) (r ell : ℝ), 0 < r → r0 * scale ≤ r →
        backwardCylinder Q r ⊆
          backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale →
        0 ≤ ell → (∀ Z ∈ kineticAffine Q r '' cap d, ell ≤ u Z) →
        ∀ P ∈ backwardCylinder P0 scale, c * ell ≤ u P := by
  obtain ⟨c, hc, hc1, hmacro⟩ :=
    exists_macroscopic_cap_constant d hd lam Lam hlam hLam m r0 hr0 hr01
  refine ⟨c, hc, hc1, ?_⟩
  intro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu Q r ell hr hbig hsub
    hell hcap P hP
  let Qref := kineticAffineInverse P0 scale Q
  let Pref := kineticAffineInverse P0 scale P
  have hrref : r0 ≤ r / scale := (le_div_iff₀ hscale).mpr hbig
  have hsubref := physical_sampling_subcylinder P0 Q hscale hr m hsub
  have hPref : Pref ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    apply (kineticAffine_mem_cylinder P0 Pref hscale).mp
    simpa only [Pref, kineticAffine_apply_inverse P0 hscale.ne'] using hP
  have hcapref : ∀ Z ∈ kineticAffine (kineticAffine P0 scale Qref) (scale * (r / scale)) ''
      cap d, ell ≤ u Z := by
    simpa only [Qref, kineticAffine_apply_inverse P0 hscale.ne',
      mul_div_cancel₀ r hscale.ne'] using hcap
  have hbound := hmacro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu
    Qref (r / scale) ell hrref hsubref hell hcapref Pref hPref
  simpa only [Pref, kineticAffine_apply_inverse P0 hscale.ne'] using hbound

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

