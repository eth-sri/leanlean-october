module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContraction
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationDecayArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGrowthLimit
import Mathlib.MeasureTheory.Measure.Real
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityAffine
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryStack
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.DensityLadderAffine
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.JointWitness
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.LevelMeasurabilityAffine
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ParameterChoice
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryAffine
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryImages
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPaths
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivity
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.TerminalLevel
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.TerminalLevelArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullThreshold
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Algebra.Order.Archimedean.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridors
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsInclusions
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsRegion
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationDimensionless
import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Algebra.BigOperators.Ring.Finset
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageVolume
import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.AssemblySmall
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityMinimum
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFull
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffAffine
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffRawHessian
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullScaling
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullSourceNorm
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Separation.Regular
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.LevelMeasurability
import Mathlib.Topology.MetricSpace.Lipschitz
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsPaths

/-! # The kinetic Holder theorem from the proved growth and oscillation estimates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder
open scoped ENNReal MatrixOrder
open HypoellipticAleksandrov.KineticAleksandrov.Holder
open Holder.Growth Covering HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open scoped BigOperators
open InkSpots HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots
open Parabolic

/- The kinetic Holder theorem, conditional only on its admissibility predicate. -/
theorem kinetic_holder_of_aleksandrov_aux
    (d ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsAdmissibleSolution A Omega p C_A u →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha  := by
  obtain ⟨alpha, D, ha, ha1, hdecay⟩ : ∃ alpha D : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R rho : ℝ), 0 < R → 0 < rho → rho ≤ R →
        closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSolution A O p C_A u →
        oscillationOn u (backwardCylinder P0 rho) ≤
          D * (rho / R) ^ alpha * oscillationOn u (backwardCylinder P0 R) := by
    obtain ⟨theta, q, ht, ht1, hq, hq1, hcontract⟩ : ∃ theta q : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < q ∧ q < 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
        closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSolution A O p C_A u →
        oscillationOn u (backwardCylinder P0 (theta * R)) ≤
          q * oscillationOn u (backwardCylinder P0 R) := by
      obtain ⟨theta, S, r, kappa, ht, ht1, _hr, hk, hk1, _hS, hupper⟩ : ∃ (theta : ℝ) (S : KineticPoint d) (r kappa : ℝ),
      0 < theta ∧ theta < 1 ∧ 0 < r ∧ 0 < kappa ∧ kappa ≤ 1 ∧
      closure (backwardCylinder S r) ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R → closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSupersolution A O p C_A (fun P => -u P) →
      ∀ b h : ℝ, 0 < h → (∀ P ∈ closure (backwardCylinder P0 R), u P ≤ b) →
        (1 / 2 : ℝ) * (volume (kineticAffine P0 R '' backwardCylinder S r)).toReal ≤
          (volume ({P | u P ≤ b - h} ∩
            kineticAffine P0 R '' backwardCylinder S r)).toReal →
        ∀ P ∈ backwardCylinder P0 (theta * R), u P ≤ b - kappa * h := by
        obtain ⟨theta, ht, ht1, S, r, hr, hS, hbeta⟩ : ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      ∃ (P_Sigma : KineticPoint d) (r_Sigma : ℝ), 0 < r_Sigma ∧
        closure (backwardCylinder P_Sigma r_Sigma) ⊆
          backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
        ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
          ∃ kappa_beta : ℝ, 0 < kappa_beta ∧
            ∀ A : FullKineticCoefficient d,
              Measurable (fullKineticCoefficientAt A) →
              (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
              (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
                lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
              (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
                fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
              ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
              ∀ O : Set (KineticPoint d), IsOpen O →
                closure (backwardCylinder P₀ R) ⊆ O →
              ∀ u : KineticPoint d → ℝ,
                (∀ P ∈ O, 0 ≤ u P) → IsAdmissibleSupersolution A O p C_A u →
                beta * (volume (kineticAffine P₀ R ''
                  backwardCylinder P_Sigma r_Sigma)).toReal ≤
                    (volume ({P | 1 ≤ u P} ∩ (kineticAffine P₀ R ''
                      backwardCylinder P_Sigma r_Sigma))).toReal →
                ∀ P ∈ backwardCylinder P₀ (theta * R), kappa_beta ≤ u P := by
          obtain ⟨theta, ht, ht1, S, r, hr, hS, hbeta⟩ : ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
              ∃ (Psigma : KineticPoint d) (rsigma : ℝ), 0 < rsigma ∧
                closure (backwardCylinder Psigma rsigma) ⊆
                  backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
                ∀ beta : ℝ, 0 < beta → beta ≤ 1 → ∃ kappa : ℝ, 0 < kappa ∧
                  ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
                  ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
                  ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P0 R) ⊆ O →
                  ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
                    IsAdmissibleSupersolution A O p C_A u →
                    beta * (volume (kineticAffine P0 R '' backwardCylinder Psigma rsigma)).toReal ≤
                      (volume ({P | 1 ≤ u P} ∩
                        kineticAffine P0 R '' backwardCylinder Psigma rsigma)).toReal →
                    ∀ P ∈ backwardCylinder P0 (theta * R), kappa ≤ u P := by
            obtain ⟨c, C, hc, hc1, hC, hink⟩ : ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧
              ∀ m : ℕ, 0 < m →
              ∀ eta r0 : ℝ, 0 < eta → eta < 1 → 0 < r0 → r0 < 1 →
              ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
              ∀ E F : Set (KineticPoint d),
                Bornology.IsBounded E → Bornology.IsBounded F →
                MeasurableSet E → MeasurableSet F → E ⊆ F ∩ backwardCylinder P0 R →
                (∀ (P : KineticPoint d) (r : ℝ), 0 < r →
                  backwardCylinder P r ⊆ backwardCylinder P0 R →
                  (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
                    (volume (E ∩ backwardCylinder P r)).toReal →
                  r < r0 * R ∧ forwardStack P r m ⊆ F) →
                (volume E).toReal ≤ (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) *
                  ((volume (F ∩ backwardCylinder P0 R)).toReal +
                    R ^ (4 * d + 2) * C * (m : ℝ) * r0 ^ 2) := by
              obtain ⟨c, C, hc, hc1, hC, hink⟩ : ∃ c_d C_d : ℝ, 0 < c_d ∧ c_d < 1 ∧ 0 < C_d ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (eta r₀ : ℝ), 0 < eta → eta < 1 → 0 < r₀ → r₀ < 1 →
      ∀ (E F : Set (KineticPoint d)),
        Bornology.IsBounded E → Bornology.IsBounded F →
        NullMeasurableSet E volume → NullMeasurableSet F volume →
        E ⊆ F ∩ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 →
        (∀ (P : KineticPoint d) (r : ℝ), 0 < r →
          backwardCylinder P r ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 →
          (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
            (volume (E ∩ backwardCylinder P r)).toReal →
          r < r₀ ∧ forwardStack P r m ⊆ F) →
        (volume E).toReal ≤
          (((m : ℝ) + 1) / (m : ℝ)) * (1 - c_d * eta) *
            ((volume (F ∩ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal +
              C_d * (m : ℝ) * r₀ ^ 2) := by
                obtain ⟨hc, hc1⟩ := coveringGain_bounds d
                obtain ⟨hC, hCV⟩ : 0 < coveringLeakage d ∧
                  32*(volume (unitCylinder d)).toReal ≤ coveringLeakage d := by
                    have hV : 0 < (volume (unitCylinder d)).toReal := ENNReal.toReal_pos
                      (volume_cylinder_pos_ne_top _ zero_lt_one).1.ne'
                      (volume_cylinder_pos_ne_top _ zero_lt_one).2
                    have hn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
                    have hk : 0 ≤ (5 : ℝ)^d := by positivity
                    dsimp [coveringLeakage]
                    constructor <;> nlinarith

                  /- The delayed multiplier is at least one for every positive natural height. -/
                refine ⟨coveringGain d, coveringLeakage d, hc, by linarith, hC, ?_⟩
                intro m hm eta R heta heta1 hR hR1 E F hEb _hFb hE _hF hEF hstack
                have hEQ : E ⊆ unitCylinder d := fun X hX => (hEF hX).2
                have hs := hstack
                by_cases hsmall : R ≤ 1/4
                · by_cases hheight : (m : ℝ)*R^2 ≤ 1
                  · exact ink_spots_small_cutoff hE hEb hEQ heta heta1 hR hsmall m hm hheight hs
                  · have hlarge : 1/16 ≤ (m : ℝ)*R^2 := by linarith only [hheight]
                    have hbound := trivial_large_height
                      (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
                      (ENNReal.toReal_nonneg (a := volume (F ∩ unitCylinder d))) hCV
                      (delay_multiplier_ge_one hm) (density_factor_bounds d heta heta1).1 hlarge
                    have hmono := ENNReal.toReal_mono (volume_cylinder_pos_ne_top _ zero_lt_one).2
                      (measure_mono hEQ)
                    exact hmono.trans (by simpa only [mul_assoc, unitCylinder] using hbound)
                · have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
                  have hlarge : 1/16 ≤ (m : ℝ)*R^2 := by nlinarith
                  have hbound := trivial_large_height
                    (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
                    (ENNReal.toReal_nonneg (a := volume (F ∩ unitCylinder d))) hCV
                    (delay_multiplier_ge_one hm) (density_factor_bounds d heta heta1).1 hlarge
                  have hmono := ENNReal.toReal_mono (volume_cylinder_pos_ne_top _ zero_lt_one).2
                    (measure_mono hEQ)
                  exact hmono.trans (by simpa only [mul_assoc, unitCylinder] using hbound)
              refine ⟨c, C, hc, hc1, hC, ?_⟩
              intro m hm eta r0 heta heta1 hr0 hr01 P0 R hR E F hEb hFb hE hF hEF hstack
              let phi := kineticAffine P0 R
              let Ep := phi ⁻¹' E
              let Fp := phi ⁻¹' F
              let Q := backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1
              have hEp : MeasurableSet Ep := measurableSet_kineticAffine_preimage P0 R hE
              have hFp : MeasurableSet Fp := measurableSet_kineticAffine_preimage P0 R hF
              have hEpF : Ep ⊆ Fp ∩ Q := by
                intro P hP
                have hh := hEF hP
                exact ⟨hh.1, (kineticAffine_mem_cylinder P0 P hR).mp hh.2⟩
              have hfactor : 0 < R ^ (4 * d + 2) := pow_pos hR _
              have hphiInj : Function.Injective phi :=
                (kineticAffineHomeomorph P0 R hR.ne').injective
              have hphiF : phi '' Fp = F :=
                (kineticAffineHomeomorph P0 R hR.ne').toEquiv.image_preimage F
              have hphiQ : phi '' Q = backwardCylinder P0 R :=
                kineticAffine_image_unitCylinder P0 hR
              have hphiE : phi '' Ep = E := (kineticAffineHomeomorph P0 R hR.ne').toEquiv.image_preimage E
              have hphiFQ : phi '' (Fp ∩ Q) = F ∩ backwardCylinder P0 R := by
                rw [image_inter hphiInj, hphiF, hphiQ]
              have hlocal (P : KineticPoint d) (r : ℝ) (hr : 0 < r)
                  (hsub : backwardCylinder P r ⊆ Q)
                  (hdense : (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
                    (volume (Ep ∩ backwardCylinder P r)).toReal) :
                  r < r0 ∧ forwardStack P r m ⊆ Fp := by
                have himage := kineticAffine_image_cylinder P0 P R r hR hr
                have hsubp : backwardCylinder (phi P) (R * r) ⊆ backwardCylinder P0 R := by
                  rw [← himage, ← kineticAffine_image_unitCylinder P0 hR]
                  exact image_mono hsub
                have hinter : phi '' (Ep ∩ backwardCylinder P r) =
                    E ∩ backwardCylinder (phi P) (R * r) := by
                  rw [image_inter hphiInj, hphiE, himage]
                have hdensep : (1 - eta) *
                    (volume (backwardCylinder (phi P) (R * r))).toReal ≤
                      (volume (E ∩ backwardCylinder (phi P) (R * r))).toReal := by
                  rw [← hinter, ← himage, volume_affine_image_toReal P0 hR,
                    volume_affine_image_toReal P0 hR]
                  nlinarith only [mul_le_mul_of_nonneg_left hdense hfactor.le]
                obtain ⟨hsmall, hforward⟩ := hstack (phi P) (R * r) (mul_pos hR hr) hsubp hdensep
                refine ⟨?_, ?_⟩
                · nlinarith only [hsmall, hR]
                · intro Z hZ
                  apply hforward
                  have _h_xinl_2 : kineticAffine P0 R '' forwardStack P r m =
                  forwardStack (kineticAffine P0 R P) (R * r) m := by
                    rw [← kineticAffine_image_forwardStack P hr m, image_image, ← Function.comp_def,
                      kineticAffine_comp,
                      kineticAffine_image_forwardStack _ (mul_pos hR hr) m]
                  rw [← _h_xinl_2]
                  exact ⟨Z, hZ, rfl⟩
              have hbound := hink m hm eta r0 heta heta1 hr0 hr01 Ep Fp
                (isBounded_kineticAffine_preimage P0 hR.ne' hEb)
                (isBounded_kineticAffine_preimage P0 hR.ne' hFb)
                hEp.nullMeasurableSet hFp.nullMeasurableSet hEpF hlocal
              have hvolE := volume_affine_image_toReal P0 hR Ep
              have hvolF := volume_affine_image_toReal P0 hR (Fp ∩ Q)
              rw [hphiE] at hvolE
              rw [hphiFQ] at hvolF
              rw [hvolE, hvolF]
              nlinarith only [mul_le_mul_of_nonneg_left hbound hfactor.le]
            obtain ⟨eta, m, delta, eps, heta, heta1, hm, ha, ha1, hdelt, hdelt1,
              heps, heps1, hscaled, hsigma, hnear, hstack⟩ : ∃ (eta : ℝ) (m : ℕ) (delta eps : ℝ),
              0 < eta ∧ eta < 1 ∧ 0 < m ∧
              0 < (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) ∧
              (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) < 1 ∧
              0 < delta ∧ delta < 1 ∧ 0 < eps ∧ eps < 1 ∧
              kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps ''
                referenceRegion d m (referenceBound m) ⊆
                  backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
              closure (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' samplingCylinder d m) ⊆
                backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
              (∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
                ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
                ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P0 r) ⊆ O →
                ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
                  IsAdmissibleSupersolution A O p C_A u →
                  (1 - eta) * (volume (backwardCylinder P0 r)).toReal ≤
                    (volume ({Z | ell ≤ u Z} ∩ backwardCylinder P0 r)).toReal →
                  ∀ Z ∈ kineticAffine P0 r '' cap d, (3 / 4 : ℝ) * ell ≤ u Z) ∧
              (∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
                ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
                ∀ O : Set (KineticPoint d), IsOpen O →
                  closure (kineticAffine P0 r '' stackComparisonRegion d m) ⊆ O →
                ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
                  IsAdmissibleSupersolution A O p C_A u →
                  (1 - eta) * (volume (backwardCylinder P0 r)).toReal ≤
                    (volume ({Z | ell ≤ u Z} ∩ backwardCylinder P0 r)).toReal →
                  ∀ Z ∈ forwardStack P0 r m, delta * ell ≤ u Z) := by
              obtain ⟨eta, heta, heta1, hnear⟩ : ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
      ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
          (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
      ∀ P ∈ kineticAffine P₀ R '' cap d, (3 / 4 : ℝ) * ell ≤ u P := by
                obtain ⟨C, hC⟩ : ∃ C₁ : ℝ, ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
                    ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
                    ∀ (P₀ : KineticPoint d) (R ell eta : ℝ),
                      0 < R → 0 ≤ ell → 0 < eta → eta < 1 →
                    ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
                    ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
                      IsAdmissibleSupersolution A O p C_A u →
                      (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
                        (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
                    ∀ P ∈ kineticAffine P₀ R '' cap d, (1 - C₁ * eta ^ (1 / p)) * ell ≤ u P := by
                  cases d with
                  | zero => omega
                  | succ n =>
                    obtain ⟨C₁, _, hC₁⟩ := near_full_with_nonneg_constant (n + 1) Lam p C_A hp
                    exact ⟨C₁, hC₁⟩
                let B := max C 0
                let delta := 1 / (4 * (B + 1))
                let eta := min (1 / 2 : ℝ) (delta ^ p)
                have hB : 0 ≤ B := le_max_right _ _
                have hden : 0 < 4 * (B + 1) := by positivity
                have hdelta : 0 < delta := one_div_pos.mpr hden
                have hp0 := lt_of_lt_of_le zero_lt_one hp
                have heta : 0 < eta := lt_min (by norm_num) (Real.rpow_pos_of_pos hdelta _)
                have heta1 : eta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
                have hroot : eta ^ (1 / p) ≤ delta := by
                  calc
                    _ ≤ (delta ^ p) ^ (1 / p) := Real.rpow_le_rpow heta.le
                      (min_le_right _ _) (one_div_nonneg.mpr hp0.le)
                    _ = delta := by rw [← Real.rpow_mul hdelta.le]; simp [hp0.ne']
                have hsmall : B * delta ≤ 1 / 4 := by
                  change B * (1 / (4 * (B + 1))) ≤ 1 / 4
                  rw [mul_one_div, div_le_iff₀ hden]
                  linarith only [hB]
                have hCsmall : C * eta ^ (1 / p) ≤ 1 / 4 :=
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg heta.le _)).trans
                    ((mul_le_mul_of_nonneg_left hroot hB).trans hsmall)
                refine ⟨eta, heta, heta1, ?_⟩
                intro lam hlam hLam A hA P₀ R ell hR hell O hO hQO u hu0 hu hdensity P hP
                exact (mul_le_mul_of_nonneg_right (by linarith only [hCsmall]) hell).trans
                  (hC lam hlam hLam A hA P₀ R ell eta hR hell heta heta1 O hO hQO u hu0 hu hdensity P hP)
              obtain ⟨m, hm, ha, ha1⟩ : ∃ m : ℕ, 0 < m ∧ 0 < (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) ∧
                  (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) < 1 := by
                obtain ⟨m, hm⟩ := exists_nat_gt ((1-c*eta)/(c*eta))
                have hce := mul_pos hc heta
                have hf : 0 < 1-c*eta ∧ 1-c*eta < 1 := by
                    constructor <;> nlinarith

                  /- An integer height makes the ink-spots multiplier contractive. -/
                have hmpos := (div_pos hf.1 hce).trans hm
                have hmn : 0 < m := by exact_mod_cast hmpos
                refine ⟨m, hmn, mul_pos (div_pos (by linarith) hmpos) hf.1, ?_⟩
                have hmul := (div_lt_iff₀ hce).mp hm
                have heq : (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) =
                    (((m : ℝ)+1)*(1-c*eta))/(m : ℝ) := by ring
                rw [heq]
                apply (div_lt_iff₀ hmpos).mpr
                nlinarith
              obtain ⟨delta, hdelta, hdelta1, hstack⟩ : ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 r '' stackComparisonRegion d m) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (∀ Z ∈ kineticAffine P0 r '' cap d, (3 / 4 : ℝ) * ell ≤ u Z) →
        ∀ P ∈ forwardStack P0 r m, delta * ell ≤ u P := by
                let M := (m : ℝ) + 1
                have hM : 0 < M := by dsimp only [M]; positivity
                have hacc : 0 < stackAcceleration m := by unfold stackAcceleration; positivity
                obtain ⟨c, hc, hc1, hprop⟩ := propagation_dimensionless d hd lam Lam
                  (1 / (32 * M)) (stackAcceleration m * Real.sqrt M)
                  (1 / (1024 * M ^ (3 / 2 : ℝ))) (1 / (16 * Real.sqrt M))
                  hlam hLam (by positivity) (by
                    apply (div_le_one (by positivity : 0 < 32 * M)).mpr
                    dsimp only [M]
                    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
                    linarith only [hm]) (by positivity) (by positivity) (by positivity)
                refine ⟨(3 / 4 : ℝ) * c, by positivity, by linarith only [hc1], ?_⟩
                intro p C_A hp A hA P0 r ell hr hell O hO hregion u hnonneg hu hcap P hP
                obtain ⟨x, v, hsk, _, _, hxP, hvP, hTlo, hThi, hcapCorr, hfullCorr⟩ : ∃ x v : ℝ → PDE.Vec d,
                    IsSkeleton x v ((384*((m : ℝ)+2)+32)/r)
                      (-(r^2/32)) (P.time-stackStartTime P0 r) ∧
                    x 0 = stackStartPosition P0 r ∧ v 0 = P0.velocity ∧
                    x (P.time-stackStartTime P0 r) = P.position ∧
                    v (P.time-stackStartTime P0 r) = P.velocity ∧
                    r^2/8 ≤ P.time-stackStartTime P0 r ∧
                    P.time-stackStartTime P0 r ≤ ((m : ℝ)+1)*r^2 ∧
                    corridor (stackStartTime P0 r) (-(r^2/32)) 0 (r^3/(2*8^3)) (r/16) x v ⊆
                      kineticAffine P0 r '' cap d ∧
                    corridor (stackStartTime P0 r) (-(r^2/32)) (P.time-stackStartTime P0 r)
                      (r^3/(2*8^3)) (r/16) x v ⊆ kineticAffine P0 r '' stackComparisonRegion d m := by
                    obtain ⟨hlo, hhi, -, -⟩ := stack_endpoint_data P0 P hr m hP
                    obtain ⟨x, v, hsk, hx0, hv0, hxT, hvT, hleft, hb⟩ : ∃ x v : ℝ → PDE.Vec d,
                        IsSkeleton x v (stackAcceleration m/r) (-(r^2/32)) (stackTravelTime P0 P r) ∧
                        x 0 = stackStartPosition P0 r ∧ v 0 = P0.velocity ∧
                        x (stackTravelTime P0 P r) = P.position ∧
                        v (stackTravelTime P0 P r) = P.velocity ∧
                        (∀ s ≤ 0, x s = stackStartPosition P0 r+s • P0.velocity ∧ v s = P0.velocity) ∧
                        (∀ s ∈ Icc (-(r^2/32)) (stackTravelTime P0 P r),
                          PDE.vecEuclideanNorm (x s-stackStartPosition P0 r-s • P0.velocity) ≤
                            stackPathBound m*r^3 ∧
                          PDE.vecEuclideanNorm (v s-P0.velocity) ≤ stackPathBound m*r) := by
                      obtain ⟨hlo, hhi, hpos, hvel⟩ := stack_endpoint_data P0 P hr m hP
                      let T := stackTravelTime P0 P r
                      have hT := lt_of_lt_of_le (by positivity) hlo
                      let xh := hermitePosition T (stackStartPosition P0 r) P0.velocity P.position P.velocity
                      let vh := hermiteVelocity T (stackStartPosition P0 r) P0.velocity P.position P.velocity
                      let H := 6*PDE.vecEuclideanNorm
                        (P.position-stackStartPosition P0 r-T • P0.velocity)/T^2+
                        4*PDE.vecEuclideanNorm (P.velocity-P0.velocity)/T
                      have hsk : IsSkeleton xh vh H 0 T := hermite_isSkeleton hT _ _ _ _
                      have hH : 0 ≤ H := by
                        have hn₁ := PDE.vecEuclideanNorm_nonneg
                          (P.position-stackStartPosition P0 r-T • P0.velocity)
                        have hn₂ := PDE.vecEuclideanNorm_nonneg (P.velocity-P0.velocity)
                        dsimp [H]
                        positivity
                      let x := extendPosition xh vh 0 T hT.le
                      let v := extendVelocity vh 0 T hT.le
                      have hleft (s : ℝ) (hs : s ≤ 0) :
                          x s = stackStartPosition P0 r+s • P0.velocity ∧ v s = P0.velocity := by
                        constructor
                        · dsimp [x]
                          rw [extendPosition_left xh vh hT.le hs]
                          simp only [xh, vh, hermitePosition_zero, hermiteVelocity_zero, sub_zero]
                        · dsimp [v, extendVelocity]
                          rw [projIcc_of_le_left hT.le hs]
                          exact hermiteVelocity_zero _ _ _ _ _
                      refine ⟨x, v, skeleton_mono_bound
                        (extendPosition_isSkeleton hT.le hH hsk _ _)
                        (stack_hermite_acceleration hr m hlo _ _ _ _ hpos hvel),
                        (by simpa using (hleft 0 le_rfl).1), (hleft 0 le_rfl).2, ?_, ?_, hleft, ?_⟩
                      · dsimp [x]
                        rw [extendPosition_eq hT.le hsk (right_mem_Icc.mpr hT.le)]
                        exact hermitePosition_end hT.ne' _ _ _ _
                      · dsimp [v]
                        rw [extendVelocity_eq vh hT.le (right_mem_Icc.mpr hT.le)]
                        exact hermiteVelocity_end hT.ne' _ _ _ _
                      · intro s hs
                        by_cases h : s ≤ 0
                        · rw [(hleft s h).1, (hleft s h).2]
                          simp only [add_sub_cancel_left, sub_self]
                          rw [PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl]
                          constructor <;> dsimp [stackPathBound] <;> positivity
                        · have hs' : s ∈ Icc 0 T := ⟨(not_le.mp h).le, hs.2⟩
                          dsimp [x, v]
                          rw [extendPosition_eq hT.le hsk hs', extendVelocity_eq vh hT.le hs']
                          exact stack_hermite_bounds hr m hlo hhi _ _ _ _ hpos hvel hs'
                    have _h_xinl_0 : corridor (stackStartTime P0 r) (-(r^2/32)) (stackTravelTime P0 P r) (r^3/(2*8^3)) (r/16) x v ⊆ kineticAffine P0 r '' stackComparisonRegion d m := by
                      intro Z hZ
                      apply (mem_kineticAffine_image_iff P0 Z hr.ne' _).mpr
                      have hsq := pow_pos hr 2
                      have hcube := pow_pos hr 3
                      obtain ⟨hx, hv⟩ := hb _ hZ.1
                      have hrel : relativePosition P0 Z =
                          (Z.position-x (Z.time-stackStartTime P0 r))+
                            (x (Z.time-stackStartTime P0 r)-stackStartPosition P0 r-
                              (Z.time-stackStartTime P0 r) • P0.velocity) := by
                        have _h_xinl_0 (P0 : KineticPoint d) (r s z) : z-P0.position-(stackStartTime P0 r+s-P0.time) • P0.velocity = z-stackStartPosition P0 r-s • P0.velocity := by
                          ext i
                          simp only [stackStartTime, stackStartPosition, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
                          ring
                        rw [← _h_xinl_0]
                        ext i
                        simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                        ring
                      have hn := PDE.vecEuclideanNorm_add_le
                        (Z.position-x (Z.time-stackStartTime P0 r))
                        (x (Z.time-stackStartTime P0 r)-stackStartPosition P0 r-
                          (Z.time-stackStartTime P0 r) • P0.velocity)
                      rw [← hrel] at hn
                      have hvn := PDE.vecEuclideanNorm_add_le
                        (Z.velocity-v (Z.time-stackStartTime P0 r))
                        (v (Z.time-stackStartTime P0 r)-P0.velocity)
                      rw [sub_add_sub_cancel] at hvn
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · change -2 < (Z.time-P0.time)/r^2
                        apply (lt_div_iff₀ hsq).mpr
                        have := hZ.1.1
                        dsimp [stackStartTime] at this
                        nlinarith
                      · change (Z.time-P0.time)/r^2 < (m : ℝ)+1
                        apply (div_lt_iff₀ hsq).mpr
                        have := hZ.1.2
                        dsimp [stackStartTime] at this
                        nlinarith
                      · rw [inverse_position_norm P0 Z hr]
                        apply (div_lt_iff₀ hcube).mpr
                        have := hZ.2.1
                        norm_num at this
                        nlinarith only [hn, hx, this, hcube]
                      · rw [inverse_velocity_norm P0 Z hr]
                        apply (div_lt_iff₀ hr).mpr
                        have := hZ.2.2
                        nlinarith only [hvn, hv, this, hr]
                    exact ⟨x, v, hsk, hx0, hv0, hxT, hvT, hlo, hhi,
                      initial_corridor_subset_cap P0 hr x v hleft,
                      _h_xinl_0⟩

                  /- The same fixed comparison region encloses both reference closures. -/
                obtain ⟨hscaleTime, hscaleH, hscaleX, hscaleV⟩ : (1 / (32 * ((m : ℝ) + 1))) * (((m : ℝ) + 1) * r ^ 2) = r ^ 2 / 32 ∧
                    (stackAcceleration m * Real.sqrt ((m : ℝ) + 1)) /
                      Real.sqrt (((m : ℝ) + 1) * r ^ 2) = stackAcceleration m / r ∧
                    (1 / (1024 * (((m : ℝ) + 1) ^ (3 / 2 : ℝ)))) *
                      (((m : ℝ) + 1) * r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 / (2 * 8 ^ 3) ∧
                    (1 / (16 * Real.sqrt ((m : ℝ) + 1))) *
                      Real.sqrt (((m : ℝ) + 1) * r ^ 2) = r / 16 := by
                  have hM : 0 < (m : ℝ) + 1 := by positivity
                  have hs : Real.sqrt ((m : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
                  have hp : ((m : ℝ) + 1) ^ (3 / 2 : ℝ) ≠ 0 :=
                    (Real.rpow_pos_of_pos hM _).ne'
                  have hsqrt : Real.sqrt (((m : ℝ) + 1) * r ^ 2) =
                      Real.sqrt ((m : ℝ) + 1) * r := by
                    rw [Real.sqrt_mul hM.le, Real.sqrt_sq_eq_abs, abs_of_pos hr]
                  have hpow : (((m : ℝ) + 1) * r ^ 2) ^ (3 / 2 : ℝ) =
                      ((m : ℝ) + 1) ^ (3 / 2 : ℝ) * r ^ 3 := by
                    rw [Real.mul_rpow hM.le (sq_nonneg r), ← Real.rpow_natCast r 2,
                      ← Real.rpow_mul hr.le]
                    norm_num
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · field_simp
                  · rw [hsqrt]
                    field_simp
                  · rw [hpow]
                    norm_num
                    field_simp
                  · rw [hsqrt]
                    field_simp
                have hT1 := mul_pos hM (sq_pos_of_pos hr)
                have hPO : P ∈ O := by
                  have hpoint : P ∈ corridor (stackStartTime P0 r) (-(r ^ 2 / 32))
                      (P.time - stackStartTime P0 r) (r ^ 3 / (2 * 8 ^ 3)) (r / 16) x v := by
                    refine ⟨⟨by linarith only [hTlo, sq_pos_of_pos hr], le_rfl⟩, ?_, ?_⟩
                    · rw [hxP, sub_self]
                      norm_num [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
                      positivity
                    · rw [hvP, sub_self]
                      norm_num [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
                      positivity
                  exact hregion (subset_closure (hfullCorr hpoint))
                have hprop' := hprop (M * r ^ 2) hT1 p C_A hp A hA O hO
                  (stackStartTime P0 r) P hPO
                rw [neg_mul, hscaleTime, hscaleH, hscaleX, hscaleV] at hprop'
                have htlo : r ^ 2 / 32 ≤ P.time - stackStartTime P0 r := by
                  linarith only [hTlo, sq_pos_of_pos hr]
                have hbound := hprop' htlo hThi x v (by simpa only [stackAcceleration] using hsk) hxP hvP
                  (fun Q hQ => hregion (subset_closure (hfullCorr hQ))) ((3 / 4 : ℝ) * ell)
                  (mul_nonneg (by norm_num) hell) u hnonneg hu
                  (fun Q hQ ht => hcap Q (hcapCorr ⟨⟨hQ.1.1, sub_nonpos.mpr ht⟩, hQ.2⟩))
                convert hbound using 1
                ring
              obtain ⟨eps, heps, heps1, _, _, _, _, hscaled, hsigma⟩ : ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
                  IsOpen (referenceRegion d m (referenceBound m)) ∧
                  Bornology.IsBounded (referenceRegion d m (referenceBound m)) ∧
                  closure (samplingCylinder d m) ⊆ referenceRegion d m (referenceBound m) ∧
                  backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ⊆
                    referenceRegion d m (referenceBound m) ∧
                  kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps ''
                    referenceRegion d m (referenceBound m) ⊆
                    backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
                  closure (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' samplingCylinder d m) ⊆
                    backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
                have hL := referenceBound_large m
                obtain ⟨eps, heps, heps1, himage⟩ := exists_buffered_reference_scale d m
                  (lt_trans (by norm_num) hL)
                have hsigma := sampling_closure_subset_reference d m hL
                refine ⟨eps, heps, heps1, isOpen_referenceRegion d m _,
                  isBounded_referenceRegion d m (le_of_lt (lt_trans (by norm_num) hL)), hsigma,
                  unitCylinder_subset_reference d m, himage, ?_⟩
                let e := kineticAffineHomeomorph (⟨0, 0, 0⟩ : KineticPoint d) eps heps.ne'
                change closure (e '' samplingCylinder d m) ⊆ _
                rw [← e.image_closure]
                exact (image_mono hsigma).trans himage
              refine ⟨eta, m, delta, eps, heta, heta1, hm, ha, ha1, hdelta, hdelta1,
                heps, heps1, hscaled, hsigma, hnear lam hlam hLam, ?_⟩
              intro A hA P0 r ell hr hell O hO hregion u hnonneg hu hdensity
              have hQO : closure (backwardCylinder P0 r) ⊆ O := by
                apply (closure_mono ?_).trans hregion
                rw [← kineticAffine_image_unitCylinder P0 hr]
                apply image_mono
                exact subset_closure.trans (stackComparisonRegion_geometry d m).2.2.1
              exact hstack p C_A hp A hA P0 r ell hr hell O hO hregion u hnonneg hu
                (hnear lam hlam hLam A hA P0 r ell hr hell O hO hQO u hnonneg hu hdensity)
            let a := (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta)
            let V := (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal
            have hV : 0 < V := ENNReal.toReal_pos
              (volume_cylinder_pos_ne_top _ zero_lt_one).1.ne'
              (volume_cylinder_pos_ne_top _ zero_lt_one).2
            refine ⟨eps, heps, heps1,
              kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps (samplingCenter d m),
              eps, heps, ?_, ?_⟩
            · rw [← physical_sampling_image _ heps m]
              exact hsigma
            intro beta hbeta _hbeta1
            obtain ⟨N, hN, _, r0, hr0, hr01, herror⟩ : ∃ N : ℕ, 1 ≤ N ∧ a⁻¹ ^ N * beta > 1 - eta ∧
      ∃ r0 : ℝ, 0 < r0 ∧ r0 < 1 ∧
        (C * (m : ℝ) * r0 ^ 2 / V) * (∑ k ∈ Finset.range N, a⁻¹ ^ k) <
          a⁻¹ ^ N * beta - (1 - eta) := by
              have hq : 1 < a⁻¹ := (one_lt_inv₀ ha).mpr ha1
              obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 - eta) / beta) hq
              let N := n + 1
              have hN : 1 ≤ N := by dsimp only [N]; omega
              have hn' := pow_le_pow_right₀ hq.le (Nat.le_succ n)
              have hbig : 1 - eta < a⁻¹ ^ N * beta := by
                exact (div_lt_iff₀ hbeta).mp (hn.trans_le hn')
              let S := ∑ k ∈ Finset.range N, a⁻¹ ^ k
              have hS : 0 < S := Finset.sum_pos (fun k _ => pow_pos (inv_pos.mpr ha) k)
                (Finset.nonempty_range_iff.mpr (by omega))
              let D := (C * (m : ℝ) / V) * S
              have hD : 0 < D := mul_pos (div_pos (mul_pos hC (Nat.cast_pos.mpr hm)) hV) hS
              let gap := a⁻¹ ^ N * beta - (1 - eta)
              have hgap : 0 < gap := sub_pos.mpr hbig
              let r0 := min (1 / 2 : ℝ) (Real.sqrt (gap / (2 * D)))
              have hr0 : 0 < r0 := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
              have hr01 : r0 < 1 := (min_le_left _ _).trans_lt (by norm_num)
              have hrsq : r0 ^ 2 ≤ gap / (2 * D) := by
                have he := (sq_le_sq₀ hr0.le (Real.sqrt_nonneg _)).mpr (min_le_right _ _)
                rwa [Real.sq_sqrt (by positivity : 0 ≤ gap / (2 * D))] at he
              have hhalf : D * r0 ^ 2 ≤ gap / 2 := by
                have he := mul_le_mul_of_nonneg_left hrsq hD.le
                apply he.trans_eq
                field_simp
              refine ⟨N, hN, hbig, r0, hr0, hr01, ?_⟩
              have heq : (C * (m : ℝ) * r0 ^ 2 / V) * S = D * r0 ^ 2 := by
                dsimp only [D]
                ring
              rw [heq]
              exact hhalf.trans_lt (by dsimp only [gap] at hgap ⊢; linarith only [hgap])
            obtain ⟨cmac, hcmac, _, hmacro⟩ :=
              exists_physical_macroscopic_cap_constant d hd lam Lam hlam hLam m r0 hr0 hr01
            let kappa := (3 / 4 : ℝ) * cmac * delta ^ N
            refine ⟨kappa, by dsimp only [kappa]; positivity, ?_⟩
            intro A hA P0 R hR O hO hdomain u hnonneg hu hdensity
            let scale := R * eps
            have hscale : 0 < scale := mul_pos hR heps
            let G := kineticAffine P0 scale '' referenceRegion d m (referenceBound m)
            let S := kineticAffine P0 scale (samplingCenter d m)
            let Sigma := backwardCylinder S scale
            have hGO : closure G ⊆ O := by
              apply (closure_mono ?_).trans hdomain
              rw [← kineticAffine_image_unitCylinder P0 hR]
              rintro _ ⟨P, hP, rfl⟩
              have hcomp := congrFun (kineticAffine_comp P0 (⟨0, 0, 0⟩ : KineticPoint d) R eps) P
              have hzero : kineticAffine P0 R (⟨0, 0, 0⟩ : KineticPoint d) = P0 := by
                simp only [kineticAffine, mul_zero, smul_zero, zero_smul, add_zero]
              rw [hzero] at hcomp
              exact ⟨kineticAffine ⟨0, 0, 0⟩ eps P, hscaled ⟨P, hP, rfl⟩, hcomp⟩
            have hSigmaO : closure Sigma ⊆ O :=
              (physical_sampling_closure_subset P0 hscale m).trans hGO
            have hSigmaG : Sigma ⊆ G := by
              dsimp only [Sigma, S]
              rw [← physical_sampling_image P0 hscale m]
              exact image_mono (subset_closure.trans
                (sampling_closure_subset_reference d m (referenceBound_large m)))
            have hGb : Bornology.IsBounded G := by
              have hE := (isBounded_referenceRegion d m (by linarith only [referenceBound_large m]))
              obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
              exact (hK.image (continuous_kineticAffine P0 scale)).isBounded.subset (image_mono hEK)
            have hGopen : IsOpen G := (kineticAffineHomeomorph P0 scale hscale.ne').isOpenMap _
              (isOpen_referenceRegion d m (referenceBound m))
            have hSigmab : Bornology.IsBounded Sigma :=
              (isCompact_closure_backwardCylinder S scale hscale).isBounded.subset subset_closure
            have hSigmaMeas : MeasurableSet Sigma := (isOpen_cylinder S scale).measurableSet
            let E := fun j : ℕ => {P | delta ^ j ≤ u P} ∩ Sigma
            let F := fun j : ℕ => {P | delta ^ (j + 1) ≤ u P} ∩ G
            have hEMeas (j : ℕ) : MeasurableSet (E j) := measurableSet_superlevel_inter hO
              hSigmaMeas (subset_closure.trans hSigmaO) hu.1 _
            have hFMeas (j : ℕ) : MeasurableSet (F j) := measurableSet_superlevel_inter hO
              hGopen.measurableSet (subset_closure.trans hGO) hu.1 _
            have hEb (j : ℕ) : Bornology.IsBounded (E j) :=
              superlevel_inter_isBounded hSigmab u _
            have hFb (j : ℕ) : Bornology.IsBounded (F j) :=
              superlevel_inter_isBounded hGb u _
            have hdown (j : ℕ) : delta ^ (j + 1) ≤ delta ^ j := by
              rw [pow_succ]
              exact mul_le_of_le_one_right (pow_nonneg hdelt.le j) hdelt1.le
            have hEF (j : ℕ) : E j ⊆ F j ∩ Sigma := by
              intro P hP
              exact ⟨⟨(hdown j).trans hP.1, hSigmaG hP.2⟩, hP.2⟩
            have hFQ (j : ℕ) : F j ∩ Sigma = E (j + 1) := by
              ext P
              constructor
              · intro hP; exact ⟨hP.1.1, hP.2⟩
              · intro hP; exact ⟨⟨hP.1, hSigmaG hP.2⟩, hP.2⟩
            have hlocalLevel (j : ℕ) (Q : KineticPoint d) (r : ℝ)
                (hsub : backwardCylinder Q r ⊆ Sigma) :
                E j ∩ backwardCylinder Q r = {Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r := by
              ext Z
              constructor
              · intro hZ; exact ⟨hZ.1.1, hZ.2⟩
              · intro hZ; exact ⟨⟨hZ.1, hsub hZ.2⟩, hZ.2⟩
            have hmacDensity (j : ℕ) (Q : KineticPoint d) (r : ℝ) (hr : 0 < r)
                (hsub : backwardCylinder Q r ⊆ Sigma) (hbig : r0 * scale ≤ r)
                (hden : (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
                  (volume ({Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r)).toReal) :
                ∀ Z ∈ backwardCylinder P0 scale, (3 / 4 : ℝ) * cmac * delta ^ j ≤ u Z := by
              have hQO : closure (backwardCylinder Q r) ⊆ O := (closure_mono hsub).trans hSigmaO
              have hcap := hnear A hA Q r (delta ^ j) hr (pow_nonneg hdelt.le j)
                O hO hQO u hnonneg hu hden
              have hb := hmacro p C_A hp A hA P0 scale hscale O hO hGO u hnonneg hu
                Q r ((3 / 4 : ℝ) * delta ^ j) hr hbig hsub (by positivity) hcap
              intro Z hZ
              convert hb Z hZ using 1
              ring
            have hSigmaVol : (volume Sigma).toReal = scale ^ (4 * d + 2) * V := by
              dsimp only [Sigma]
              rw [← kineticAffine_image_unitCylinder S hscale, volume_affine_image_toReal S hscale]
            have hSigmaVolPos : 0 < (volume Sigma).toReal := by rw [hSigmaVol]; positivity
            have hphysicalSigma : kineticAffine P0 R ''
                backwardCylinder
                  (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps (samplingCenter d m)) eps = Sigma := by
              rw [← physical_sampling_image _ heps m]
              rw [image_image]
              have hc0 : kineticAffine P0 R ∘ kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps =
                  kineticAffine P0 scale := by
                rw [kineticAffine_comp]
                congr 1
                ext i <;> simp [kineticAffine]
              rw [← Function.comp_def, hc0, physical_sampling_image P0 hscale m]
            rw [hphysicalSigma] at hdensity
            have htarget : backwardCylinder P0 (eps * R) = backwardCylinder P0 scale := by
              dsimp only [scale]
              rw [mul_comm eps R]
            rw [htarget]
            by_cases hmac : ∃ j : ℕ, j < N ∧ ∃ (Q : KineticPoint d) (r : ℝ),
                0 < r ∧ backwardCylinder Q r ⊆ Sigma ∧ r0 * scale ≤ r ∧
                (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
                  (volume ({Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r)).toReal
            · obtain ⟨j, hj, Q, r, hr, hsub, hbig, hden⟩ := hmac
              have hpow : delta ^ N ≤ delta ^ j :=
                pow_le_pow_of_le_one hdelt.le hdelt1.le hj.le
              intro Z hZ
              exact (mul_le_mul_of_nonneg_left hpow (by positivity :
                0 ≤ (3 / 4 : ℝ) * cmac)).trans (hmacDensity j Q r hr hsub hbig hden Z hZ)
            let e := fun j : ℕ => (volume (E j)).toReal / (volume Sigma).toReal
            let L0 := C * (m : ℝ) * r0 ^ 2 / V
            have hzero : beta ≤ e 0 := by
              apply (le_div_iff₀ hSigmaVolPos).mpr
              simpa only [E, pow_zero] using hdensity
            have hstep (j : ℕ) (hj : j < N) : e j ≤ a * (e (j + 1) + L0) := by
              have hcriterion (Q : KineticPoint d) (r : ℝ) (hr : 0 < r)
                  (hsub : backwardCylinder Q r ⊆ Sigma)
                  (hden : (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
                    (volume (E j ∩ backwardCylinder Q r)).toReal) :
                  r < r0 * scale ∧ forwardStack Q r m ⊆ F j := by
                rw [hlocalLevel j Q r hsub] at hden
                have hsmall : r < r0 * scale := by
                  by_contra hs
                  exact hmac ⟨j, hj, Q, r, hr, hsub, le_of_not_gt hs, hden⟩
                refine ⟨hsmall, ?_⟩
                have hcomp : kineticAffine Q r '' stackComparisonRegion d m ⊆
      kineticAffine P0 scale '' referenceRegion d m (referenceBound m) := by
                  let P := Q
                  let Q := kineticAffineInverse P0 scale P
                  have hQ := physical_sampling_subcylinder P0 P hscale hr m hsub
                  have hi := sampling_comparison_image_subset m Q (div_pos hr hscale) hQ
                  have hc : kineticAffine P r = kineticAffine P0 scale ∘ kineticAffine Q (r / scale) := by
                    rw [kineticAffine_comp, kineticAffine_apply_inverse P0 hscale.ne',
                      mul_div_cancel₀ r hscale.ne']
                  rw [hc]
                  rintro Z ⟨Y, hY, rfl⟩
                  exact ⟨kineticAffine Q (r / scale) Y, hi ⟨Y, hY, rfl⟩, rfl⟩
                have hcompO := (closure_mono hcomp).trans hGO
                have hvis := hstack A hA Q r (delta ^ j) hr (pow_nonneg hdelt.le j)
                  O hO hcompO u hnonneg hu hden
                intro Z hZ
                exact ⟨by simpa only [mem_ofPred_eq, pow_succ, mul_comm delta] using hvis Z hZ,
                  hcomp (forwardStack_subset_comparison Q hr m hZ)⟩
              have hb := hink m hm eta r0 heta heta1 hr0 hr01 S scale hscale
                (E j) (F j) (hEb j) (hFb j) (hEMeas j) (hFMeas j) (hEF j) hcriterion
              rw [hFQ j] at hb
              apply (div_le_iff₀ hSigmaVolPos).mpr
              have heq : a * (e (j + 1) + L0) * (volume Sigma).toReal =
                  a * ((volume (E (j + 1))).toReal + scale ^ (4 * d + 2) * C * (m : ℝ) * r0 ^ 2) := by
                dsimp only [e, L0]
                rw [hSigmaVol]
                field_simp
              rw [heq]
              exact hb
            have hterminal : a⁻¹ ^ N * beta - L0 * (∑ k ∈ Finset.range N, a⁻¹ ^ k) ≤ e N := by
                have hrec : ∀ j < N, a⁻¹ * e j - L0 ≤ e (j + 1) := by
                  intro j hj
                  have he := mul_le_mul_of_nonneg_left (hstep j hj) (inv_nonneg.mpr ha.le)
                  rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at he
                  linarith only [he]
                have hbound : ∀ n, n ≤ N →
                    a⁻¹ ^ n * beta - L0 * (∑ k ∈ Finset.range n, a⁻¹ ^ k) ≤ e n := by
                  intro n
                  induction n with
                  | zero => intro _; simpa only [pow_zero, one_mul, Finset.range_zero,
                      Finset.sum_empty, mul_zero, sub_zero] using hzero
                  | succ n ih =>
                    intro hn
                    have he := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hn))
                      (inv_nonneg.mpr ha.le)
                    have hr := hrec n (Nat.lt_of_succ_le hn)
                    rw [ladder_power_sum_succ, pow_succ]
                    nlinarith only [he, hr]
                exact hbound N le_rfl

              /- Fixing N first allows the source leakage radius to be chosen strictly positive and small. -/
            have hterminalDense : 1 - eta < e N := by linarith only [hterminal, herror]
            have hdenSigma : (1 - eta) * (volume Sigma).toReal ≤
                (volume ({Z | delta ^ N ≤ u Z} ∩ Sigma)).toReal :=
              (le_div_iff₀ hSigmaVolPos).mp hterminalDense.le
            have hbigSigma : r0 * scale ≤ scale :=
              (mul_le_mul_of_nonneg_right hr01.le hscale.le).trans_eq (one_mul scale)
            exact hmacDensity N S scale hscale Subset.rfl hbigSigma hdenSigma
          refine ⟨theta, ht, ht1, S, r, hr, hS, ?_⟩
          intro beta hb hb1
          obtain ⟨kappa, hk, hbound⟩ := hbeta beta hb hb1
          refine ⟨kappa, hk, ?_⟩
          intro A hmeas hsym hlo hhi
          exact hbound A ⟨hmeas, hsym, hlo, hhi⟩
        obtain ⟨k, hk, hbound⟩ := hbeta (1 / 2) (by norm_num) (by norm_num)
        refine ⟨theta, S, r, min k 1, ht, ht1, hr, lt_min hk (by norm_num),
          min_le_right _ _, hS, ?_⟩
        intro A hA O hO P0 R hR hQ u hu b h hh hupper hdense P hP
        have hcont : ContinuousOn u O := by
          have heq : (-(fun P => -u P)) = u := by funext P; simp only [Pi.neg_apply, neg_neg]
          rw [← heq]
          exact hu.1.neg
        have hlocal : ∀ epsilon : ℝ, 0 < epsilon → u P ≤ b - min k 1 * h + epsilon := by
          intro epsilon hepsilon
          let U := O ∩ {Z | u Z < b + epsilon}
          have hU : IsOpen U := hcont.isOpen_inter_preimage hO isOpen_Iio
          have hQU : closure (backwardCylinder P0 R) ⊆ U := by
            intro Z hZ
            exact ⟨hQ hZ, (hupper Z hZ).trans_lt (by linarith only [hepsilon])⟩
          let w := fun Z => h⁻¹ * (-u Z) + (b + epsilon) / h
          have hw : IsAdmissibleSupersolution A U p C_A w :=
            (admissible_pos_affine hu h⁻¹ ((b + epsilon) / h) (inv_pos.mpr hh)).mono
              inter_subset_left
          have hn : ∀ Z ∈ U, 0 ≤ w Z := by
            intro Z hZ
            dsimp only [w]
            rw [inv_mul_eq_div, ← add_div]
            have hz : u Z < b + epsilon := hZ.2
            exact div_nonneg (by linarith only [hz]) hh.le
          have hlevels : {Z | u Z ≤ b - h} ∩ kineticAffine P0 R '' backwardCylinder S r ⊆
              {Z | 1 ≤ w Z} ∩ kineticAffine P0 R '' backwardCylinder S r := by
            intro Z hZ
            refine ⟨?_, hZ.2⟩
            change 1 ≤ h⁻¹ * (-u Z) + (b + epsilon) / h
            rw [inv_mul_eq_div, ← add_div]
            apply (le_div_iff₀ hh).mpr
            have hz : u Z ≤ b - h := hZ.1
            linarith only [hz, hepsilon]
          have hfinite : volume (kineticAffine P0 R '' backwardCylinder S r) ≠ ⊤ := by
            have hinside : kineticAffine P0 R '' backwardCylinder S r ⊆ backwardCylinder P0 R := by
              rw [← kineticAffine_image_unitCylinder P0 hR]
              exact image_mono (subset_closure.trans hS)
            exact ne_top_of_le_ne_top (Covering.volume_cylinder_pos_ne_top P0 hR).2
              (measure_mono hinside)
          have hdenw :=
            hdense.trans (ENNReal.toReal_mono
              (ne_top_of_le_ne_top hfinite (measure_mono inter_subset_right)) (measure_mono hlevels))
          have hkP := hbound A hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 P0 R hR U hU hQU
            w hn hw hdenw P hP
          have hkP' : min k 1 ≤ w P := (min_le_left _ _).trans hkP
          dsimp only [w] at hkP'
          rw [inv_mul_eq_div, ← add_div, le_div_iff₀ hh] at hkP'
          linarith only [hkP']
        apply le_of_forall_pos_le_add
        exact hlocal
      refine ⟨theta, 1 - kappa / 2, ht, ht1, by linarith only [hk1],
        by linarith only [hk], ?_⟩
      intro A hA O hO P0 R hR hQ u hu
      let Q := backwardCylinder P0 R
      let Qsmall := backwardCylinder P0 (theta * R)
      let Sigma := kineticAffine P0 R '' backwardCylinder S r
      have hQc := isCompact_closure_backwardCylinder P0 R hR
      have huc : ContinuousOn u (closure Q) := hu.1.1.mono hQ
      have habc := hQc.bddAbove_image huc
      have hbbc := hQc.bddBelow_image huc
      have hab : BddAbove (u '' Q) := habc.mono (image_mono subset_closure)
      have hbb : BddBelow (u '' Q) := hbbc.mono (image_mono subset_closure)
      have hsub : Qsmall ⊆ Q := backwardCylinder_radius_mono P0 (mul_pos ht hR)
        ((mul_le_mul_of_nonneg_right ht1.le hR.le).trans_eq (one_mul R))
      have hne := backwardCylinder_nonempty P0 (mul_pos ht hR)
      have hosc : 0 ≤ oscillationOn u Q := oscillationOn_nonneg
        (backwardCylinder_nonempty P0 hR) hab hbb
      by_cases hz : oscillationOn u Q = 0
      · have hm := oscillationOn_mono hne hsub hab hbb
        change oscillationOn u Qsmall ≤ (1 - kappa / 2) * oscillationOn u Q
        simpa only [hz, mul_zero] using hm
      have hpos : 0 < oscillationOn u Q := lt_of_le_of_ne hosc (Ne.symm hz)
      let M := sSup (u '' Q)
      let m := sInf (u '' Q)
      let half := oscillationOn u Q / 2
      have hhalf : 0 < half := div_pos hpos (by norm_num)
      have hM (P : KineticPoint d) (hP : P ∈ closure Q) : u P ≤ M :=
        closure_values_le_sup huc hab hP
      have hm (P : KineticPoint d) (hP : P ∈ closure Q) : m ≤ u P :=
        inf_le_closure_values huc hbb hP
      have hmid : M - half = m + half := by
        dsimp only [half, oscillationOn, M, m]
        ring
      have _h_xinl_0 : (1 / 2 : ℝ) * (volume Sigma).toReal ≤ (volume ({P | u P ≤ (M - half)} ∩ Sigma)).toReal ∨
          (1 / 2 : ℝ) * (volume Sigma).toReal ≤ (volume ({P | (M - half) ≤ u P} ∩ Sigma)).toReal := by
        let b := (M - half)
        have heq : ({P | u P ≤ b} ∩ Sigma) ∪ ({P | b ≤ u P} ∩ Sigma) = Sigma := by
          ext P
          simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
          · intro h
            rcases le_total (u P) b with hb | hb
            · exact Or.inl ⟨hb, h⟩
            · exact Or.inr ⟨hb, h⟩
        have hb := measureReal_union_le (μ := volume) ({P | u P ≤ b} ∩ Sigma) ({P | b ≤ u P} ∩ Sigma)
        rw [heq] at hb
        change (volume Sigma).toReal ≤ (volume ({P | u P ≤ b} ∩ Sigma)).toReal +
          (volume ({P | b ≤ u P} ∩ Sigma)).toReal at hb
        by_cases h : (1 / 2 : ℝ) * (volume Sigma).toReal ≤ (volume ({P | u P ≤ b} ∩ Sigma)).toReal
        · exact Or.inl h
        · exact Or.inr (by linarith only [hb, h])
      rcases _h_xinl_0 with hlo | hhi
      · have himproved := hupper A hA O hO P0 R hR hQ u hu.2 M half hhalf hM hlo
        have hb := oscillationOn_le hne
          (fun P hP => hm P (subset_closure (hsub hP))) himproved
        apply hb.trans_eq
        dsimp only [half, oscillationOn, M, m]
        ring
      · have hneg : IsAdmissibleSupersolution A O p C_A (fun P => -(-u P)) := by
          simpa only [neg_neg] using hu.1
        have hupperneg (P : KineticPoint d) (hP : P ∈ closure Q) : -u P ≤ -m :=
          neg_le_neg (hm P hP)
        have hlevels : {P | M - half ≤ u P} = {P | -u P ≤ -m - half} := by
          ext P
          simp only [mem_ofPred_eq]
          rw [hmid]
          constructor <;> intro h <;> linarith only [h]
        rw [hlevels] at hhi
        have himproved := hupper A hA O hO P0 R hR hQ (fun P => -u P)
          hneg (-m) half hhalf hupperneg hhi
        have hb := oscillationOn_le (a := m + kappa * half) (b := M) hne
          (fun P hP => by have hh := himproved P hP; linarith only [hh])
          (fun P hP => hM P (subset_closure (hsub hP)))
        apply hb.trans_eq
        dsimp only [half, oscillationOn, M, m]
        ring
    let alpha := min 1 (Real.log (1 / q) / Real.log (1 / theta))
    obtain ⟨ha, ha1, hqa⟩ := source_holder_exponent ht ht1 hq hq1
    refine ⟨alpha, theta ^ (-alpha), ha, ha1, ?_⟩
    intro A hA O hO P0 R rho hR hrho hrhoR hQ u hu
    have hcompact := isCompact_closure_backwardCylinder P0 R hR
    have hcont := hu.1.1.mono hQ
    have hab := (hcompact.bddAbove_image hcont).mono (image_mono subset_closure)
    have hbb := (hcompact.bddBelow_image hcont).mono (image_mono subset_closure)
    have hosc := oscillationOn_nonneg (backwardCylinder_nonempty P0 hR) hab hbb
    have hrad (n : ℕ) : 0 < theta ^ n * R := mul_pos (pow_pos ht n) hR
    have hrads (n : ℕ) : theta ^ n * R ≤ R :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht1.le) hR.le).trans_eq (one_mul R)
    have hsub (n : ℕ) := backwardCylinder_radius_mono P0 (hrad n) (hrads n)
    have hiter (n : ℕ) : oscillationOn u (backwardCylinder P0 (theta ^ n * R)) ≤
        q ^ n * oscillationOn u (backwardCylinder P0 R) := by
      induction n with
      | zero => simp only [pow_zero, one_mul, le_refl]
      | succ n ih =>
        have hc := hcontract A hA O hO P0 (theta ^ n * R) (hrad n)
          ((closure_mono (hsub n)).trans hQ) u hu
        have he : theta * (theta ^ n * R) = theta ^ (n + 1) * R := by rw [pow_succ]; ring
        rw [he] at hc
        have hb := hc.trans (mul_le_mul_of_nonneg_left ih hq.le)
        exact hb.trans_eq (by rw [pow_succ]; ring)
    have hx := div_pos hrho hR
    have hx1 : rho / R ≤ 1 := (div_le_one hR).mpr hrhoR
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hx hx1 ht ht1
    have hsmall : rho ≤ theta ^ n * R := (div_le_iff₀ hR).mp hnhi
    have hm := oscillationOn_mono (backwardCylinder_nonempty P0 hrho)
      (backwardCylinder_radius_mono P0 hrho hsmall)
      (hab.mono (image_mono (hsub n))) (hbb.mono (image_mono (hsub n)))
    have hpower := contraction_power_le_scale_power ht hq.le ha hqa n hnlo
    exact (hm.trans (hiter n)).trans (mul_le_mul_of_nonneg_right hpower hosc)
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro A hmeas hsym hlo hhi Omega hOmega u _hbounded hu K _hKO hK R0 hR0 hQ
  have hA : FullElliptic lam Lam A := ⟨hmeas, hsym, hlo, hhi⟩
  let E := holderNeighbourhood R0 K
  obtain ⟨hclosed, hcompact⟩ := holder_neighbourhood_compact K hK R0 hR0
  have hEO : closure E ⊆ Omega := by
    rw [hclosed]
    intro Z hZ
    simp only [mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact hQ P hP hZ
  have hcont := hu.1.1.mono hEO
  have habc := hcompact.bddAbove_image hcont
  have hbbc := hcompact.bddBelow_image hcont
  have hab := habc.mono (image_mono subset_closure)
  have hbb := hbbc.mono (image_mono subset_closure)
  have hcenter (P : KineticPoint d) (hP : P ∈ K) : P ∈ closure E := by
    rw [hclosed]
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP,
      Covering.top_mem_closure_cylinder P (by positivity : 0 < 2 * R0)
        (PDE.center_mem_euclideanBall _ (by positivity))⟩⟩
  have hpair (P : KineticPoint d) (hP : P ∈ K) (P' : KineticPoint d) (hP' : P' ∈ K)
      (ht : P.time ≤ P'.time) :
      |u P - u P'| ≤ C * oscillationOn u E * (quasiDistance P P' / R0) ^ alpha := by
    have hne : E.Nonempty := by
      obtain ⟨Z, hZ⟩ := backwardCylinder_nonempty P (by positivity : 0 < 2 * R0)
      exact ⟨Z, mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hZ⟩⟩⟩
    have hosc := oscillationOn_nonneg hne hab hbb
    have hosccl :=
      oscillationOn_closure hne hcompact hcont
    have hdelta := quasiDistance_nonneg P P'
    by_cases hz : quasiDistance P P' = 0
    · have heq := (quasiDistance_eq_zero_iff P P').mp hz
      rw [congrArg u heq, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le hosc)
        (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)
    have hdpos : 0 < quasiDistance P P' := lt_of_le_of_ne hdelta (Ne.symm hz)
    by_cases hnear : quasiDistance P P' ≤ R0
    · have hR : 0 < 2 * R0 := by positivity
      have hdistR : quasiDistance P P' ≤ 2 * R0 := by linarith only [hnear, hR0]
      obtain ⟨hpcl, hp'cl⟩ := pair_mem_closed_later_cylinder P P' ht hdpos
      have hsmallO :=
        (closure_mono (backwardCylinder_radius_mono P' hdpos hdistR)).trans (hQ P' hP')
      have hcsmall := isCompact_closure_backwardCylinder P' _ hdpos
      have hucsmall := hu.1.1.mono hsmallO
      have habsmall := hcsmall.bddAbove_image hucsmall
      have hbbsmall := hcsmall.bddBelow_image hucsmall
      have habdiff := abs_sub_le_oscillationOn habsmall hbbsmall hpcl hp'cl
      rw [oscillationOn_closure (backwardCylinder_nonempty P' hdpos) hcsmall hucsmall]
        at habdiff
      have hd := hdecay A hA Omega hOmega P' (2 * R0) (quasiDistance P P')
        hR hdpos hdistR (hQ P' hP') u hu
      have hbigE : backwardCylinder P' (2 * R0) ⊆ E := fun Z hZ =>
        mem_iUnion.mpr ⟨P', mem_iUnion.mpr ⟨hP', hZ⟩⟩
      have hbigosc := oscillationOn_nonneg (backwardCylinder_nonempty P' hR)
        (hab.mono (image_mono hbigE)) (hbb.mono (image_mono hbigE))
      have hoscmono := oscillationOn_mono (backwardCylinder_nonempty P' hR) hbigE hab hbb
      have hratio : quasiDistance P P' / (2 * R0) ≤ quasiDistance P P' / R0 :=
        div_le_div_of_nonneg_left hdelta hR0 (by linarith only [hR0])
      have hpower := Real.rpow_le_rpow (div_nonneg hdelta hR.le) hratio ha.le
      have hcoeff : D * (quasiDistance P P' / (2 * R0)) ^ alpha ≤
          C * (quasiDistance P P' / R0) ^ alpha :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (div_nonneg hdelta hR.le) _)).trans
          (mul_le_mul_of_nonneg_left hpower hC.le)
      have hb := (habdiff.trans hd).trans
        (mul_le_mul_of_nonneg_right hcoeff hbigosc)
      have hb' := hb.trans (mul_le_mul_of_nonneg_left hoscmono
        (mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)))
      exact hb'.trans_eq (by ring)
    · have hbase := abs_sub_le_oscillationOn habc hbbc (hcenter P hP) (hcenter P' hP')
      rw [hosccl] at hbase
      have hratio : 1 ≤ quasiDistance P P' / R0 :=
        (one_le_div hR0).mpr (le_of_not_ge hnear)
      have hpower : 1 ≤ (quasiDistance P P' / R0) ^ alpha := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hratio ha.le
      have hCpower : C ≤ C * (quasiDistance P P' / R0) ^ alpha := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hC.le
      have hcoeff :=
        (le_max_right D 1).trans hCpower
      have hb := mul_le_mul_of_nonneg_right hcoeff hosc
      rw [one_mul] at hb
      exact hbase.trans (hb.trans_eq (by ring))
  intro P hP P' hP'
  rcases le_total P.time P'.time with ht | ht
  · exact hpair P hP P' hP' ht
  · have hb := hpair P' hP' P hP ht
    simpa only [abs_sub_comm, quasiDistance_symm P' P] using hb

end HypoellipticAleksandrov.KineticAleksandrov
