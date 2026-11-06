module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullSourceNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullScaling
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityMinimum
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffRawHessian
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Analysis.Normed.Group.Bounded
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffAffine
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # The source nearly-full superlevel estimate with uniform constants -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped MatrixOrder
open Parabolic
open scoped ENNReal

/- The source near-full estimate, with the nonnegative constant needed by its threshold. -/
theorem near_full_with_nonneg_constant (d : ℕ) (Lam p C_A : ℝ) (hp : 1 ≤ p) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell eta : ℝ),
        0 < R → 0 ≤ ell → 0 < eta → eta < 1 →
      ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
          (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
      ∀ P ∈ kineticAffine P₀ R '' cap d, (1 - C₁ * eta ^ (1 / p)) * ell ≤ u P := by
  obtain ⟨f, hf, hrange, hcap, _, hsupport⟩ : ∃ f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      (∀ P ∈ closure (cap d), f (KineticPoint.equivProd d P) = 1) ∧
      HasCompactSupport f ∧
      tsupport f ⊆ (KineticPoint.equivProd d) ''
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    let e := KineticPoint.homeomorphProd d
    have hK := (isCompact_closure_cap d).image e.continuous
    have hQ : IsOpen (e '' backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) :=
      e.isOpen_image.mpr (isOpen_backwardCylinder _ _ (by norm_num))
    have hKQ := image_mono (f := e) (cap_compact_inside d).2
    obtain ⟨U, hU, hKU, hUQ, hUc⟩ :=
      exists_open_between_and_isCompact_closure hK hQ hKQ
    obtain ⟨f, hf, hrange, hsupport, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU hK.isClosed hKU
    refine ⟨f, hf, fun z => hrange (mem_range_self z), ?_, ?_, ?_⟩
    · intro P hP
      exact (hone _).mp (mem_image_of_mem e hP)
    · change IsCompact (closure (Function.support f))
      rw [hsupport]
      exact hUc
    · change closure (Function.support f) ⊆ _
      rw [hsupport]
      exact hUQ
  obtain ⟨C₀, hC₀, hop⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ lam : ℝ, 0 < lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
      ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
        |backwardOperator A (scaledUnitCutoff f P₀ R ell) P| ≤ C₀ * ell * (R ^ 2)⁻¹ := by
    obtain ⟨C₀, hC₀, hbound⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Q ∈ closure
        (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1),
        ∀ B : PDE.Mat d, (∀ i j, |B i j| ≤ |Lam|) →
          |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
            matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ C₀ := by
        let K := closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
        let S : Set (PDE.Mat d) := {B | ∀ i j, B i j ∈ Icc (-|Lam|) |Lam|}
        have hK : IsCompact K := isCompact_closure_backwardCylinder _ 1 (by norm_num)
        have hS : IsCompact S :=
          isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
        have _h_xinl_0 : Continuous (fun z : KineticPoint d × PDE.Mat d => fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0)) - matrixContraction z.2 (sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity)) := by
          have hD : Continuous (fun z : KineticPoint d × PDE.Mat d =>
              fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0))) :=
            (continuous_unitCutoffTransport hf).comp continuous_fst
          apply hD.sub
          have hH : Continuous (fun z : KineticPoint d × PDE.Mat d =>
              sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity) :=
            (continuous_unitCutoffVelocityHessian hf).comp continuous_fst
          unfold matrixContraction
          apply continuous_finsetSum
          intro i _
          apply continuous_finsetSum
          intro j _
          exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).mul
            ((continuous_apply j).comp ((continuous_apply i).comp hH))
        obtain ⟨M, hM⟩ := (hK.prod hS).exists_bound_of_continuousOn
          _h_xinl_0.continuousOn
        refine ⟨max M 0, le_max_right _ _, fun Q hQ B hB => ?_⟩
        have hBS : B ∈ S := fun i j => abs_le.mp (hB i j)
        exact (show |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
          matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ M by
            simpa only [Real.norm_eq_abs] using hM (Q, B) ⟨hQ, hBS⟩).trans (le_max_left _ _)

      /- Ellipticity and exact affine jets yield the source cutoff bound with uniform constants. -/
    refine ⟨C₀, hC₀, fun lam hlam A hA P₀ R ell hR hell => ?_⟩
    have hQ := isOpen_backwardCylinder P₀ R hR
    filter_upwards [ae_restrict_mem hQ.measurableSet,
      ae_restrict_of_ae hA.2.2.1, ae_restrict_of_ae hA.2.2.2] with P hP hl hu
    have hunit : kineticAffineInverse P₀ R P ∈
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
      apply (kineticAffine_mem_cylinder P₀ _ hR).mp
      simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP
    have hB : ∀ i j, |fullKineticCoefficientAt A P i j| ≤ |Lam| :=
      fun i j =>
        (HypoellipticAleksandrov.abs_apply_le_of_loewner hlam hl hu i j).trans (le_abs_self Lam)
    have hb := hbound _ (subset_closure hunit) _ hB
    rw [scaledUnitCutoff_backwardOperator hf, abs_mul,
      abs_of_nonneg (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))]
    calc
      _ ≤ ell * (R ^ 2)⁻¹ * C₀ :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))
      _ = C₀ * ell * (R ^ 2)⁻¹ := by ring
  let V := (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal
  let C₁ := max C_A 0 * C₀ * V ^ (1 / p)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hCA : 0 ≤ max C_A 0 := le_max_right _ _
  refine ⟨C₁, mul_nonneg (mul_nonneg hCA hC₀) (Real.rpow_nonneg hV _), ?_⟩
  intro lam hlam hLam A hA P₀ R ell eta hR hell heta heta1 O hO hQO u hu0 hu hdensity P hP
  let Q := backwardCylinder P₀ R
  let psi := scaledUnitCutoff f P₀ R ell
  have hQU : Q ⊆ O := subset_closure.trans hQO
  have hEll : 0 < lam ∧ lam ≤ Lam := ⟨hlam, hLam⟩
  have hEta : eta ∈ Ioo (0 : ℝ) 1 := ⟨heta, heta1⟩
  have hB : 0 ≤ C₀ * ell * (R ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg hC₀ hell) (inv_nonneg.mpr (sq_nonneg R))
  have hopQ := hop lam hEll.1 A hA P₀ R ell hR hell
  have hsmooth : IsSmoothNear (scaledUnitCutoff f P₀ R ell) (closure Q) := by
    let E := (closure Q)
    refine ⟨univ, isOpen_univ, subset_univ E, ?_⟩
    exact (contDiff_const.mul (hf.comp (contDiff_kineticAffineInverse_prod P₀ R))).contDiffOn
  have hpsi := hsmooth.continuousOn
  have huQ := hu.1.mono hQU
  have _h_xinl_0 : Measurable (backwardOperator A (scaledUnitCutoff f P₀ R ell)) := by
    have hA := hA.1
    have hT := ((continuous_unitCutoffTransport hf).comp
      (continuous_kineticAffineInverse P₀ R)).measurable
    have hH := ((continuous_unitCutoffVelocityHessian hf).comp
      (continuous_kineticAffineInverse P₀ R)).measurable
    have hC : Measurable (fun P => matrixContraction (fullKineticCoefficientAt A P)
        (sliceHessian (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
          (kineticAffineInverse P₀ R P).velocity)) := by
      unfold matrixContraction
      apply Finset.measurable_sum
      intro i _
      apply Finset.measurable_sum
      intro j _
      exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH))
    convert ((measurable_const (a := ell * (R ^ 2)⁻¹)).mul (hT.sub hC)) using 1
    funext P
    exact scaledUnitCutoff_backwardOperator hf A P₀ P R ell
  have hnorm := localizedSource_norm_le_sublevel_volume A
    (isOpen_backwardCylinder P₀ R hR) (volume_backwardCylinder_lt_top P₀ hR).ne
    (hpsi.mono subset_closure) huQ
    _h_xinl_0
    ell (C₀ * ell * (R ^ 2)⁻¹) p hB hp
    (fun T _ => (scaledUnitCutoff_bounds hrange P₀ R ell hell T).2) hopQ
  have hdens : (volume ({P | u P < ell} ∩ backwardCylinder P₀ R)).toReal ≤
      eta * (volume (backwardCylinder P₀ R)).toReal := by
    have hu := hu.1
    let Q := backwardCylinder P₀ R
    let E := {P | u P < ell} ∩ Q
    have hE : MeasurableSet E := by
      have ho : IsOpen ((O ∩ u ⁻¹' Iio ell) ∩ Q) :=
        (hu.isOpen_inter_preimage hO isOpen_Iio).inter
        (isOpen_backwardCylinder P₀ R hR)
      have heq : E = (O ∩ u ⁻¹' Iio ell) ∩ Q := by
        ext P
        change (u P < ell ∧ P ∈ Q) ↔ ((P ∈ O ∧ u P < ell) ∧ P ∈ Q)
        exact ⟨fun h => ⟨⟨hQU h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
      rw [heq]
      exact ho.measurableSet
    have hdiff : Q \ E = {P | ell ≤ u P} ∩ Q := by
      ext P
      simp only [E, mem_sdiff, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hP, h⟩
        exact ⟨le_of_not_gt (fun ht => h ⟨ht, hP⟩), hP⟩
      · rintro ⟨huP, hP⟩
        exact ⟨hP, fun h => (not_lt_of_ge huP) h.1⟩
    have hsum := measureReal_inter_add_sdiff (μ := volume) (s := Q) hE
      (volume_backwardCylinder_lt_top P₀ hR).ne
    have hQE : Q ∩ E = E := inter_eq_right.mpr inter_subset_right
    rw [hQE, hdiff] at hsum
    change (volume E).toReal ≤ eta * (volume Q).toReal
    change (volume E).toReal + (volume ({P | ell ≤ u P} ∩ Q)).toReal =
      (volume Q).toReal at hsum
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hrpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hdens
    (one_div_nonneg.mpr hp0.le)
  have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_left hrpow hB)
  have _h_xinl_0 : (volume (backwardCylinder P₀ R)).toReal =
      R ^ (4 * d + 2) *
        (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal := by
      rw [← kineticAffine_image_unitCylinder P₀ hR, volume_kineticAffine_image P₀ hR,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hR _).le]

    /- The comparison radius, cutoff inverse-square factor and source volume powers cancel. -/
  rw [_h_xinl_0,
    Real.mul_rpow hEta.1.le (mul_nonneg (pow_pos hR _).le hV),
    Real.mul_rpow (pow_pos hR _).le hV] at hnorm'
  have hscale : R ^ (2 - (4 * (d : ℝ) + 2) / p) * (R ^ 2)⁻¹ *
      (R ^ (4 * d + 2)) ^ (1 / p : ℝ) = 1 := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_neg hR.le,
      ← Real.rpow_natCast R (4 * d + 2), ← Real.rpow_mul hR.le,
      ← Real.rpow_add hR, ← Real.rpow_add hR]
    have heq : (2 - (4 * (d : ℝ) + 2) / p) + -(2 : ℝ) +
        ((4 * d + 2 : ℕ) : ℝ) * (1 / p) = 0 := by
      push_cast
      ring
    norm_num only [Nat.cast_ofNat]
    rw [heq, Real.rpow_zero]
  have hmul : max C_A 0 * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
      (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p) (volume.restrict Q)).toReal ≤
        C₁ * eta ^ (1 / p) * ell := by
    calc
      _ ≤ max C_A 0 * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (C₀ * ell * (R ^ 2)⁻¹ *
            (eta ^ (1 / p) * ((R ^ (4 * d + 2)) ^ (1 / p) * V ^ (1 / p)))) :=
        mul_le_mul_of_nonneg_left hnorm' (mul_nonneg hCA (Real.rpow_nonneg hR.le _))
      _ = C₁ * eta ^ (1 / p) * ell := by
        calc
          _ = (max C_A 0 * C₀ * V ^ (1 / p)) * eta ^ (1 / p) * ell *
              (R ^ (2 - (4 * (d : ℝ) + 2) / p) * (R ^ 2)⁻¹ *
                (R ^ (4 * d + 2)) ^ (1 / p)) := by ring
          _ = _ := by rw [hscale, mul_one]
  have hboundary : sSup ((fun T => max (psi T - u T) 0) '' kineticBoundary P₀ R) ≤ 0 := by
    apply csSup_le ((kineticBoundary_nonempty P₀ hR).image _)
    rintro _ ⟨T, hT, rfl⟩
    have hz := scaledUnitCutoff_boundary_eq_zero hsupport P₀ hR ell hT
    have hn := hu0 T (hQO hT.1)
    change max (scaledUnitCutoff f P₀ R ell T - u T) 0 ≤ 0
    rw [hz, zero_sub]
    exact max_le (neg_nonpos.mpr hn) le_rfl
  have hPunit : P ∈ Q := by
    obtain ⟨T, hT, rfl⟩ := hP
    exact (kineticAffine_mem_cylinder P₀ T hR).mpr
      ((cap_compact_inside d).2 (subset_closure hT))
  have hbounded := (isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image
    (hpsi.sub (hu.1.mono hQO))
  have hpoint := (le_csSup hbounded (mem_image_of_mem (fun T => psi T - u T)
    (subset_closure hPunit))).trans (hu.nonnegative_constant.2 P₀ R hR hQO psi hsmooth)
  have hplateau : psi P = ell := scaledUnitCutoff_eq_level hcap P₀ hR ell hP
  rw [hplateau] at hpoint
  change ell - u P ≤ _ at hpoint
  have hlast := hpoint.trans (add_le_add hboundary hmul)
  simp only [zero_add] at hlast
  linarith only [hlast]

/- The exact source near-full conditions, with its constant fixed before ellipticity data. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
