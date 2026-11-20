module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Compactness of norm-one idele classes

This module combines local compactness, the logarithmic unit lattice, and the
principal-idele norm formula to prove compactness of the norm-one subgroup of
the idele class group.
-/

open scoped Classical NumberField Pointwise RestrictedProduct NNReal
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The product of all local integral-unit groups, embedded in the finite
idele group. -/
def integralStructureMap :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletionIntegers K).units) → FiniteIdeleGroup K :=
  RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.adicCompletionIntegers K).units)
    Filter.cofinite

theorem range_integralStructureMap :
    Set.range (integralStructureMap (K := K)) =
      (integralSubgroup (K := K) : Set (FiniteIdeleGroup K)) := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩ v
    exact (u v).property
  · intro ha
    exact ⟨(fun v ↦ ⟨a v, ha v⟩), rfl⟩

/-- The everywhere integral finite ideles form a compact group. -/
theorem isCompact_integralSubgroup :
    IsCompact
      ((integralSubgroup (K := K) :
        Subgroup (FiniteIdeleGroup K)) : Set (FiniteIdeleGroup K)) := by
  have hlocal :
      ∀ v : HeightOneSpectrum (𝓞 K),
        CompactSpace (v.adicCompletionIntegers K).units := fun v => isCompact_iff_compactSpace.mp
      (isCompact_finiteLocalUnits K v)
  let (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace (v.adicCompletionIntegers K).units :=
    hlocal v
  rw [← range_integralStructureMap]
  unfold integralStructureMap
  simpa using
    isCompact_univ.image
      RestrictedProduct.isEmbedding_structureMap.continuous

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

/-- A compact annulus in one archimedean local multiplicative group. -/
def localAnnulus (w : InfinitePlace K) (B : ℝ) :
    Set w.Completionˣ :=
  {x | Real.exp (-B) ≤ ‖(x : w.Completion)‖ ∧
    ‖(x : w.Completion)‖ ≤ Real.exp B}

omit [NumberField K] in
theorem isCompact_localAnnulus (w : InfinitePlace K) (B : ℝ) :
    IsCompact (localAnnulus w B) := by
  have hnorm_two : ‖(2 : w.Completion)‖ = 2 := by
    calc
      _ =
          ‖NumberField.InfinitePlace.Completion.extensionEmbedding w
            (2 : w.Completion)‖ :=
        (Isometry.norm_map_of_map_zero
          (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w)
          (map_zero _) _).symm
      _ = 2 := by
        rw [map_ofNat]
        norm_num
  let : NontriviallyNormedField w.Completion :=
    NontriviallyNormedField.ofNormNeOne
      ⟨2, by
        intro h
        have hz : ‖(2 : w.Completion)‖ = 0 := by rw [h, norm_zero]
        rw [hnorm_two] at hz
        norm_num at hz,
       by rw [hnorm_two]; norm_num⟩
  let : ProperSpace w.Completion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
      w.Completion
  let A : Set w.Completion :=
    {x | Real.exp (-B) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp B}
  have hAclosed : IsClosed A := by
    exact isClosed_Icc.preimage continuous_norm
  have hAbounded : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.exp B, fun x hx ↦ hx.2⟩
  have hArange : A ⊆ Set.range (Units.val : w.Completionˣ → w.Completion) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      have hnonpos : Real.exp (-B) ≤ 0 := by
        simpa using hx.1
      exact (not_lt_of_ge hnonpos) (Real.exp_pos (-B))
    exact ⟨Units.mk0 x hx0, rfl⟩
  change IsCompact (Units.val ⁻¹' A)
  exact
    (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hArange).mpr
      (Metric.isCompact_iff_isClosed_bounded.mpr
        ⟨hAclosed, hAbounded⟩)

/-- A compact product of local archimedean annuli. -/
def annulus (B : ℝ) : Set (InfiniteIdeleGroup K) :=
  ContinuousMulEquiv.piUnits.symm ''
    Set.univ.pi (fun w : InfinitePlace K ↦ localAnnulus w B)

omit [NumberField K] in
theorem isCompact_annulus (B : ℝ) :
    IsCompact (annulus (K := K) B) := by
  apply IsCompact.image
  · exact isCompact_univ_pi fun w ↦ isCompact_localAnnulus w B
  · exact ContinuousMulEquiv.piUnits.symm.continuous

omit [NumberField K] in
theorem mem_annulus_iff (a : InfiniteIdeleGroup K) (B : ℝ) :
    a ∈ annulus (K := K) B ↔
      ∀ w : InfinitePlace K,
        Real.exp (-B) ≤
            ‖((component w a : w.Completionˣ) : w.Completion)‖ ∧
          ‖((component w a : w.Completionˣ) : w.Completion)‖ ≤
            Real.exp B := by
  constructor
  · rintro ⟨u, hu, rfl⟩ w
    exact hu w (Set.mem_univ w)
  · intro ha
    refine ⟨ContinuousMulEquiv.piUnits a, ?_, ?_⟩
    · intro w _
      exact ha w
    · exact ContinuousMulEquiv.piUnits.symm_apply_apply a

/-- The archimedean norm is continuous. -/
theorem continuous_archimedeanNorm :
    Continuous (archimedeanNorm (K := K)) := by
  classical
  rw [show (archimedeanNorm :
      InfiniteIdeleGroup K → ℝ≥0ˣ) =
      fun a ↦ ∏ w : InfinitePlace K,
        nnnormUnitHom w.Completion (component w a) ^ w.mult by
    rfl]
  apply continuous_finsetProd
  intro w _
  apply Continuous.pow
  exact (continuous_nnnorm.units_map _).comp
    ((continuous_apply w).comp
      ContinuousMulEquiv.piUnits.continuous)

/-- The logarithms of the normalized archimedean absolute values, with the
distinguished place omitted as in Dirichlet's unit theorem. -/
def logNorm (a : InfiniteIdeleGroup K) :
    logSpace K :=
  fun w ↦ w.1.mult *
    Real.log ‖((component w.1 a : w.1.Completionˣ) : w.1.Completion)‖

@[simp]
theorem logNorm_mul (a b : InfiniteIdeleGroup K) :
    logNorm (a * b) = logNorm a + logNorm b := by
  ext w
  have ha :=
    norm_ne_zero_iff.mpr (component w.1 a).ne_zero
  have hb :=
    norm_ne_zero_iff.mpr (component w.1 b).ne_zero
  simp only [logNorm, Pi.add_apply, map_mul, Units.val_mul, norm_mul,
    Real.log_mul ha hb, mul_add]

/-- Ring-of-integers units, viewed as units of the number field. -/
def ringUnitToFieldUnit :
    (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K)

theorem norm_infiniteComponent_principalIdele (x : Kˣ)
    (w : InfinitePlace K) :
    ‖((component w (IdeleGroup.principalIdele K x).1 :
        w.Completionˣ) : w.Completion)‖ =
      w (x : K) := by
  change ‖(((WithAbs.equiv w.1).symm (x : K) :
    WithAbs w.1) : w.Completion)‖ = w (x : K)
  rw [NumberField.InfinitePlace.Completion.norm_coe,
    (WithAbs.equiv w.1).apply_symm_apply]

/-- On an algebraic integer unit, the archimedean idele log is exactly
Dirichlet's logarithmic embedding. -/
theorem logNorm_principalRingUnit (u : (𝓞 K)ˣ) :
    logNorm (IdeleGroup.principalIdele K
        (ringUnitToFieldUnit (K := K) u)).1 =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := by
  ext w
  rw [logNorm, logEmbedding_component,
    norm_infiniteComponent_principalIdele]
  rfl

theorem logNorm_component_le {r : ℝ} (a : InfiniteIdeleGroup K)
    (h : ‖logNorm a‖ ≤ r)
    (w : {w : InfinitePlace K //
      w ≠ w₀ (K := K)}) :
    |logNorm a w| ≤ r := by
  simpa using
    (norm_le_pi_norm (logNorm a) w).trans h

/-- If the total archimedean norm is one, the omitted logarithmic coordinate
is the negative sum of all the other coordinates. -/
theorem sum_logNorm_eq_neg_distinguished
    (a : InfiniteIdeleGroup K)
    (ha : archimedeanNorm a = 1) :
    ∑ w, logNorm a w =
      -(w₀ (K := K)).mult *
        Real.log
          ‖((component (w₀ (K := K)) a :
              (w₀ (K := K)).Completionˣ) :
            (w₀ (K := K)).Completion)‖ := by
  have hprod :
      ∏ w : InfinitePlace K,
          ‖((component w a : w.Completionˣ) : w.Completion)‖ ^ w.mult =
        1 := by
    simpa using (congrArg
        (fun z : ℝ≥0ˣ ↦ ((z : ℝ))) ha)
  have hsum :
      ∑ w : InfinitePlace K,
          w.mult *
            Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ = 0 := by
    calc
      _ =
          Real.log
            (∏ w : InfinitePlace K,
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ ^ w.mult) := by
              rw [Real.log_prod]
              · apply Finset.sum_congr rfl
                intro w _
                rw [Real.log_pow]
              · intro w _
                exact pow_ne_zero _ <|
                  norm_ne_zero_iff.mpr (component w a).ne_zero
      _ = 0 := by rw [hprod, Real.log_one]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀)] at hsum
  have hsum' :
      (∑ w : {w : InfinitePlace K // w ≠ w₀ (K := K)},
          w.1.mult *
            Real.log
              ‖((component w.1 a : w.1.Completionˣ) :
                w.1.Completion)‖) =
        -(w₀ (K := K)).mult *
          Real.log
            ‖((component (w₀ (K := K)) a :
                (w₀ (K := K)).Completionˣ) :
              (w₀ (K := K)).Completion)‖ := by
    simpa using
      (eq_neg_of_add_eq_zero_right hsum)
  simpa only [logNorm] using hsum'

/-- A norm bound in the logarithmic space bounds every local logarithm.
The harmless factor `#S∞` also covers the omitted coordinate. -/
theorem abs_log_norm_component_le
    {r : ℝ} (hr : 0 ≤ r) (a : InfiniteIdeleGroup K)
    (hlog : ‖logNorm a‖ ≤ r)
    (hnorm : archimedeanNorm a = 1)
    (w : InfinitePlace K) :
    |Real.log
        ‖((component w a : w.Completionˣ) : w.Completion)‖| ≤
      (Fintype.card (InfinitePlace K) : ℝ) * r := by
  have hmult :
      ∀ x : ℝ, 0 ≤ x → x ≤ w.mult * x := by
    intro x hx
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals
      rw [NumberField.InfinitePlace.mult]
      split_ifs <;> norm_num
  by_cases hw : w = w₀
  · have h := congrArg (‖·‖)
      (sum_logNorm_eq_neg_distinguished a hnorm).symm
    replace h := (le_of_eq h).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at h
    refine (le_trans ?_ h).trans ?_
    · rw [← hw]
      exact hmult _ (abs_nonneg _)
    · refine (Finset.sum_le_card_nsmul _ _ _
          (fun v _ ↦ logNorm_component_le a hlog v)).trans ?_
      rw [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hr
      exact_mod_cast
        (Fintype.card_subtype_le
          (fun w : InfinitePlace K ↦ w ≠ w₀))
  · have h := logNorm_component_le a hlog ⟨w, hw⟩
    rw [logNorm, abs_mul, Nat.abs_cast] at h
    refine (le_trans ?_ h).trans ?_
    · exact hmult _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul
        (Nat.one_le_cast.mpr Fintype.card_pos)
        le_rfl hr (Nat.cast_nonneg _)

/-- Exponentiating the preceding logarithmic estimate gives a compact
annulus containing the idele. -/
theorem mem_annulus_of_logNorm_le
    {r : ℝ} (hr : 0 ≤ r) (a : InfiniteIdeleGroup K)
    (hlog : ‖logNorm a‖ ≤ r)
    (hnorm : archimedeanNorm a = 1) :
    a ∈ annulus (K := K)
      ((Fintype.card (InfinitePlace K) : ℝ) * r) := by
  rw [mem_annulus_iff]
  intro w
  let B := (Fintype.card (InfinitePlace K) : ℝ) * r
  have hnpos :=
    norm_pos_iff.mpr (component w a).ne_zero
  have habs :
      -B ≤
          Real.log
            ‖((component w a : w.Completionˣ) :
              w.Completion)‖ ∧
        Real.log
            ‖((component w a : w.Completionˣ) :
              w.Completion)‖ ≤ B := by
    simpa using (abs_le.mp (abs_log_norm_component_le hr a hlog hnorm w))
  constructor
  · calc
      _ ≤
          Real.exp
            (Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖) :=
        Real.exp_le_exp.mpr habs.1
      _ = ‖((component w a : w.Completionˣ) :
            w.Completion)‖ :=
        Real.exp_log hnpos
  · calc
      _ =
          Real.exp
            (Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖) :=
        (Real.exp_log hnpos).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr habs.2

/-- A real basis obtained from the full unit lattice. -/
 def unitLatticeRealBasis :
    Module.Basis
      (Module.Free.ChooseBasisIndex ℤ
        (NumberField.Units.unitLattice K))
      ℝ (logSpace K) :=
  (Module.Free.chooseBasis ℤ
    (NumberField.Units.unitLattice K)).ofZLatticeBasis
      ℝ (NumberField.Units.unitLattice K)

/-- An explicit uniform logarithmic bound for representatives modulo the
ordinary unit lattice. -/
def logFundamentalBound : ℝ :=
  ∑ i, ‖unitLatticeRealBasis (K := K) i‖

theorem logFundamentalBound_nonneg :
    0 ≤ logFundamentalBound (K := K) :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Every archimedean idele can be multiplied by an algebraic integer unit
so that its logarithmic vector lies in a fixed bounded fundamental
parallelepiped. -/
theorem exists_ringUnit_logNorm_le (a : InfiniteIdeleGroup K) :
    ∃ u : (𝓞 K)ˣ,
      ‖logNorm
          (a * (IdeleGroup.principalIdele K
            (ringUnitToFieldUnit (K := K) u)).1)‖ ≤
        logFundamentalBound (K := K) := by
  let b := unitLatticeRealBasis (K := K)
  let f := ZSpan.floor b (logNorm a)
  have hf :
      (f : logSpace K) ∈ NumberField.Units.unitLattice K := by
    have hspan :
        Submodule.span ℤ (Set.range b) =
          NumberField.Units.unitLattice K := by
      dsimp [b, unitLatticeRealBasis]
      exact (Module.Free.chooseBasis ℤ
        (NumberField.Units.unitLattice K)).ofZLatticeBasis_span
          ℝ (NumberField.Units.unitLattice K)
    exact hspan.le f.property
  change (f : logSpace K) ∈
      Submodule.map
        (NumberField.Units.logEmbedding K).toIntLinearMap ⊤ at hf
  obtain ⟨u, -, hu⟩ := hf
  refine ⟨u.toMul⁻¹, ?_⟩
  have hinv :
      NumberField.Units.logEmbedding K
          (Additive.ofMul u.toMul⁻¹) =
        -f := by
    calc
      _ =
          -NumberField.Units.logEmbedding K u := by
            rw [← map_neg]
            rfl
      _ = -f := congrArg Neg.neg hu
  rw [logNorm_mul, logNorm_principalRingUnit, hinv,
    ← sub_eq_add_neg, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b (logNorm a)

end InfiniteIdeleGroup

namespace IdeleGroup

/-- A principal idele coming from a unit of the ring of integers is integral
at every finite place. -/
theorem principalRingUnit_mem_integralAtFinitePlaces
    (u : (𝓞 K)ˣ) :
    principalIdele K
        (InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u) ∈
      integralAtFinitePlaces (K := K) := by
  rw [← fractionalIdeal_ker, MonoidHom.mem_ker,
    fractionalIdeal_principalIdele]
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K u) =
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr u.isUnit,
    FractionalIdeal.coeIdeal_top]

theorem finite_absoluteNorm_eq_one_of_integral
    (a : FiniteIdeleGroup K)
    (ha : a ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    FiniteIdeleGroup.absoluteNorm a = 1 := by
  rw [FiniteIdeleGroup.absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  have hfrac :
      FiniteIdeleGroup.fractionalIdeal a = 1 := by
    rw [← MonoidHom.mem_ker,
      FiniteIdeleGroup.fractionalIdeal_ker]
    exact ha
  rw [hfrac, map_one]

/-- For an idele which is integral at all finite places, the global norm-one
condition is exactly the archimedean norm-one condition. -/
theorem archimedeanNorm_eq_one_of_normOne_integral
    (a : IdeleGroup K)
    (hnorm : a ∈ normOneSubgroup (K := K))
    (hintegral :
      a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    InfiniteIdeleGroup.archimedeanNorm a.1 = 1 := by
  change absoluteNorm a = 1 at hnorm
  rw [absoluteNorm_apply, (finite_absoluteNorm_eq_one_of_integral a.2 hintegral), one_mul] at hnorm
  exact inv_eq_one.mp hnorm

/-- The fixed compact set of norm-one ideles which are integral at every
finite place and logarithmically reduced modulo the ordinary units. -/
def compactIntegralNormOneSet : Set (IdeleGroup K) :=
  (InfiniteIdeleGroup.annulus (K := K)
      ((Fintype.card (InfinitePlace K) : ℝ) *
        InfiniteIdeleGroup.logFundamentalBound (K := K)) ×ˢ
    (FiniteIdeleGroup.integralSubgroup (K := K) :
      Set (FiniteIdeleGroup K))) ∩
  {a | InfiniteIdeleGroup.archimedeanNorm a.1 = 1}

theorem isCompact_compactIntegralNormOneSet :
    IsCompact (compactIntegralNormOneSet (K := K)) := by
  apply IsCompact.inter_right
  · exact
      (InfiniteIdeleGroup.isCompact_annulus
        ((Fintype.card (InfinitePlace K) : ℝ) *
          InfiniteIdeleGroup.logFundamentalBound)).prod
        (FiniteIdeleGroup.isCompact_integralSubgroup)
  · exact isClosed_singleton.preimage
      (InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst)

theorem mem_compactIntegralNormOneSet_iff (a : IdeleGroup K) :
    a ∈ compactIntegralNormOneSet (K := K) ↔
      a.1 ∈ InfiniteIdeleGroup.annulus (K := K)
          ((Fintype.card (InfinitePlace K) : ℝ) *
            InfiniteIdeleGroup.logFundamentalBound (K := K)) ∧
        a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) ∧
        InfiniteIdeleGroup.archimedeanNorm a.1 = 1 := by
  change
    ((a.1 ∈ InfiniteIdeleGroup.annulus
          ((Fintype.card (InfinitePlace K) : ℝ) *
            InfiniteIdeleGroup.logFundamentalBound) ∧
        a.2 ∈ FiniteIdeleGroup.integralSubgroup) ∧
      InfiniteIdeleGroup.archimedeanNorm a.1 = 1) ↔ _
  tauto

/-- A norm-one idele integral at every finite place is principal-equivalent
to an element of the fixed compact representative set. -/
theorem exists_compactIntegralNormOneSet_representative
    (a : IdeleGroup K)
    (hnorm : a ∈ normOneSubgroup (K := K))
    (hintegral :
      a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    ∃ b ∈ compactIntegralNormOneSet (K := K),
      QuotientGroup.mk' (principalSubgroup K) b =
        QuotientGroup.mk' (principalSubgroup K) a := by
  obtain ⟨u, hu⟩ :=
    InfiniteIdeleGroup.exists_ringUnit_logNorm_le a.1
  let p :=
    principalIdele K
      (InfiniteIdeleGroup.ringUnitToFieldUnit u)
  let b := a * p
  have hbIntegral := (integralAtFinitePlaces).mul_mem hintegral
      (principalRingUnit_mem_integralAtFinitePlaces u)
  have hpNorm := principalSubgroup_le_normOneSubgroup
      ⟨InfiniteIdeleGroup.ringUnitToFieldUnit u, rfl⟩
  have hbArch :=
    archimedeanNorm_eq_one_of_normOne_integral b ((normOneSubgroup).mul_mem hnorm hpNorm) hbIntegral
  refine ⟨b,
    (mem_compactIntegralNormOneSet_iff b).mpr
      ⟨(InfiniteIdeleGroup.mem_annulus_of_logNorm_le
        InfiniteIdeleGroup.logFundamentalBound_nonneg b.1 hu hbArch), hbIntegral, hbArch⟩, ?_⟩
  change
    (QuotientGroup.mk' (principalSubgroup K)) (a * p) =
      (QuotientGroup.mk' (principalSubgroup K)) a
  rw [map_mul]
  have hpOne :
      QuotientGroup.mk' (principalSubgroup K) p = 1 := by
    apply (QuotientGroup.eq_one_iff p).mpr
    exact
      ⟨InfiniteIdeleGroup.ringUnitToFieldUnit u, rfl⟩
  rw [hpOne]
  exact mul_one
    (QuotientGroup.mk' (principalSubgroup K) a)

section

variable (c : ClassGroup (𝓞 K))

/-- For every ordinary ideal class which occurs on a norm-one idele, choose
one such representative; use `1` for the (irrelevant) remaining classes. -/
 def normOneIdealClassRepresentative : IdeleGroup K :=
  if h : ∃ a : IdeleGroup K,
      a ∈ normOneSubgroup (K := K) ∧ idealClass a = c then
    Classical.choose h
  else
    1

private theorem normOneIdealClassRepresentative_mem :
    normOneIdealClassRepresentative (K := K) c ∈
      normOneSubgroup (K := K) := by
  rw [normOneIdealClassRepresentative]
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact (normOneSubgroup).one_mem

private theorem idealClass_normOneIdealClassRepresentative
    (h : ∃ a : IdeleGroup K,
      a ∈ normOneSubgroup (K := K) ∧ idealClass a = c) :
    idealClass (normOneIdealClassRepresentative (K := K) c) = c := by
  rw [normOneIdealClassRepresentative, dite_eq_left h]
  exact (Classical.choose_spec h).2

end

/-- The finite set of chosen norm-one representatives of ordinary ideal
classes. -/
def normOneIdealClassRepresentativeSet : Set (IdeleGroup K) :=
  Set.range (normOneIdealClassRepresentative (K := K))

theorem isCompact_normOneIdealClassRepresentativeSet :
    IsCompact (normOneIdealClassRepresentativeSet (K := K)) := by
  apply Set.Finite.isCompact
  exact Set.finite_range _

theorem normOneIdealClassRepresentativeSet_subset_normOne :
    normOneIdealClassRepresentativeSet (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  rintro _ ⟨c, rfl⟩
  exact normOneIdealClassRepresentative_mem c

/-- Remove the ordinary ideal class of a norm-one idele.  The result is
integral at every finite place, and multiplying back by the chosen
representative recovers the original idele class. -/
theorem exists_integral_normOne_reduction
    (a : IdeleGroup K)
    (ha : a ∈ normOneSubgroup (K := K)) :
    ∃ b : IdeleGroup K,
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) ∧
      b ∈ normOneSubgroup (K := K) ∧
      QuotientGroup.mk' (principalSubgroup K)
          (b * normOneIdealClassRepresentative
            (K := K) (idealClass a)) =
        QuotientGroup.mk' (principalSubgroup K) a := by
  let r :=
    normOneIdealClassRepresentative (idealClass a)
  let d := a * r⁻¹
  have hdClass : idealClass d = 1 := by
    dsimp [d]
    rw [map_mul, map_inv, (idealClass_normOneIdealClassRepresentative
      (idealClass a) ⟨a, ha, rfl⟩)]
    exact mul_inv_cancel _
  have hdPrincipal :
      fractionalIdeal d ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
    change ClassGroup.mk K (fractionalIdeal d) = 1 at hdClass
    exact (classGroup_mk_eq_one_iff (fractionalIdeal d)).mp hdClass
  obtain ⟨x, hx⟩ := hdPrincipal
  let p := principalIdele K x
  let b := d * p⁻¹
  have hbIntegral :
      b.2 ∈ FiniteIdeleGroup.integralSubgroup := by
    change b ∈ integralAtFinitePlaces
    rw [← fractionalIdeal_ker, MonoidHom.mem_ker]
    dsimp [b, p]
    rw [map_mul, map_inv, fractionalIdeal_principalIdele,
      hx, mul_inv_cancel]
  refine ⟨b, hbIntegral, ((normOneSubgroup).mul_mem ((normOneSubgroup).mul_mem ha
    ((normOneSubgroup).inv_mem (normOneIdealClassRepresentative_mem (idealClass a))))
    ((normOneSubgroup).inv_mem (principalSubgroup_le_normOneSubgroup ⟨x, rfl⟩))), ?_⟩
  apply QuotientGroup.eq_iff_div_mem.mpr
  refine ⟨x⁻¹, ?_⟩
  dsimp [b, d, p]
  rw [map_inv]
  symm
  calc
    a * r⁻¹ * (principalIdele K x)⁻¹ * r * a⁻¹ =
        (a * a⁻¹) * (r⁻¹ * r) * (principalIdele K x)⁻¹ := by
      ac_rfl
    _ = (principalIdele K x)⁻¹ := by simp

/-- A compact set of ideles meeting every norm-one idele class. -/
def compactNormOneClassCover : Set (IdeleGroup K) :=
  compactIntegralNormOneSet (K := K) *
    normOneIdealClassRepresentativeSet (K := K)

theorem isCompact_compactNormOneClassCover :
    IsCompact (compactNormOneClassCover (K := K)) :=
  by
    simpa [compactNormOneClassCover] using
      (isCompact_compactIntegralNormOneSet).mul
        (isCompact_normOneIdealClassRepresentativeSet)

theorem compactIntegralNormOneSet_subset_normOne :
    compactIntegralNormOneSet (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  intro a ha
  rw [mem_compactIntegralNormOneSet_iff] at ha
  change absoluteNorm a = 1
  rw [absoluteNorm_apply, (finite_absoluteNorm_eq_one_of_integral a.2 ha.2.1), ha.2.2, inv_one, mul_one]

theorem compactNormOneClassCover_subset_normOne :
    compactNormOneClassCover (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  rintro z ⟨b, hb, r, hr, rfl⟩
  exact (normOneSubgroup).mul_mem
    (compactIntegralNormOneSet_subset_normOne hb)
    (normOneIdealClassRepresentativeSet_subset_normOne hr)

end IdeleGroup

namespace IdeleClassGroup

/-- The image of the compact idele cover is exactly the group of norm-one
idele classes. -/
theorem image_compactNormOneClassCover :
    (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)) ''
        IdeleGroup.compactNormOneClassCover (K := K) =
      (normOneSubgroup (K := K) : Set (IdeleClassGroup K)) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mk_mem_normOneSubgroup_iff a).mpr
      (IdeleGroup.compactNormOneClassCover_subset_normOne ha)
  · intro hq
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (IdeleGroup.principalSubgroup K) q
    obtain ⟨b, hbIntegral, hbNorm, hbClass⟩ :=
      IdeleGroup.exists_integral_normOne_reduction a ((mk_mem_normOneSubgroup_iff a).mp hq)
    obtain ⟨c, hcCompact, hcClass⟩ :=
      IdeleGroup.exists_compactIntegralNormOneSet_representative
        b hbNorm hbIntegral
    let r :=
      IdeleGroup.normOneIdealClassRepresentative
         (IdeleGroup.idealClass a)
    refine ⟨c * r, ?_, ?_⟩
    · exact
        ⟨c, hcCompact, r,
          ⟨IdeleGroup.idealClass a, rfl⟩, rfl⟩
    · calc
        _ =
            QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) c *
              QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) r := by
                  rw [map_mul]
        _ =
            QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) b *
              QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) r := by
                  rw [hcClass]
        _ =
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) (b * r) := by
                rw [map_mul]
        _ =
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a := hbClass

/-- The norm-one idele class group is compact. -/
theorem normOneSubgroup_isCompact :
    IsCompact
      ((normOneSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := by
  rw [← image_compactNormOneClassCover]
  exact
    (IdeleGroup.isCompact_compactNormOneClassCover).image
      QuotientGroup.continuous_mk

/-- Compact-space form of the compactness theorem for norm-one idele classes. -/
instance normOneSubgroupCompactSpace :
    CompactSpace (normOneSubgroup (K := K)) :=
  isCompact_iff_compactSpace.mp
    (normOneSubgroup_isCompact (K := K))

end IdeleClassGroup

end
