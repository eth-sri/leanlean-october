module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps

open scoped NumberField Valued ValuativeRel Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def reverseCompactLaurentIntegrand
    (I : IwasawaData A) (B : Binding F ζ hζ q A P)
    (L : CompactOpenLevel (Cover F ζ hζ q))
    (χ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .minus L)
    (r : ℂˣ) (lam : ℂ) (h : H₀) (v : (LocalField F q)ˣ) : ℂ :=
  (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (reverseRoot F ζ hζ q T A P B r v
      ((centerCompactTrivialization F ζ hζ q T A I .minus (-additiveParameter F q r)
        ((1 - t F q (r : ℂ))⁻¹ • χ.sum (fun n f => (r : ℂ) ^ n • f)).val).val
          (openCoordinate F ζ hζ q (v : LocalField F q)))).val h *
    normPower (LocalField F q) v lam

section

variable (v : (LocalField F q)ˣ)

theorem reverse_compact_normPower_regulator (lam : ℂ) :
    normPower (LocalField F q) v lam = Q F q lam ^ (-valuationIndex F q v) := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos)
  rw [normPower, localAbs, Real.log_rpow hq, Q, ← Complex.exp_int_mul]
  congr 1
  simp only [valuationIndex]
  push_cast
  ring

theorem reverse_compact_normPower_root (r : ℂˣ) :
    normPower (LocalField F q) v (-additiveParameter F q r) =
      (r : ℂ) ^ valuationIndex F q v := by
  have hq1 : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hq1
  have hlog : (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hq1)).ne'
  rw [normPower, localAbs, Real.log_rpow hq, ← Complex.exp_log (Units.ne_zero r),
    ← Complex.exp_int_mul]
  congr 1
  simp only [valuationIndex, additiveParameter]
  rw [Complex.ofReal_mul]
  field_simp
  norm_cast

theorem reverse_compact_valuationIndex_sq :
    valuationIndex F q (v ^ 2) = 2 * valuationIndex F q v := by
  have hv : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) v) ≠ 0 := by simp
  simp only [valuationIndex, pow_two, Units.val_mul, map_mul, WithZero.log_mul hv hv]
  ring

end

def reverseCompactRootExponent (I : IwasawaData A) (v : (LocalField F q)ˣ) : ℤ :=
  2 * valuationIndex F q v + valuationIndex F q
    (A.coordinate (A.retract (I.borelPart (openCoordinate F ζ hζ q (v : LocalField F q)))))

section

variable (I : IwasawaData A) (B : Binding F ζ hζ q A P) (L : CompactOpenLevel (Cover F ζ hζ q))

def reverseCompactRootCoefficient
    (f : centerCompactLevel F ζ hζ q T A I .minus L)
    (h : H₀) (v : (LocalField F q)ˣ) : ℂ :=
  (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (centerTorus F ζ hζ q T A .minus (B.rootTorus v)
      (centerInducingAction F ζ hζ q T A .minus 0
        (I.borelPart (openCoordinate F ζ hζ q (v : LocalField F q)))
        (f.val.val (I.compactPart (openCoordinate F ζ hζ q (v : LocalField F q)))))).val h

theorem reverse_compact_pointwise_laurent
    (χ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .minus L)
    (r : ℂˣ) (lam : ℂ) (h : H₀) (v : (LocalField F q)ˣ) :
    reverseCompactLaurentIntegrand F ζ hζ q T A P I B L χ r lam h v =
      (∑ n ∈ χ.support,
        reverseCompactRootCoefficient F ζ hζ q T A P I B L (χ n) h v *
          (r : ℂ) ^ (n + reverseCompactRootExponent F ζ hζ q T A I v) *
          Q F q lam ^ (-valuationIndex F q v)) / (1 - t F q (r : ℂ)) := by
  let centerTorus₀ := centerTorus F ζ hζ q T A .minus
  classical
  let x := openCoordinate F ζ hζ q (v : LocalField F q)
  let b := I.borelPart x
  let y := A.coordinate (A.retract b)
  have hs : inducingScalar A (-additiveParameter F q r) b =
      deltaHalf A b * (r : ℂ) ^ valuationIndex F q y := by
    exact congrArg (deltaHalf A b * ·) (reverse_compact_normPower_root F q y r)
  have hs0 : inducingScalar A 0 b = deltaHalf A b := by simp [inducingScalar, normPower]
  change (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (normPower (LocalField F q) (v ^ 2) (-additiveParameter F q r) •
      centerTorus₀ (B.rootTorus v)
        (inducingScalar A (-additiveParameter F q r) b •
          centerTorus₀ (A.retract b)
            (((1 - t F q (r : ℂ))⁻¹ • χ.sum (fun n f => (r : ℂ) ^ n • f)).val.val
              (I.compactPart x)))).val h * normPower (LocalField F q) v lam = _
  rw [hs, reverse_compact_normPower_root, reverse_compact_valuationIndex_sq,
    reverse_compact_normPower_regulator]
  simp only [Finsupp.sum, Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply,
    Finset.sum_apply, map_smul, map_sum, smul_eq_mul]
  change _ = (∑ n ∈ χ.support,
    ((B.eta (kappa F ζ hζ q v 0) : ℂ) *
      (centerTorus₀ (B.rootTorus v)
        (inducingScalar A 0 b • centerTorus₀ (A.retract b)
          ((χ n).val.val (I.compactPart x)))).val h) *
      (r : ℂ) ^ (n + (2 * valuationIndex F q v + valuationIndex F q y)) *
      Q F q lam ^ (-valuationIndex F q v)) / (1 - t F q (r : ℂ))
  rw [hs0]
  simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp only [zpow_add₀ r.ne_zero, div_eq_mul_inv]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end

section

variable (I : IwasawaData A)

theorem reverse_compact_laurent_annulus_of_finite_integrable_coefficients (μ : Measure (LocalField F q))
    (B : Binding F ζ hζ q A P) (L : CompactOpenLevel (Cover F ζ hζ q))
    (χ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .minus L) (N : ℕ)
    (M : Finset (ℤ × ℤ))
    (hM : ∀ v ∈ annulusRegion F q N,
      (reverseCompactRootExponent F ζ hζ q T A I v, -valuationIndex F q v) ∈ M)
    (hmeas : ∀ n ij, MeasurableSet {v : (LocalField F q)ˣ |
      ij = (n + reverseCompactRootExponent F ζ hζ q T A I v, -valuationIndex F q v)})
    (hc : ∀ h n, n ∈ χ.support → IntegrableOn
      (reverseCompactRootCoefficient F ζ hζ q T A P I B L (χ n) h)
        (annulusRegion F q N) (multiplicativeMeasure F q μ)) :
    ∃ (S : Finset (ℤ × ℤ)) (c : H₀ → (ℤ × ℤ) → (LocalField F q)ˣ → ℂ),
      (∀ h ij, ij ∈ S → IntegrableOn (c h ij)
        (annulusRegion F q N) (multiplicativeMeasure F q μ)) ∧
      ∀ (r : ℂˣ), IsRegular F q r → ∀ lam : ℂ, ∀ h v,
        v ∈ annulusRegion F q N →
        reverseCompactLaurentIntegrand F ζ hζ q T A P I B L χ r lam h v =
          (∑ ij ∈ S, c h ij v * (r : ℂ) ^ ij.1 * (Q F q lam) ^ ij.2) /
            (1 - t F q (r : ℂ)) := by
  classical
  let S := χ.support.biUnion fun n => M.image fun ej => (n + ej.1, ej.2)
  let c := fun h ij v =>
    ∑ n ∈ χ.support,
      if ij = (n + reverseCompactRootExponent F ζ hζ q T A I v, -valuationIndex F q v)
      then reverseCompactRootCoefficient F ζ hζ q T A P I B L (χ n) h v else 0
  refine ⟨S, c, ?_, ?_⟩
  · intro h ij hij
    apply integrable_finset_sum
    intro n hn
    have hi := (hc h n hn).indicator (hmeas n ij)
    change Integrable _ _ at hi
    convert hi using 1
    funext v
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  · intro r hr lam h v hv
    rw [reverse_compact_pointwise_laurent]
    congr 1
    dsimp [c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    have hin : (n + reverseCompactRootExponent F ζ hζ q T A I v, -valuationIndex F q v) ∈ S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨n, hn, ?_⟩
      exact Finset.mem_image.mpr ⟨_, hM v hv, rfl⟩
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' S _ _]
    simp [hin]

private theorem iwasawa_abs_right_invariant (g j : Cover F ζ hζ q) (hj : j ∈ I.compact.toOpenSubgroup) :
    localAbs (LocalField F q) (A.coordinate (A.retract (I.borelPart (g * j)))) =
      localAbs (LocalField F q) (A.coordinate (A.retract (I.borelPart g))) := by
  have he : ((I.borelPart g)⁻¹ * I.borelPart (g * j) : Cover F ζ hζ q) =
      (I.compactPart g : Cover F ζ hζ q) * j * (I.compactPart (g * j) : Cover F ζ hζ q)⁻¹ := by
    have h1 := I.decomposition g
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    apply eq_mul_inv_iff_mul_eq.mpr
    rw [mul_assoc, ← (I.decomposition (g * j))]
    calc
      (I.borelPart g : Cover F ζ hζ q)⁻¹ * (g * j) =
          (I.borelPart g : Cover F ζ hζ q)⁻¹ *
            (((I.borelPart g : Cover F ζ hζ q) * (I.compactPart g : Cover F ζ hζ q)) * j) := by
        congr 2
      _ = _ := by group
  have hm : ((I.borelPart g)⁻¹ * I.borelPart (g * j) : Cover F ζ hζ q) ∈
      I.compact.toOpenSubgroup := by
    rw [he]
    exact I.compact.toOpenSubgroup.mul_mem
      (I.compact.toOpenSubgroup.mul_mem (I.compactPart g).property hj)
      (I.compact.toOpenSubgroup.inv_mem (I.compactPart (g * j)).property)
  have hn := I.intersection_norm ((I.borelPart g)⁻¹ * I.borelPart (g * j)) hm
  simp only [map_mul, map_inv, localAbs_mul] at hn
  have hi (y : (LocalField F q)ˣ) : localAbs (LocalField F q) y⁻¹ = (localAbs (LocalField F q) y)⁻¹ := by
    have hh := localAbs_mul (LocalField F q) y y⁻¹
    rw [mul_inv_cancel, localAbs_one] at hh
    exact eq_inv_of_mul_eq_one_right hh.symm
  rw [hi] at hn
  exact ((inv_mul_eq_one₀ (localAbs_pos _ _).ne').mp hn).symm

theorem reverse_compact_iwasawa_valuation_locallyConstant :
    IsLocallyConstant (fun g : Cover F ζ hζ q =>
      valuationIndex F q (A.coordinate (A.retract (I.borelPart g)))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous (fun g' : Cover F ζ hζ q => g⁻¹ * g') := continuous_const.mul continuous_id
  have hn : ∀ᶠ g' in nhds g, g⁻¹ * g' ∈ I.compact.toOpenSubgroup :=
    hc.continuousAt.preimage_mem_nhds (by simpa using
      I.compact.toOpenSubgroup.isOpen.mem_nhds I.compact.toOpenSubgroup.one_mem)
  filter_upwards [hn] with g' hg'
  have ha := iwasawa_abs_right_invariant F ζ hζ q T A I g (g⁻¹ * g') hg'
  simp only [mul_inv_cancel_left] at ha
  have hq : 1 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast Finite.one_lt_card
  unfold localAbs at ha
  exact_mod_cast ((Real.rpow_right_inj (lt_trans zero_lt_one hq) hq.ne').mp ha)

end

theorem reverse_compact_valuationIndex_locallyConstant :
    IsLocallyConstant (valuationIndex F q) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro v
  filter_upwards [(Units.continuous_val.continuousAt.preimage_mem_nhds ((valuation (LocalField F q)).locally_const
    (by simp)))] with w hw
  change valuation (LocalField F q) w = valuation (LocalField F q) v at hw
  simp only [valuationIndex, hw]

section

variable (I : IwasawaData A) (P : Polarization T) (B : Binding F ζ hζ q A P)

include B in
theorem reverse_compact_exponents_locallyConstant :
    IsLocallyConstant (fun v : (LocalField F q)ˣ =>
      (reverseCompactRootExponent F ζ hζ q T A I v, -valuationIndex F q v)) := by
  have hn : Continuous (nLift F ζ hζ q) := by
    have he :=
      funext (fun s => (B.upper_eq s).symm)
    rw [he]
    exact continuous_subtype_val.comp (A.upperRoot_continuous.comp continuous_ofAdd)
  have hopen : Continuous (openCoordinate F ζ hζ q) := continuous_const.mul hn
  have hi := (reverse_compact_iwasawa_valuation_locallyConstant F ζ hζ q T A I).comp_continuous
    (hopen.comp Units.continuous_val)
  have hv := reverse_compact_valuationIndex_locallyConstant F q
  rw [IsLocallyConstant.iff_eventually_eq]
  intro v
  have hv' := (IsLocallyConstant.iff_eventually_eq _).mp hv v
  have hi' := (IsLocallyConstant.iff_eventually_eq _).mp hi v
  filter_upwards [hv', hi'] with w hw hk
  dsimp only [Function.comp_def] at hk
  simp only [reverseCompactRootExponent, hw, hk]

include B in
theorem reverse_compact_exponents_finite_on_compact
    (C : Set (LocalField F q)ˣ) (hC : IsCompact C) :
    ∃ M : Finset (ℤ × ℤ), ∀ v ∈ C,
      (reverseCompactRootExponent F ζ hζ q T A I v, -valuationIndex F q v) ∈ M := by
  classical
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hl := (reverse_compact_exponents_locallyConstant F ζ hζ q T A I P B).comp_continuous
    (continuous_subtype_val : Continuous (fun v : C => (v : (LocalField F q)ˣ)))
  refine ⟨hl.range_finite.toFinset, ?_⟩
  intro v hv
  exact hl.range_finite.mem_toFinset.mpr ⟨⟨v, hv⟩, rfl⟩

end

private lemma root_cont (B : Binding F ζ hζ q A P) : Continuous B.rootTorus := by
 have ht : Continuous (fun v => A.torus (B.rootTorus v)) := by
   apply Continuous.subtype_mk
   change Continuous (fun v => (A.torus (B.rootTorus v) : Cover F ζ hζ q))
   simp_rw [B.torus_eq]
   exact ((KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
     (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2).comp (continuous_id.pow 2)
 have he : B.rootTorus = fun v => A.retract (A.torus (B.rootTorus v)) := by
   funext v; exact (A.retract_torus _).symm
 rw [he]
 exact A.retract_continuous.comp ht

alias ReverseCompactLaurentAnnulus.root_cont := root_cont
private lemma kappa_lc : IsLocallyConstant (fun v : (LocalField F q)ˣ => kappa F ζ hζ q v 0) := by
 let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
 have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
 letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
 letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
 have hn := KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q m hm
 have he (v : (LocalField F q)ˣ) :
     KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
       (bruhatLeft F ζ hζ q v 0 * (bruhatRight F ζ hζ q v 0)⁻¹) =
     KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v 0) := by
   rw [raw_bruhat_identity, mul_inv_cancel_right]
   rfl
 have hc : Continuous (fun v : (LocalField F q)ˣ =>
     KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v 0)) := by
   simp_rw [← he]
   exact QuotientGroup.continuous_mk.comp (((((continuous_const.mul (hn.comp (Units.continuous_val.comp continuous_inv).neg)).mul continuous_const).mul continuous_const)).mul ((((KPScalarSplitCentral.finite_continuous_closed F ζ hζ q m hm).1).comp continuous_inv).mul
     ((((KPStandardLocalRootLifts.finite_A_continuous F ζ hζ q m hm).comp (continuous_id.pow 2)).mul (hn.comp (Units.continuous_val.comp continuous_inv))).mul continuous_const |>.mul
       (hn.comp (continuous_const.add Units.continuous_val)))).inv)
 letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
   @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
    (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))
 letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
 letI := (KPPGLLocalCover.finite_discrete_kernel F ζ hζ q m hm).1
 have hsub : Continuous (fun v : (LocalField F q)ˣ =>
   (⟨KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v 0),
     by rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]; exact ⟨_, rfl⟩⟩ :
     (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).ker)) := hc.subtype_mk _
 have hh := (IsLocallyConstant.iff_continuous _).mpr hsub
 rw [IsLocallyConstant.iff_eventually_eq] at hh ⊢
 intro v
 filter_upwards [hh v] with w hw
 exact KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q) (congrArg Subtype.val hw)

alias ReverseCompactLaurentAnnulus.kappa_lc := kappa_lc

private lemma center_lc (f : CenterModule T) : IsLocallyConstant f.val := by
 let J : Subgroup H₀ := T.ω.toMonoidHom.ker.map T.C.subtype
 have hJ : IsOpen (J : Set H₀) := by
   exact T.center_open.isOpenMap_subtype_val _ T.character_kernel_open
 rw [IsLocallyConstant.iff_eventually_eq]
 intro h
 have hc : Continuous (fun y : H₀ => y * h⁻¹) := continuous_id.mul continuous_const
 have hn : ∀ᶠ y in nhds h, y * h⁻¹ ∈ J :=
   hc.continuousAt.preimage_mem_nhds (by simpa using hJ.mem_nhds J.one_mem)
 filter_upwards [hn] with y hy
 obtain ⟨c, hc, he⟩ := hy
 have hw : T.ω c = 1 := hc
 have hf := f.property c h
 change (c : H₀) = y * h⁻¹ at he
 have hey : (c : H₀) * h = y := by rw [he]; group
 simpa [hey, hw] using hf

alias ReverseCompactLaurentAnnulus.center_lc := center_lc
local notation "LocalCompletion" => LocalField F q

private lemma coeff_lc (I : IwasawaData A) (B : Binding F ζ hζ q A P)
 (L : CompactOpenLevel (Cover F ζ hζ q))
 (f : centerCompactLevel F ζ hζ q T A I .minus L) (h : H₀) :
 IsLocallyConstant (reverseCompactRootCoefficient F ζ hζ q T A P I B L f h) := by
 let fs := centerCompactTrivialization F ζ hζ q T A I .minus 0 f.val
 have hfs : IsLocallyConstant fs.val := by
   obtain ⟨J, hJ⟩ := fs.property.2
   rw [IsLocallyConstant.iff_eventually_eq]
   intro g
   have hc : Continuous (fun y : Cover F ζ hζ q => g⁻¹ * y) := continuous_const.mul continuous_id
   have hn : ∀ᶠ y in nhds g, g⁻¹ * y ∈ J :=
     hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
   filter_upwards [hn] with y hy
   have he := congrFun (hJ (g⁻¹ * y) hy) g
   simpa [vectorRightTranslation] using he
 have hn : Continuous (nLift F ζ hζ q) :=
   (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
 have hopen : Continuous (fun v : LocalCompletionˣ => openCoordinate F ζ hζ q (v : LocalCompletion)) :=
   continuous_const.mul (hn.comp Units.continuous_val)
 have hfs' := hfs.comp_continuous hopen
 have hr := root_cont F ζ hζ q T A P B
 have hk := kappa_lc F ζ hζ q
 rw [IsLocallyConstant.iff_eventually_eq] at hfs' hk ⊢
 intro v
 have hrc : Continuous (fun w : LocalCompletionˣ => h * A.weyl (B.rootTorus w)) :=
   continuous_const.mul (A.weyl.continuous.comp hr)
 have hfval := (center_lc T (fs.val (openCoordinate F ζ hζ q (v : LocalCompletion)))).comp_continuous hrc
 have hfval' := (IsLocallyConstant.iff_eventually_eq _).mp hfval v
 filter_upwards [hfs' v, hk v, hfval'] with w hw hk' hh
 change (B.eta (kappa F ζ hζ q w 0) : ℂ) *
   (fs.val (openCoordinate F ζ hζ q (w : LocalCompletion))).val (h * A.weyl (B.rootTorus w)) =
   (B.eta (kappa F ζ hζ q v 0) : ℂ) *
   (fs.val (openCoordinate F ζ hζ q (v : LocalCompletion))).val (h * A.weyl (B.rootTorus v))
 dsimp only [Function.comp_def] at hw hh
 rw [hw, hk', hh]

private lemma ann_compact (N : ℕ) : IsCompact (annulusRegion F q N) := by
 let valueGroupWithZeroIsoInt₀ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
 let γ := (valueGroupWithZeroIsoInt₀).symm (WithZero.exp (N : ℤ))
 let C := {x | valuation LocalCompletion x ≤ γ}
 have hC : IsCompact C := IsNonarchimedeanLocalField.isCompact_closedBall _ _
 have hb : IsCompact {v : LocalCompletionˣ | (v : LocalCompletion) ∈ C ∧ ((v⁻¹ : LocalCompletionˣ) : LocalCompletion) ∈ C} := by
   exact Units.isClosedEmbedding_embedProduct |>.isCompact_preimage
     (hC.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hC))
 convert hb using 1
 ext v
 have hz : valueGroupWithZeroIsoInt₀
   (valuation LocalCompletion v) ≠ 0 := by simp
 have hzi : valueGroupWithZeroIsoInt₀
   (valuation LocalCompletion ((v⁻¹ : LocalCompletionˣ) : LocalCompletion)) ≠ 0 := by simp
 have he : valuationIndex F q v⁻¹ = -valuationIndex F q v := by
   simp [valuationIndex, WithZero.log_inv]
 simp only [annulusRegion, Set.mem_setOf_eq, C, γ]
 have hi (x : ValueGroupWithZero LocalCompletion) :
   x ≤ (valueGroupWithZeroIsoInt₀).symm (WithZero.exp (N : ℤ)) ↔
   valueGroupWithZeroIsoInt₀ x ≤ WithZero.exp (N : ℤ) := (valueGroupWithZeroIsoInt₀).toOrderIso.le_symm_apply
 rw [hi, hi]
 rw [← WithZero.log_le_iff_le_exp hz, ← WithZero.log_le_iff_le_exp hzi]
 change _ ↔ valuationIndex F q v ≤ (N : ℤ) ∧ valuationIndex F q v⁻¹ ≤ (N : ℤ)
 rw [he]
 omega

alias reverse_compact_annulus_isCompact := ann_compact

theorem reverse_compact_laurent_annulus
    (I : IwasawaData A) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (B : Binding F ζ hζ q A P) (L : CompactOpenLevel (Cover F ζ hζ q))
    (hL : (L.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup)
    (χ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .minus L) (N : ℕ) :
    ∃ (S : Finset (ℤ × ℤ)) (c : H₀ → (ℤ × ℤ) → (LocalField F q)ˣ → ℂ),
      (∀ h ij, ij ∈ S → IntegrableOn (c h ij)
        (annulusRegion F q N) (multiplicativeMeasure F q μ)) ∧
      ∀ (r : ℂˣ), IsRegular F q r → ∀ lam : ℂ, ∀ h v,
        v ∈ annulusRegion F q N →
        reverseCompactLaurentIntegrand F ζ hζ q T A P I B L χ r lam h v =
          (∑ ij ∈ S, c h ij v * (r : ℂ) ^ ij.1 * (Q F q lam) ^ ij.2) /
            (1 - t F q (r : ℂ)) := by
  classical
  letI : BorelSpace (LocalField F q)ˣ := by
    constructor
    unfold Units.instMeasurableSpace
    rw [‹BorelSpace (LocalField F q)›.measurable_eq, ← borel_comap]
    rw [← (Units.isEmbedding_val₀).isInducing.eq_induced]
  have hC := ann_compact F q N
  obtain ⟨M, hM⟩ := reverse_compact_exponents_finite_on_compact F ζ hζ q T A I P B _ hC
  have hhaar : (multiplicativeMeasure F q μ).IsHaarMeasure := by
    letI := IsTopologicalAddGroup.rightUniformSpace (LocalField F q)
    haveI := isUniformAddGroup_of_addCommGroup (G := LocalField F q)
    have hc : IsCompact (KPCubicUnitIndices.Integers (LocalField F q) : Set (LocalField F q)) :=
      IsNonarchimedeanLocalField.isCompact_closedBall _ 1
    have ho : IsOpen (KPCubicUnitIndices.Integers (LocalField F q) : Set (LocalField F q)) := by
      simpa using (Valuation.isOpen_integer)
    have hp : 0 < μ (KPCubicUnitIndices.Integers (LocalField F q) : Set (LocalField F q)) :=
      ho.measure_pos (μ := μ) ⟨0, by simp⟩
    exact (kp_rankone_cubic_haar_power_measure (LocalField F q) μ _
      (ENNReal.toReal_pos hp.ne' hc.measure_lt_top.ne) (ENNReal.ofReal_toReal hc.measure_lt_top.ne).symm).1
  letI := hhaar
  apply reverse_compact_laurent_annulus_of_finite_integrable_coefficients F ζ hζ q T A P I μ B L χ N M hM
  · intro n ij
    exact measurableSet_eq_fun measurable_const ((reverse_compact_exponents_locallyConstant F ζ hζ q T A I P B).comp
      (fun ej : ℤ × ℤ => (n + ej.1, ej.2))).continuous.measurable
  · intro h n hn
    exact (coeff_lc F ζ hζ q T A P I B L (χ n) h).continuous.continuousOn.integrableOn_compact hC

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps
