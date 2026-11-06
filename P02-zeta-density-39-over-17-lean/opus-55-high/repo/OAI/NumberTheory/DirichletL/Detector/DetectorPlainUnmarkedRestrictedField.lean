module
public import OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical SchwartzMap
open Filter

namespace SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField
open HeckeDyadic HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound

open ProbeDetectorPlainUnmarkedField
variable {Δ:ℝ}

theorem source_batch_plain_unmarked (D:Parameters.HighData Δ)
    (S:ProbeFinalAssembly.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z ^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z ^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→ B.widths=(fun s=>D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z ^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z ^d)^F.m) σ t‖^2;
      value≤C*(1+height)^Jheight*(Z ^d)^(max 1 (2*F.m)+D.t) ∧
      value≤C*(1+height)^Jheight*max (Z ^d) (((Z ^d)^F.m)^2)*(Z ^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  pm_3698 Jheight Cp hCp hprofiles paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=>sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=>internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=>henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  pm_5053 hsum A hA
  pm_466 hAmax Amax
  have hA_bound (label):A label≤Amax:=by
    pm_342 hh hA label Amax
  pm_7897 C Amax Cp
  have hC:0<C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤d→
      ZeroAt (Q label) (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D)
        (Z ^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z ^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1<Z ^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z ^d)^(max 1 (2*F.m)+delta D +stageError D)≤
      (Z ^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤C*(1+height)^Jheight*(Z ^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z ^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z ^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField


end OAI
