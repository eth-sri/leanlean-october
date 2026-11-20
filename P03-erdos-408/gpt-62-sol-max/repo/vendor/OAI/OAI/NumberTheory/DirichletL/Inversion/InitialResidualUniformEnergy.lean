module

public import OAI.NumberTheory.DirichletL.Inversion.InitialOriginalHeight
public import OAI.NumberTheory.DirichletL.Inversion.InitialInputReindex
public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier
public import OAI.NumberTheory.DirichletL.Inversion.InitialUniformFresh
public import OAI.NumberTheory.DirichletL.Inversion.InitialInputRadial
public import OAI.NumberTheory.DirichletL.Inversion.InitialAssignments
public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapHeight
public import OAI.NumberTheory.DirichletL.Inversion.InitialMarkedInputEnergy

public import OAI.NumberTheory.DirichletL.Inversion.InitialAssignments

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualUniformEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool InverseInitialDyadicAssembly
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_uniform_energy
    (Woriginal:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→
    ForInitialAssignments (fun P : Ideal O => (P.absNorm : ℝ)) K Z fun σ _ all assigned L Hslot coeff qelem z al bl primeW =>
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ForInitialSourceScales all assigned Hslot z bl Z cap η gap fun D m r =>
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨W,A,B,Bnorm,hA,hAB,hBn,hWc,hWs,hWb,hFresh⟩:=
    InverseInitialUniformFresh.exists_uniform_fresh K ao bo hao hab
  have hs:=(subset_tsupport (W:ℝ→ℂ)).trans hWs
  let g := CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo
  obtain ⟨J₀,Btree,hBtree,hinput⟩ := InverseInitialTotalEnergy.original_input_bound
    W A B 1 hA le_rfl hs (W.smooth ⊤) Φ Bnorm hBn hWb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  let J := InverseClippingProfiles.momentOrder (4*J₀)
  obtain ⟨Cm,hCm,hmeasure⟩ := InverseInitialOverlapHeight.twisted_polynomial_measure_energy g J
  refine ⟨J+(volume : Measure ℝ).integrablePower,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hinput⟩ := hinput q hq
  refine ⟨(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan hjratio hL hcoeff hP hcopTuple hPE θ
  have hZp:=zero_lt_one.trans (hZ₀.trans_le hZ)
  obtain ⟨Dpool,hcover,hfloor⟩:=exists_excluded_complete_pool
    (originalSource Z r bo) (reflectionExcludedPrimes q) ((all\assigned).pi L)
    (fun t=>j*survivingProduct (all\assigned) t) j (reflectionExcludedPrimes_prime q)
    hP (fun t _=>dvd_mul_right j _) hPE (originalSource_supported Z r bo) (Btree*Z^(cap+1))
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool
  have hFa:=InitialMeanSquare.outsideSquarefree_admissible
    (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q)
  letI := poolPrimary_maximal F hFa
  let p:=poolPrimary F
  let hg:=poolPrimary_good F hFa
  have hfresh:=hFresh (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK) Woriginal hso
  have hdisPool:(all:Set σ).PairwiseDisjoint (fun i=>poolList F (L i)):=by
    intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro P hPi hPk
    exact (Finset.disjoint_left.mp (hdis hi hk hik))
      (Finset.mem_filter.mp hPi).2 (Finset.mem_filter.mp hPk).2
  let lists := fun i => poolList F (L i)
  let y := fun (i : σ) (P : primePool F) => Real.log (slotRatio Z z i P.val)
  let xj := Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))
  let φ (u : O) (t : ℝ) := ((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ (elementCharacter χ)
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P.val*logPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht := hmeasure θ xj (fun u:rows=>φ u.val) (C*Z^(m+15*η+π+eps+loss)) (by positivity)
    (fun u=>InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ (elementCharacter χ) (assignedElement assigned qelem) u.val
      (all\assigned) lists (fun i P=>coeff i P.val) y W Z D xj) (fun t=>by
    have he := hinput Z hZ Dpool hfloor all assigned hassigned hK lists Hslot
      (fun i P=>coeff i P.val*logPhase (-t) (y i P)) hdisPool hHs
      (fun i hi P hP=>hPs i hi P.val (Finset.mem_filter.mp hP).2)
      (by intro i hi P hP; simpa only [norm_mul,logPhase_norm,mul_one] using hac i hi P.val (Finset.mem_filter.mp hP).2)
      qelem z al bl primeW hz hqe hprimeW hprimeLive (elementCharacter χ) hχ hperiod
      D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent 1 t le_rfl le_rfl
    have hr := InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ (elementCharacter χ)
      (assignedElement assigned qelem)
      (initialTest p (primeMark (all\assigned) lists
        (fun i P=>coeff i P.val*logPhase (-t) (y i P))) (childLogTest W t) Z D)
      ((Z^(-D/2):ℝ):ℂ) Φ hΦ hone (Z^m) (Real.rpow_pos_of_pos hZp _) rows hrows
    refine (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans (hr.trans ?_)
    simpa only [InverseInitialProfileBounds.childLogTest_eq_clipped,J,pow_mul,pow_two,mul_pow] using he)
  have hsum:∑i∈all\assigned,z i=assignedCenter all z-assignedCenter assigned z:=by
    have hh:=Finset.sum_sdiff (f:=z) hassigned
    dsimp [assignedCenter]
    linarith
  have hgj:=
    (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1.trans hspan.symm
  have hid (u:O):
      (∑t∈(all\assigned).pi L,(∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u)=
      ∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t := by
    have hh:=InverseInitialExcludedFourier.original_tuples_excluded_fourier
      (childLogTest Woriginal θ) W ao bo hao
      ((InverseInitialOriginalHeight.child_support Woriginal θ).trans hso)
      (InverseInitialOriginalHeight.child_smooth Woriginal ao bo hao hso hWo θ)
      (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (all\assigned) L hL coeff j hj.1 hP hcopTuple hPE χ hout u Z r
      (assignedCenter all z) (assignedCenter assigned z) hZp z (fun _=>1) (fun _=>2) hsum 1 ((2:ℝ)^K) hjratio hcoeff
      (fun v yj yc hv hyj hyc hn=>hfresh v yj yc hv hyj hyc
        (InverseInitialOriginalHeight.child_support Woriginal θ hn))
      F hFa (fun I hI=>(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2) hcover
    rw [hh,InverseInitialOriginalHeight.logSchwartz_child]
    simp only [←hDeq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    dsimp only [φ]
    rw [InverseInitialInputReindex.input_puncture_span p hg Finset.univ (elementCharacter χ)
      (primaryGenerator j) (assignedElement assigned qelem) hgj]
  simp_rw [hid]
  refine (Finset.sum_coe_sort rows (fun u=>‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t‖^2)).symm.le.trans (ht.trans ?_)
  have hE : 0≤C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)) := by positivity
  simpa only [←pow_mul,Nat.mul_comm,mul_assoc] using
    mul_le_mul_of_nonneg_right (show Cm≤Cm+1 by linarith) hE

end SevenEighths.InverseInitialResidualUniformEnergy

end

end OAI
