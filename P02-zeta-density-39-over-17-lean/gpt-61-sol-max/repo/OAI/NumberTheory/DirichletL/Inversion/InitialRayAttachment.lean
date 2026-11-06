module
public import OAI.NumberTheory.DirichletL.Inversion.InitialKernelBridge

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
open scoped EisensteinO

def elementCharacter (η : Ideal O →* ℂ) : O →* ℂ where
  toFun x := η (Ideal.span {x})
  map_one' := by rw [Ideal.span_singleton_one, ←Ideal.one_eq_top, map_one]
  map_mul' x y := by rw [←Ideal.span_singleton_mul_span_singleton,map_mul]

theorem elementCharacter_product {ι : Type*} (η : Ideal O →* ℂ)
    (p : ι → O) (A : Finset ι) :
    elementCharacter η (∏ i ∈ A,p i) = η (∏ i ∈ A,Ideal.span {p i}) := by
  change η (Ideal.span {∏ i ∈ A,p i}) = _
  rw [FiniteGaussPhase.span_finset_prod]

section
variable (F : Finset (Ideal O))
include F

theorem poolPrimary_injective  (hF : ∀ I ∈ F,Admissible I) :
    Function.Injective (fun i : primePool F => Ideal.span {poolPrimary F i}) := by
  intro i k he
  change Ideal.span {poolPrimary F i} = Ideal.span {poolPrimary F k} at he
  rw [poolPrimary_span F hF,poolPrimary_span F hF] at he
  exact Subtype.ext he

theorem poolPrimary_primary  (hF : ∀ I ∈ F,Admissible I)
    (i : primePool F) : goodLambda^2 ∣ poolPrimary F i-1 :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2

theorem selected_mask  (j : Ideal O) (hj : Admissible j)
    (A : Finset (primePool F)) (hcop : IsCoprime (∏ i ∈ A,i.val) j) :
    rowCoprimeMask (fun i : primePool F => i.val) A (primaryGenerator j)=1 := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  unfold rowCoprimeMask
  split_ifs with h
  · obtain ⟨i,hi,hm⟩ := h
    have hd : i.val ∣ ∏ k ∈ A,k.val := Finset.dvd_prod_of_mem _ hi
    have hjd : i.val ∣ j := by
      rw [Ideal.dvd_iff_le,←hspan]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have hp : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    exact False.elim (hp.not_isUnit (hcop.isRelPrime hd hjd))
  · rfl

theorem selected_conjugate_row 
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (hcop : ∀ I ∈ F,IsCoprime I j) (η : Ideal O →* ℂ) (H : Ideal O → ℂ) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  erw [initial_input_row]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    rw [selected_mask F j hj A (hcop _ hAF),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]
end


section RayModes
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})
open FirstPassCubeLabels (primeProductNorm primeProductNorm_union)

def initialTest (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (A : Finset ι) : ℂ :=
  σ A*V (primeProductNorm p A/Z^D)

def initialBeta (Ψ : O →* ℂ) (j : O) (G : Finset ι) : ℂ :=
  (‖Ψ (∏ i ∈ G,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) G j‖^2 : ℝ)

theorem initial_overlap_weight (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (G U T : Finset ι) :
    overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T =
      initialBeta p Ψ j G *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
        (supportMobius (fun i => Ideal.span {p i}) T *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
        star (V (primeProductNorm p (G∪U)/Z^D))*V (primeProductNorm p (G∪T)/Z^D) := by
  have hrow (A : Finset ι) :
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A 1 = 1 :=
    finiteSquarefreeRow_one _ hg A
  simp only [overlapPairWeight,secondInputCoefficient,initialBeta,initialTest,
    hrow,one_pow,mul_one,star_mul]
  ring

theorem initial_pair_rays
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j e h : O) (σ : Finset ι → ℂ)
    (G U T : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) :
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
      (supportMobius (fun i => Ideal.span {p i}) T *
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
      activeGaussRowFactor p hp hinj hg T U e h =
    ∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i) e h
        (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i) e (-h)
        (fun A => σ (G∪A)) T := by
  have hm (A : Finset ι) (hAG : Disjoint A G) :
      secondInputCoefficient p hg Ψ (j*∏ i ∈ G,p i) 1 1 (fun A => σ (G∪A)) A =
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) A := by
    erw [secondInputCoefficient_fixed_mask,commonProduct_mask p hg hinj]
    simp only [hAG,ite_true,one_mul]
  have he := second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ Ψ
    (j*∏ i ∈ G,p i) 1 1 e h (fun A => σ (G∪A)) (fun A => σ (G∪A)) U T hUT
  rw [hm U hGU.symm,hm T hGT.symm] at he
  simpa only [Fintype.sum_prod_type,secondRayCoefficient,secondRayMinus,secondRayPlus,
    initialColumn_eq_secondPre] using he

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem initial_product_kernel (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) (h : O) :
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h) =
    ((Z^(-D) : ℝ) : ℂ)*star (V (primeProductNorm p (G∪U)/Z^D))*
      V (primeProductNorm p (G∪T)/Z^D)*
      ((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ) *
      (1/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) := by
  have hn := active_norm_sq_disjoint p U T hUT
  have hr : Real.sqrt (primeProductNorm p U*primeProductNorm p T) =
      ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ := by
    rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have he : (Ideal.absNorm (sourceIdeal p E) : ℝ) =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 := by
    rw [primeSubsetGenerator_norm_sq,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  have hnorm (A : Finset ι) : (Ideal.absNorm (sourceIdeal p A) : ℝ)=primeProductNorm p A :=
    (eisEmbedding_norm_sq_eq_absNorm_span _).symm
  unfold physicalKernel physicalCoordinates
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    hnorm,map_one,Nat.cast_one,mul_one,one_pow]
  rw [hr,←hnorm E,he,hn]
  rw [primeProductNorm_union p G U hGU,primeProductNorm_union p G T hGT]
  push_cast
  ring_nf

def initialPhysicalMode (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι) (h : O) : ℂ :=
  initialBeta p Ψ j G * (moebius (sourceIdeal p E) : ℂ) *
    (∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (-h) (fun A => σ (G∪A)) T) *
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h)

section
variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
include hinj hc hpr

theorem normalized_overlap_mode
    
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι)
    (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) (h : O) :
    ((Z^(-D) : ℝ) : ℂ)*
      overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T *
      (((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ)) *
      ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      (paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) *
        activeGaussRowFactor p hp hinj hg T U
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h := by
  rw [initial_overlap_weight]
  unfold initialPhysicalMode
  rw [←initial_pair_rays p hp hcop hg hinj hc hpr Ψ j _ h σ G U T hGU hGT hUT,
    initial_product_kernel p V Φ Z D m G U T E hGU hGT hUT h]
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  ring

theorem initial_input_physical
    
    (F : Finset ι) (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2) : ℝ) : ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ)) =
    ∑ G ∈ F.powerset,∑ U ∈ (F\G).powerset,∑ T ∈ (F\G).powerset,
      if Disjoint U T then ∑ E ∈ G.powerset,∑' h : O,
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h else 0 := by
  have hn := norm_rpow_half_sq hZ D
  simp only [norm_mul,mul_pow,hn,Complex.ofReal_mul]
  have hs : (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (((Z^(-D) : ℝ) : ℂ)*(‖inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ))) =
      ((Z^(-D) : ℝ) : ℂ)*(∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖inputConjugateRow p hg F Ψ j 1 1 (initialTest p σ V Z D) u‖^2 : ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro u
    ring
  rw [hs,inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ j 1 1
    (initialTest p σ V Z D) Φ (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hUT : Disjoint U T
  · simp only [hUT,ite_true]
    have hGU : Disjoint G U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    unfold maskedSecondDual
    simp only [Finset.mul_sum,←tsum_mul_left]
    apply Finset.sum_congr rfl
    intro E hE
    apply tsum_congr
    intro h
    convert normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
      Z D m G U T E hGU hGT hUT h using 1
    ring
  · simp only [hUT,ite_false,mul_zero]

theorem initialPhysicalMode_summable
    
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    Summable (initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E) := by
  have hs := secondPairRadialMode_summable p hp hg hinj U T
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (primeSubsetGenerator_ne_zero _ _)
    Φ (Z^m) (Real.rpow_pos_of_pos hZ m)
  have hs' := (hs.mul_left ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ))).mul_left
    (((Z^(-D) : ℝ) : ℂ)*overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T)
  apply hs'.congr
  intro h
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
    Z D m G U T E hGU hGT hUT h]
  unfold secondPairRadialMode
  ring
end









