module

public import OAI.NumberTheory.DirichletL.Reflection.CompletedCanonicalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CompletedAggregation
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalCaps
public import OAI.NumberTheory.DirichletL.Reflection.PunctureLists
public import OAI.NumberTheory.DirichletL.Reflection.CubeSlotEnergy
public import OAI.NumberTheory.DirichletL.Reflection.SourcePhysical
public import OAI.NumberTheory.DirichletL.Reflection.SourceBudget
public import OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
public import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CountBudget
public import OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
public import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
public import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.TupleMembers
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalParameters
public import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
public import OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy
public import OAI.NumberTheory.DirichletL.Reflection.DyadBudget
public import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport
public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource
public import OAI.NumberTheory.DirichletL.Reflection.ChoiceEnergyData
public import OAI.NumberTheory.DirichletL.Reflection.DyadMemberEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalEnergyUniformDegree

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section

local notation "Eis" => ActualEisensteinCubic.O
universe v

set_option maxHeartbeats 1500000 in
theorem canonical_cube_shifted_completed_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (Hcube : Ideal Eis),Hcube≠0 → (Ideal.absNorm Hcube:ℝ)≤Z^hhat →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣Hcube^3*A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64) := by
  obtain ⟨degree,hu⟩ := canonical_member_geometry_uniform_uniform_degree lo hi hlo W hWs hW L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,?_⟩
  intro q hq
  let Q := CanonicalCoefficientClass.fixedBaseConductor q
  have hQ  := CanonicalCoefficientClass.fixedBaseConductor_ne_zero q hq
  let c := reflectionConductor q
  have hc  := reflectionConductor_ne_zero q hq
  let  := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let b := excludedGenerator (reflectionExcludedPrimes q)
  let B  := Ideal.span {b}
  have hb  := reflectionExcludedGenerator_ne_zero q
  have hB  := Ideal.span_singleton_eq_bot.not.mpr hb
  let E := fixedFourierGeometry c hc
  have hEc  := fun h => (E h).denominator_ne_zero
  have hEN  := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨Ca,Zmem,hCa,hZmem,hmember⟩ := hu
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode)
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime) B hB
  obtain ⟨Cd,hCd,hbins⟩ := actual_dyad_count_budget L (cstar/32) hL (by positivity)
  let Cmem := Cd*Ca
  let εsrc := cstar/(32*(4*L+2))
  have hεsrc : 0<εsrc := by positivity
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=Eis⧸Ideal.span {c}) rmax εsrc hεsrc
  let C := (‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*Cmem
  have hC : 0<C := by dsimp [C,Cmem]; positivity
  let Z₀ := max Zmem (Ideal.absNorm B:ℝ)
  have hZ₀ : 1<Z₀ := hZmem.trans_le (le_max_left _ _)
  obtain ⟨Dagg,hDagg,ha⟩ := completed_representative_aggregation (2*L+1) (cstar/32) (by linarith) (by positivity)
  let Z₁ := max Z₀ (max 2 (Ideal.absNorm B:ℝ))
  let ε := cstar/(64*(L+1))
  have hε : 0<ε := by positivity
  obtain ⟨D,hD,hcube⟩ := original_cube_shifted_tuple_energy rmax ε hε
  have hZ₁ := hZ₀.trans_le (le_max_left Z₀ (max 2 (Ideal.absNorm B:ℝ)))
  refine ⟨D*(Dagg*C),Z₁,by positivity,hZ₁,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod Hcube hcube0 hcuben u θ w hw
  have hz1  := (lt_of_lt_of_le hZ₁ hZ).le
  have hz  := lt_of_lt_of_le zero_lt_one hz1
  have hremain (T : Finset σ) :
      (∑ I∈parents,‖∑ a : ∀ i : T,cubeAwayList Hcube (lists i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
            (Z^(N-3*hhat)) (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤
      (Dagg*C)*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
    let activeLists (i : T) := cubeAwayList Hcube (lists i.val)
    have hactive (i : T) : activeLists i ⊆ lists i.val := Finset.filter_subset _ _
    let activeWidths (i : T) := H i.val
    let activeWeights (i : T) (P : activeLists i) := w i.val ⟨P.val,hactive i P.property⟩
    have hcardT : Fintype.card T ≤ rmax := by
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ T).trans hcard
    have hdisT : Pairwise (fun i j : T => Disjoint (activeLists i) (activeLists j)) :=
      fun i j hij => (hdis (fun heq => hij (Subtype.ext heq))).mono (hactive i) (hactive j)
    have hmaxT (i : T) P (hP : P ∈ activeLists i) := hmax i.val P (hactive i hP)
    have hgoodT (i : T) P (hP : P ∈ activeLists i) := hgood i.val P (hactive i hP)
    have hprimeT (i : T) P (hP : P ∈ activeLists i) := hprime i.val P (hactive i hP)
    have hoddT (i : T) P (hP : P ∈ activeLists i) := hodd i.val P (hactive i hP)
    have hHT (i : T) P (hP : P ∈ activeLists i) := hH i.val P (hactive i hP)
    have hwT (i : T) (P : activeLists i) := hw i.val ⟨P.val,hactive i P.property⟩
    have hH1T (i : T) := hH1 i.val
    have hprodT : (∏ i : T, activeWidths i) ≤ Z^z₀ := by
      apply le_trans ?_ hprod
      rw [Finset.prod_coe_sort T H]
      exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
        (fun i _ => zero_le_one.trans (hH1 i)) (fun i _ _ => hH1 i)
    let S := reflectionExcludedPrimes q
    let lists' := punctureLists activeLists S
    have hsub (i : T) : lists' i⊆activeLists i := Finset.filter_subset _ _
    let w' : ∀ i,lists' i→ℂ := fun i P => activeWeights i ⟨P.val,hsub i P.property⟩
    have hexcluded' (i : T) (P : Ideal Eis) (hP : P ∈ lists' i) : P ∉ reflectionExcludedPrimes q :=
      (Finset.mem_filter.mp hP).2
    have hdis' := fun i j hij => (hdisT hij).mono (hsub i) (hsub j)
    have hmax' i P (hP : P ∈ lists' i) := hmaxT i P (hsub i hP)
    have hgood' i P (hP : P ∈ lists' i) := hgoodT i P (hsub i hP)
    have hprime' i P (hP : P ∈ lists' i) := hprimeT i P (hsub i hP)
    have hodd' i P (hP : P ∈ lists' i) := hoddT i P (hsub i hP)
    have hH' i P (hP : P ∈ lists' i) := hHT i P (hsub i hP)
    have hw' i (P : lists' i) := hwT i ⟨P.val,hsub i P.property⟩
    let term (I : Ideal Eis) := ∑ p : ∀ i,lists' i,(∏ i,w' i (p i))*markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
        (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)
    calc
      _ = ∑ I ∈ parents, ‖term I‖^2 := by
        apply Finset.sum_congr rfl
        intro I hI
        exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_puncture_lists activeLists hprimeT S Ψ m
      (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) activeWeights)
      _ ≤ _ := by
          have hZZ  := (le_max_left _ _).trans hZ
          have hZ2  := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
          have hz1 : 1≤Z := by linarith
          have hzp : 0<Z := by linarith
          have hBn  := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hZ
          have hmaskEq : ActualFiber.maskIdeal q m F=B*F*Ideal.span {m} := by
            dsimp only [ActualFiber.maskIdeal,ActualFiber.maskElement,B]
            rw [←Ideal.span_singleton_mul_span_singleton]
            ring
          have hmaskn : (Ideal.absNorm (ActualFiber.maskIdeal q m F):ℝ)≤Z^(2*L+1) := by
            rw [hmaskEq]
            exact canonical_mask_norm_cap B F (Ideal.span {m}) Z V L L hz1 hBn hFn hRn hVc le_rfl
          have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2*L+1) := by
            intro I hI
            exact ⟨(hparents I hI).1,(hparents I hI).2.trans
              (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))⟩
          refine (ha Z hZ2 parents (ActualFiber.maskIdeal q m F) hparentn
            (ActualFiber.maskIdeal_ne_zero q m hm F hF.ne_zero) hmaskn
            (C*(1+‖θ‖)^degree*Z^(N+V-cstar/16))
            (fun I => ‖term I‖^2) (by positivity) ?_).trans_eq ?_
          · intro J hJmem
            have hJ := (hparents J hJmem).1
            have hJn := (hparents J hJmem).2
            let mfull := ActualFiber.maskElement q m
            have hmfull  := ActualFiber.maskElement_ne_zero q m hm
            let mask := Ideal.span {mfull}*F
            let Q₀ := Q*Ideal.span {(72:Eis)}
            have hmask : mask=B*F*Ideal.span {m} := by
              dsimp only [mask,mfull,ActualFiber.maskElement,B,b]
              rw [←Ideal.span_singleton_mul_span_singleton]
              ring
            have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hmfull) hF.ne_zero
            have hbad  := ActualFiber.mask_bad q m F
            let rows := originalResidualRows parents J mask
            have hparents0  := fun I hI => (hparents I hI).1
            let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F mfull hbad
            have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
              intro K hK
              obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
              exact residual_coprime_free_base q hq m F I
            have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := reflectionConductor_ideal q
            have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
              (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
            have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
              intro K hK
              refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
              obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
              obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
              exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
            have hLP : ∀ i,∀ P∈lists' i,IsCoprime Q₀ P := by
              intro i P hP
              let : P.IsMaximal := hmax' i P hP
              have hh := reflectionConductor_coprime_of_not_excluded q hq P (hexcluded' i P hP)
              rw [reflectionConductor_ideal] at hh
              exact hh.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))
            have hLN : ∀ i,∀ P∈lists' i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
              fun i P hP => maximal_prime_level_coprime P (hmax' i P hP) (hgood' i P hP) Q₀ c hcQ (hLP i P hP)
            have hz : 1<Z := lt_of_lt_of_le hZ₀ hZZ
            let O := normWidth Z (rowPowerfulPart J)
            have hO : 0≤O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
            have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
              have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
              linarith
            have hOM : O≤M := by
              have hh := Real.logb_le_logb_of_le hz hPowPos ((original_powerful_norm_le J hJ).trans hJn)
              rwa [Real.logb_rpow hzp (ne_of_gt hz)] at hh
            have hOn : Z^O≤(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
              dsimp [O,normWidth]
              rw [Real.rpow_logb hzp (ne_of_gt hz) hPowPos]
            let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
              ((residualOriginalData parents J F hF mfull hmfull hparents0 u K).fixedFactor Ψ Q) h
            have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
              (residualOriginalData parents J F hF mfull hmfull hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
            let FF := (poolPrimeFamily J mask Q₀).ideal
            have hall (g : Eis⧸Ideal.span {c}) (A : Finset (FreeReflection.pool J mask Q₀)) (U : Finset (↥T)) :
                InactiveChoiceEnergy (N := (9:Eis)*c) ((poolPrimeFamily J mask Q₀).restrict A) FF
                  (E g).shape (hEc g) (fun b : A => completedLocalExponent J F b.val.val) W
                  (Z^(N-3*hhat)) lists' hmax' hgood' rows hrows U activeWidths
                  (fun θ => Cmem*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O/2)) := by
              let G := (poolPrimeFamily J mask Q₀).restrict A
              exact inactive_choice_energy_of_active (N := (9:Eis)*c) G (poolPrimeFamily J mask Q₀).ideal (E g).shape (hEc g) (fun b : A => completedLocalExponent J F b.val.val) W (Z^(N-3*hhat))
                lists' hmax' hgood' rows hrows U activeWidths (fun i P hP => (hprime' i P hP).ne_zero) hH' (fun θ => Cmem*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O/2))
                (fun _ => by dsimp [Cmem]; positivity) (fun b => by
                let rowsb := inactiveRowSet rows lists' U FF b
                have hsub' : rowsb ⊆ rows := inactiveRowSet_subset FF lists' rows U b
                let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J mask):ℝ))
                let Hslot := Z^z₀
                let jF : A → ℕ := fun b => completedLocalExponent J F b.val.val
                have hrowNorm : ∀ K∈rowsb,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
                  fun K hK => original_residual_norm_bounds parents J mask hbad (Z^M) hparents K (hsub' hK)
                refine choice_energy_from_members G FF (E g).shape (hEc g) jF W (Z^(N-3*hhat))
                  (fun i : U => lists' i.val) (fun i => hmax' i.val) (fun i => hgood' i.val)
                  rowsb (fun K hK => hrows K (hsub' hK))
                  (fun i j hij => hdis' _ _ (fun h => hij (Subtype.ext h))) (fun i => hprime' i.val)
                  ((poolPrimeFamily J mask Q₀).restrict_pairwise (poolPrimeFamily_pairwise J mask Q₀) A)
                  (fun b => ⟨b.val,rfl⟩) (fun i : U => activeWidths i.val) Hrow Hslot
                  (fun i => hH' i.val) ((active_prod_le U activeWidths hH1T).trans hprodT) (fun f => hGN f.val) (fun f => (poolPrimeFamily_odd J mask Q₀) f.val)
                  (fun K hK => ⟨fun f => (hrowcop K (hsub' hK)).1 f.val, (hrowcop K (hsub' hK)).2⟩)
                  (fun i => hLN i.val) (fun i => hodd' i.val) hrowNorm
                  (fun θ => Ca*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O/2)) _ (fun θ => by positivity) ?_ ?_
                · intro θ
                  have hp : (1:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
                  have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J mask) :=
                    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) mask)
                  have hRpos : 0<Hrow := by dsimp [Hrow];positivity
                  have hScap : Hslot≤Z^L := Real.rpow_le_rpow_of_exponent_le hz.le hzc
                  have hRcap : Hrow≤Z^L := by
                    exact (div_le_self (Real.rpow_nonneg hzp.le _) (one_le_mul_of_one_le_of_one_le hp hm')).trans
                      (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
                  have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzp _) hRcap hScap
                  calc
                    _ ≤ (Cd*Z^(cstar/32))*(Ca*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O/2)) :=
                      mul_le_mul_of_nonneg_right hcount (by positivity)
                    _ = (Cd*Ca)*(1+‖θ‖)^degree*Z^(cstar/32+(N+V-3*cstar/16-O/2)) := by
                      rw [Real.rpow_add hzp];ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
                · intro tuples i j hi hj Rc Tc hmmax hg hRi hti hPupper
                  obtain ⟨I,hI0,hIn,hpow,hmaskI,hKlower,hKupper⟩ :=
                    exists_dyadic_parent parents rowsb J mask (Z^M) Hrow hparents hsub' hrowNorm i hi
                  have hmemb := hmember g (σ:=↥U) J I F (Ideal.span {m}) Q₀ hJ hI0 hF.ne_zero
                    (Ideal.span_singleton_eq_bot.not.mpr hm) hpow
                  rw [←hmask] at hmemb
                  exact hmemb hmaskI A
                    Z N V M z₀ margin O hhat d (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
                    ((le_max_left _ _).trans hZZ) hN hM hMc hVc hzc hhc hIn hFn hRn hO hOM (by rw [←hpow];exact hOn) hKlower
                    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
                    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper hinv hmargin hVd hhd hd
                    Rc Tc hj hmmax hg hti hRi)
            choose D hD using hall
            let energy := Cmem*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O/2)
            let harm := (∏ i,256*(columnDyadicLength (activeWidths i)+1:ℝ))^2
            let source := fun (g : Eis⧸Ideal.span {c}) (A : Finset (FreeReflection.pool J mask Q₀)) (U : Finset (↥T)) (K : rows) =>
              originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A) FF rows hrows lists' hmax' hgood' U
                (D g A U) (E g).shape (hEc g) (fun b : A => completedLocalExponent J F b.val.val)
                (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w' K
            let Labels := (Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J mask Q₀)×Finset (↥T))
            have hsum := frozen_inactive_sum_energy J F mask Q₀ activeWidths energy (by dsimp [energy]; positivity)
              thetaDerivativeScalar⁻¹ scalar hscalar source (fun g A U => hD g A U θ w' hw')
            have hJn'  := hJn.trans (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
            have hpool : (Ideal.absNorm (J*mask):ℝ)≤Z^(3*L+1) := by
              rw [map_mul,Nat.cast_mul]
              calc
                _ ≤ Z^L*Z^(2*L+1) := mul_le_mul hJn' hmaskn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
                _ = _ := by rw [←Real.rpow_add hzp];congr 1;ring
            have hbudget : εsrc*((3*L+1)+L)≤cstar/32 := by
              have heq : εsrc*(4*L+2)=cstar/32 := by dsimp [εsrc];field_simp
              have hh := mul_le_mul_of_nonneg_left (show (3*L+1)+L≤4*L+2 by linarith) hεsrc.le
              rwa [heq] at hh
            have hcst := hcost activeWidths hcardT hH1T J mask Q₀ hJ hmask0
              Z (3*L+1) L (cstar/32) hz hpool
              (hprodT.trans (Real.rpow_le_rpow_of_exponent_le hz.le hzc)) hbudget
            have henergy := hsum.trans (show _ ≤ C*(1+‖θ‖)^degree*Z^(N+V-cstar/16-O/2) by
              calc
                _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
                _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(cstar/32))*energy := by
                  apply mul_le_mul_of_nonneg_right _ (by dsimp [energy,Cmem];positivity)
                  exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
                _ = C*(1+‖θ‖)^degree*
                    Z^(cstar/32+(N+V-cstar/8-O/2)) := by
                  dsimp only [energy,C]
                  rw [Real.rpow_add hzp]
                  ring
                _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by dsimp [Cmem]; positivity)
            )
            have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
              CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
            have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
            have hTc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hTs
            have hmLam : ConcretePrimeRowBridge.goodLambda∣mfull :=
              ((reflectionExcludedGenerator_bad q).1).trans (dvd_mul_left _ m)
            have hm2 : (2:Eis)∣mfull := ((reflectionExcludedGenerator_bad q).2).trans (dvd_mul_left _ m)
            have hid (K : rows) := original_completed_residual_source parents J F hJ hF mfull hmfull hparents0 u hbad
              Q hQ c hc hcQ E hcop lists' hmax' hgood' hdis' hodd' hLP D Ψ hΨnorm hΨperiod hmLam hm2
              (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(N-3*hhat)) (Real.rpow_pos_of_pos hzp _) w' K
            have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
            convert henergy using 1
            · rw [original_fiber_energy_reindex _ _ _ hparents0, ←Finset.sum_coe_sort]
              exact Finset.sum_congr rfl fun K _ => congrArg (fun z : ℂ => ‖z‖^2) (hid K)
            · rw [show (N+V-cstar/16)-O/2=(N+V-cstar/16)+O*(-(1/2:ℝ)) by ring,
                Real.rpow_add hzp _ (O*(-(1/2:ℝ))),Real.rpow_mul hzp.le O,hp]
              ring
          · calc
              _ = (Dagg*C)*(1+‖θ‖)^degree*(Z^(cstar/32)*Z^(N+V-cstar/16)) := by ring
              _ = _ := by rw [←Real.rpow_add hzp]; congr 2; ring
  have hh := hcube Hcube hcube0 lists hmax hgood w hw hcard parents
    (fun I => rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
    (Z^(N-3*hhat)) ((Dagg*C)*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) (by positivity) hremain
  have hεcap : hhat*ε≤cstar/64 := by
    have hhε : ε*(64*(L+1))=cstar := by dsimp [ε];field_simp
    nlinarith [mul_le_mul_of_nonneg_right hhc hε.le]
  have hn : (Ideal.absNorm Hcube:ℝ)^ε≤Z^(cstar/64) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hcuben hε.le).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 hεcap
  apply hh.trans
  calc
    _ ≤ D*Z^(cstar/64)*((Dagg*C)*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) := by gcongr
    _ = (D*(Dagg*C))*(1+‖θ‖)^degree*(Z^(cstar/64)*Z^(N+V-cstar/32)) := by ring
    _ = _ := by rw [←Real.rpow_add hz];congr 2;ring
end
end SevenEighths.InverseReflectedPhase

end OAI
