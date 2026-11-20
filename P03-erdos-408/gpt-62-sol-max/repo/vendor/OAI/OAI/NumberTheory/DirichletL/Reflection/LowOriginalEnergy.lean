module

public import OAI.NumberTheory.DirichletL.Reflection.LowPunctureLists
public import OAI.NumberTheory.DirichletL.Reflection.CompletedAggregation
public import OAI.NumberTheory.DirichletL.Reflection.CompletedCanonicalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption
public import OAI.NumberTheory.DirichletL.Reflection.CompletedFiberSource
public import OAI.NumberTheory.DirichletL.Reflection.CellArithmetic
public import OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
public import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel
public import OAI.NumberTheory.DirichletL.Reflection.LowFrozenEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

set_option maxHeartbeats 600000 in
theorem low_original_completed_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+507*η) := by
  let Q₀ := Q*Ideal.span {(72:Eis)}
  let c : Eis := (9:Eis)*(ConcretePrimeRowBridge.idealGenerator Q)*(72:Eis)
  have hc : c≠0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)) (by norm_num)
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := by
    dsimp only [c,Q₀]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      ConcretePrimeRowBridge.span_idealGenerator]
    ring
  let  := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let mask := Ideal.span {m}*F
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let E := fixedFourierGeometry c hc
  have hEc  := fun h => (E h).denominator_ne_zero
  have hEN  := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_frozen_energy
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime)
    mask hmask0 Ck η hCk hη hη1 rmax
  obtain ⟨Dagg,hDagg,ha⟩ := completed_representative_aggregation 2 η (by norm_num) hη
  let Z₁ := max Z₀ (max 2 (max Ck (Ideal.absNorm mask:ℝ)))
  refine ⟨degree,Dagg*C,Z₁,mul_pos hDagg hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := actualPuncturePrimes lists m
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hLP (i : σ) (P : Ideal Eis) (hP : P∈lists' i) : IsCoprime (Q*Ideal.span {(72:Eis)}) P := by
    apply puncture_period_coprime _ m hperiod P (hmax i P (hsub i hP))
    intro hmP
    exact (Finset.mem_filter.mp hP).2 ((actualPuncturePrimes_mem lists m i P (hsub i hP)).mpr hmP)
  have hdis' := fun i j hij => (hdis hij).mono (hsub i) (hsub j)
  have hmax' i P (hP : P ∈ lists' i) := hmax i P (hsub i hP)
  have hgood' i P (hP : P ∈ lists' i) := hgood i P (hsub i hP)
  have hprime' i P (hP : P ∈ lists' i) := hprime i P (hsub i hP)
  have hodd' i P (hP : P ∈ lists' i) := hodd i P (hsub i hP)
  have hH' i P (hP : P ∈ lists' i) := hH i P (hsub i hP)
  have hw' i (P : lists' i) := hw i ⟨P.val,hsub i P.property⟩
  let term (I : Ideal Eis) := ∑ p : ∀ i,lists' i,(∏ i,w' i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)
  calc
    _ = ∑ I ∈ parents, ‖term I‖^2 := by
      apply Finset.sum_congr rfl
      intro I hI
      exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_actual_puncture_lists lists hprime Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w)
    _ ≤ _ := by
        have hZZ  := (le_max_left _ _).trans hZ
        have hZ2  := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
        have hz1 : 1≤Z := by linarith
        have hzp : 0<Z := by linarith
        have hCkZ  := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
        have hmaskZ  := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
        have hmaskn : (Ideal.absNorm mask:ℝ)≤Z^(2:ℝ) := hmaskZ.trans
          (by simpa using Real.rpow_le_rpow_of_exponent_le hz1 (show (1:ℝ)≤2 by norm_num))
        have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2:ℝ) := by
          intro I hI
          refine ⟨(hparents I hI).1,(hparents I hI).2.trans ?_⟩
          calc
            _ ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
            _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
        refine (ha Z hZ2 parents mask hparentn
          (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
          (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η))
          (fun I => ‖term I‖^2) (by positivity) ?_).trans_eq ?_
        · intro J hJmem
          have hJ := (hparents J hJmem).1
          have hJn := (hparents J hJmem).2
          let rows := originalResidualRows parents J mask
          have hparents0  := fun I hI => (hparents I hI).1
          let hrows  := originalResidualAdmissible parents J F m hbad
          have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
            intro K hK
            obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
            exact rowResidualPart_coprime_period I F Q₀ m hperiod
          have hGN  :=
            (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
          have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
            intro K hK
            refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
            obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
            obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
            exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
          have hLN  :=
            fun i P hP => maximal_prime_level_coprime P (hmax' i P hP) (hgood' i P hP) Q₀ c hcQ (hLP i P hP)
          have hz : 1<Z := lt_of_lt_of_le hZ₀ hZZ
          let O := normWidth Z (rowPowerfulPart J)
          have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
            have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
            linarith
          obtain ⟨D,hD⟩ := he (σ:=σ) J F Q₀ hJ hF.ne_zero Z d ell0 shift O
            hZZ hd hd1 hell hellcap hshift rfl hJn parents rows hparents (Finset.Subset.refl _) hbad
            hcard lists' H hdis' hmax' hgood' hprime' hrows hH1 hH' hprod hGN (poolPrimeFamily_odd J mask Q₀)
            hrowcop hLN hodd'
          let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
            ((residualOriginalData parents J F hF m hm hparents0 u K).fixedFactor Ψ Q) h
          have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
            (residualOriginalData parents J F hF m hm hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
          have henergy := hD θ w' scalar hw' hscalar
          have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
            CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
          have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
          have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
            HasCompactSupport.intro isCompact_Icc (fun x hx => by
              by_contra hn
              exact hx (hTs hn))
          have hid (K : rows) := original_completed_residual_source parents J F hJ hF m hm hparents0 u hbad
            Q hQ c hc hcQ E hcop lists' hmax' hgood' hdis' hodd' hLP D Ψ hΨnorm hΨperiod hmLam hm2
            (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(1+ell0+shift)) (Real.rpow_pos_of_pos hzp _) w' K
          have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
          convert henergy using 1
          · rw [original_fiber_energy_reindex _ _ _ hparents0, ←Finset.sum_coe_sort]
            exact Finset.sum_congr rfl fun K _ => congrArg (fun z : ℂ => ‖z‖^2) (hid K)
          · rw [show ((5/6-2*d)+506*η)-O/2=((5/6-2*d)+506*η)+O*(-(1/2:ℝ)) by ring,
              Real.rpow_add hzp _ (O*(-(1/2:ℝ))),Real.rpow_mul hzp.le O,hp]
            ring
        · calc
            _ = (Dagg*C)*(1+‖θ‖)^degree*(Z^η*Z^((5/6-2*d)+506*η)) := by ring
            _ = _ := by rw [←Real.rpow_add hzp]; congr 2; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
