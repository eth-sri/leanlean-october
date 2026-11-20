module

public import OAI.NumberTheory.DirichletL.Reflection.SourcePhysical
public import OAI.NumberTheory.DirichletL.Reflection.SourceBudget
public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource
public import OAI.NumberTheory.DirichletL.Reflection.ChoiceEnergyData
public import OAI.NumberTheory.DirichletL.Reflection.DyadMemberEnergy
public import OAI.NumberTheory.DirichletL.Reflection.LowFixedMember
public import OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy
public import OAI.NumberTheory.DirichletL.Reflection.DyadBudget
public import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section

local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

set_option maxHeartbeats 1000000 in
theorem low_original_frozen_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) → (Ideal.absNorm J:ℝ)≤Ck*Z^(5/6-2*d) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
    Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J Q Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J Q Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J Q Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J Q Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η-O₀/2) := by
  obtain ⟨degree,Ca,Z₁,hCa,hZ₁,hmember⟩ := low_fixed_member_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  obtain ⟨Cd,hCd,hbins⟩ := actual_dyad_count_budget 8 η (by norm_num) hη
  let C := Cd * Ca
  let ε := η/8
  have hε : 0<ε := by positivity
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (max Ck (Ideal.absNorm Q:ℝ))
  refine ⟨degree,(‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C,Z₀,by dsimp [C]; positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F Q₀ hJ hF Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq hJn
    parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1  := (le_max_left _ _).trans hZ
  have hz  := lt_of_lt_of_le hZ₁ hz1
  have hzp  := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J Q Q₀).ideal
  have hall (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) :
      InactiveChoiceEnergy (N := Nlevel) ((poolPrimeFamily J Q Q₀).restrict A) FF
        (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W
        (Z^(1+ell0+shift)) lists hmax hgood rows hrows T H
        (fun θ => C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2)) := by
    let G := (poolPrimeFamily J Q Q₀).restrict A
    exact inactive_choice_energy_of_active (N := Nlevel) G (poolPrimeFamily J Q Q₀).ideal (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W (Z^(1+ell0+shift))
      lists hmax hgood rows hrows T H (fun i P hP => (hprime i P hP).ne_zero) hH (fun θ => C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2))
      (fun _ => by dsimp [C]; positivity) (fun b => by
      let rowsb := inactiveRowSet rows lists T FF b
      have hsub' : rowsb ⊆ rows := inactiveRowSet_subset FF lists rows T b
      have hCkZ : Ck ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
      let Hrow := (Ck*Z^(5/6-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
      let Hslot := Z^ell0
      let jF : A → ℕ := fun b => completedLocalExponent J F b.val.val
      have hrowNorm : ∀ K∈rowsb,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
        fun K hK => original_residual_norm_bounds parents J Q hbad (Ck*Z^(5/6-2*d)) hparents K (hsub (hsub' hK))
      refine choice_energy_from_members G FF (s g) (hc₀ g) jF W (Z^(1+ell0+shift))
        (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val)
        rowsb (fun K hK => hrows K (hsub' hK))
        (fun i j hij => hdis (fun h => hij (Subtype.ext h))) (fun i => hprime i.val)
        ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
        (fun b => ⟨b.val,rfl⟩) (fun i : T => H i.val) Hrow Hslot
        (fun i => hH i.val) ((active_prod_le T H hH1).trans hprod) (fun f => hGN f.val) (fun f => hGchar f.val)
        (fun K hK => ⟨fun f => (hrowcop K (hsub' hK)).1 f.val, (hrowcop K (hsub' hK)).2⟩)
        (fun i => hLN i.val) (fun i => hLchar i.val) hrowNorm
        (fun θ => Ca*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2)) _ (fun θ => by positivity) ?_ ?_
      · intro θ
        have hp : (1:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
        have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J Q) :=
          QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) Q)
        have hRpos : 0<Hrow := by dsimp [Hrow];positivity
        have hScap : Hslot≤Z^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
        have hRcap : Hrow≤Z^(8:ℝ) := by
          apply (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hp hm')).trans
          calc
            Ck*Z^(5/6-2*d) ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
            _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
        have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzp _) hRcap hScap
        calc
          _ ≤ (Cd*Z^(η))*(Ca*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2)) :=
            mul_le_mul_of_nonneg_right hcount (by positivity)
          _ = (Cd*Ca)*(1+‖θ‖)^degree*Z^(η+((5/6-2*d)+504*η-O₀/2)) := by
            rw [Real.rpow_add hzp];ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
      · intro tuples i j hi hj Rc Tc hm hg hRi hti hPupper
        obtain ⟨I,hI0,hIn,hpow,hmask,hKlower,hKupper⟩ :=
          exists_dyadic_parent parents rowsb J Q (Ck*Z^(5/6-2*d)) Hrow hparents (hsub'.trans hsub) hrowNorm i hi
        exact hmember g J I F Q₀ hJ hI0 hF hpow hmask A
          Z d ell0 shift O₀ (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
          hz1 hd hd1 hell hellcap hshift (by rw [←hpow];exact hOeq) hIn hKlower
          (by linarith [divisorDyadicScale_ge_one i.val]) (by simpa only [mul_assoc] using hKupper)
          (by linarith [divisorDyadicScale_ge_one j.val]) hPupper
          Rc Tc hj hm hg hti hRi)
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) (K : rows) =>
    originalInactivePhysical ((poolPrimeFamily J Q Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K
  let Labels := γ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)
  apply (frozen_inactive_sum_energy J F Q Q₀ H energy (by dsimp [energy]; positivity)
    thetaDerivativeScalar⁻¹ scalar hscalar source (fun g A T => hD g A T θ w hw)).trans
  have hQn  := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hCkZ  := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hJcap : (Ideal.absNorm J:ℝ)≤Z^(2:ℝ) := by
    apply hJn.trans
    calc
      Ck*Z^(5/6-2*d) ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  have hpool : (Ideal.absNorm (J*Q):ℝ)≤Z^(3:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^(2:ℝ)*Z := mul_le_mul hJcap hQn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by norm_num;ring
  have hslot : (∏ i,H i)≤Z^(2:ℝ) := hprod.trans
    (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith))
  have hcst := hcost H hcard hH1 J Q Q₀ hJ hQ Z 3 2 η hz hpool hslot (by dsimp [ε];linarith)
  calc
    _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(η))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy,C];positivity)
      exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
    _ = ((‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C)*(1+‖θ‖)^degree*
        Z^(η+((5/6-2*d)+505*η-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by dsimp [C]; positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
