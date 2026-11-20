module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Reflection.UniformSieve
public import OAI.NumberTheory.DirichletL.Reflection.Surviving
public import OAI.NumberTheory.DirichletL.Reflection.KernelAdmissible
public import OAI.NumberTheory.DirichletL.Inversion.ReflectedArithmeticHeight
public import OAI.NumberTheory.DirichletL.Reflection.UpperThreshold
public import OAI.NumberTheory.DirichletL.Reflection.SectorData
public import OAI.NumberTheory.DirichletL.Reflection.ShellRows

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
open InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

private theorem actual_physical_shape_uniform_type_uniform {a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (m : ℕ)
      (T QK QP Qn Qb A C ε : ℝ), 0<T → 0<QK → 0<QP → 0<Qn → 0<Qb → 0≤C →
    let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
    let r := ramifiedScale 1 completedRamifiedStep m
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2*(frozenBranchScale F jF e)^2*
      (C*((kK*QK)*U*B*(kP*QP))^ε*((kK*QK)+U*B)*B*
        (U+(kP*QP)+(U*(kP*QP))^(2/3:ℝ))) ≤
    (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
      InverseTerminalWidths.reflectedExponent 0 (Real.logb Z (kK*QK))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
        (InverseTerminalWidths.ramifiedWidth Z m)
        (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK))
          (Real.logb Z (kP*QP)) (Real.logb Z T) F.ideal jF e) +
      ε*(Real.logb Z (kK*QK)+Real.logb Z U+Real.logb Z B+Real.logb Z (kP*QP))+η/2) := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Ideal.absNorm_pos_of_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hc)
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,he⟩ := literal_threshold_error_uniform Cf η hCf hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ Z hZ F jF e m T QK QP Qn Qb A C ε hT hK hP hn hb hC
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let r := ramifiedScale 1 completedRamifiedStep m
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hr : 0<r := ramifiedScale_pos _ _ (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have hR : 0<R := by
    have hcc := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hh := physical_scalar_hybrid_shape F jF e Z r Qn Qb kn kb R A C (kK*QK) (kP*QP) ε
    hz hr hn hb hkn hkb hR hC (mul_pos hkK hK) (mul_pos hkP hP)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hC))
  apply Real.rpow_le_rpow_of_exponent_le hz.le
  have hthreshold := actual_kernel_upper_threshold F jF e s hc m Z T QK QP Qn Qb kK kP kn kb
    hT hK hP hn hb hkK hkP hkn hkb
  have hexp := he Z hZ m 0 (Real.logb Z (kK*QK))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
    (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP))
      (Real.logb Z T) F.ideal jF e)
  change Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R = _ at hthreshold
  rw [hthreshold]
  linarith

theorem sector_normalized_literal_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (η : ℝ) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c∣N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f,jF f<6) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) F rows Pset S hrows s hc),
      (∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ j,IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal j)) →
      (∀ P∈Pset,∀ j,ringChar (Eis⧸(F.sum (S P)).ideal j)≠2) →
    ∀ (u : Eisˣ) (i : ℕ×ℕ×ℕ) (T θ QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<T → 1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
        (E.completion K) s hc u i W θ T r aw‖^2)≤
      ((branches.card:ℝ)*∑ e∈branches,
        (Real.exp (Real.log 2/2+Real.log 2))^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z QK)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z (QP/2))
            (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1)))
            (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2)))
            (InverseTerminalWidths.ramifiedWidth Z i.1)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z (QP/2)) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z QK+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+Real.logb Z (QP/2))+η/2))*
        (C₀*(1+‖θ‖)^degree)^2 := by
  let windows : Fin 4 → ℝ → ℂ := fun _ => completedShellWindow
  let M : Fin 4 → ℝ := fun _ => Real.log 2
  have hwindowNorm : ∀ i y, ‖windows i y‖≤1 := fun _ => completedShellWindow_norm
  have hwindows : ∀ i y, windows i y≠0 → |y|≤M i := fun _ => completedShellWindow_support
  obtain ⟨U,degree,C₀,hC₀,_,_,hsource⟩ := InverseReflectedArithmeticHeight.weighted_finite_physical_row_branch_measure_arithmetic_uniform
    lo hi hlo windows M (fun _ => Real.log_nonneg (by norm_num)) hwindows W hWs hW 0
  obtain ⟨C,hC,henergy⟩ := bounded_column_hybrid_energy_extracted_type_uniform ε hε
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨Z₀,hZ₀,hshape⟩ := actual_physical_shape_uniform_type_uniform s hc 1 (1/2) 1 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ F jF hN hbase hac hF hNF hcharF hj rows Pset S hrows' E
    hrowcop hproducts hScop hSN hSchar u i T θ QK QP r₀ aw₀ hT hX hQP' hKr hPr hr₀ haw₀
  let m := i.1
  let nset := reflectedNDyad i.2.2
  let bset := reflectedBDyad i.2.1
  let X := QK
  let Y := (2:ℝ)^i.2.2
  let B := (2:ℝ)^i.2.1
  let L := QP/2
  let Qn := Y
  let Qb := B
  let w₀ : Ideal Eis→Ideal Eis→ℂ := fun _ _ => 1
  have hw₀ (n b : Ideal Eis) : ‖w₀ n b‖ ≤ 1 := by simp [w₀]
  have hQK : 0 < QK := by linarith
  have hQP : 0 < QP := by linarith
  have hQn : 0 < Qn := by positivity
  have hQb : 0 < Qb := by positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hrows (K) (hK : K∈rows) : Admissible K ∧ (Ideal.absNorm K:ℝ)≤X :=
    ⟨hrows' K hK,(hKr K hK).2⟩
  have hn (n) (hn : n∈nset) : CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y :=
    ⟨(reflectedNDyad_bounds _ n hn).1,(reflectedNDyad_bounds _ n hn).2.2⟩
  have hb (b) (hb : b∈bset) : primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B :=
    ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩
  have hP (P) (hP : P∈Pset) : CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L := by
    simpa only [L,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hPr P hP
  let G0 := E.referencePrimes
  let D0 := E.referenceArithmetic
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
  let density := twistedDensity U W θ R
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let r := fun t K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ)
  let aw := fun t P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ)
  let w := fun t n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)
  obtain ⟨hsource',hdi,_,hl1,_⟩ := hsource (N:=N) (a:=a) (c:=c) (mode:=mode) (φ:=φ) (σ:=σ) F s hc u m θ T QK QP Qn Qb hT hQK hQP hQn hQb
  have hpair (K : rows) (P : Pset) (hKP : IsCoprime K.val P.val) :
      Pairwise (Function.onFun IsCoprime (F.reflected K.val (hrows K.val K.property).1 (S P.val)).ideal) := by
    apply F.reflected_pairwise _ _ _ hF
    · intro i j hij
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inr i)) ((F.sum (S P.val)).ideal (Sum.inr j))
      exact hScop P.val P.property (Sum.inr_injective.ne hij)
    · rw [hproducts P.val P.property]
      exact hKP
    · exact (hrowcop K.val K.property).1
    · intro f i
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inl f)) ((F.sum (S P.val)).ideal (Sum.inr i))
      exact hScop P.val P.property (Sum.inl_ne_inr : (Sum.inl f : φ⊕σ)≠Sum.inr i)
  have hn0  := fun n hn' => (hn n hn').1.1.ne_zero
  have hb0 : ∀ b ∈ bset, b≠0 := by
    intro b hb' hbzero
    exact (hb b hb').1 (by rw [hbzero,primaryGenerator_zero])
  have hidentity (K : rows) :
      weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (E.completion K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀ =
      (scalar:ℂ)*∫ t : ℝ, density t*∑ e∈branches,
        weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
          (r t) (aw t) (w t) u m Pset nset bset K.val := by
    simpa only [sum_branches_eq_surviving] using hsource' K.val (hrows K.val K.property).1 S jF Pset nset bset (E.completion K) hproducts hn0 hb0 r₀ aw₀ w₀
      G0 D0 (hpair K) (E.fixedFactor_eq K) (E.cuspColumn_eq K) (fun b hb' => (hb b hb').1)
  have hr (t) (K) (hK : K ∈ rows) : ‖r t K‖ ≤ 1 :=
    weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (hr₀ K hK) _ _ _ _ _
  have haw (t) (P) (hP : P ∈ Pset) : ‖aw t P‖ ≤ 1 :=
    weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (haw₀ P hP) _ _ _ _ _
  have hw (t n b) : ‖w t n b‖ ≤ 1 :=
    weightedKernelDual_norm windows M hwindowNorm hwindows _ (hw₀ n b) _ _ _ _ _
  let bound (e : φ → Fin 3) :=
    let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
    let Bq := extractedDualScale (frozenExtracted F jF e 2) B
    (frozenBranchScale F jF e)^2*(C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  let cap := (branches.card:ℝ)*∑ e∈branches,bound e
  have hcap : 0 ≤ cap := by
    refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun e _ => ?_)
    have hYq : 0 ≤ extractedDualScale (frozenExtracted F jF e 1) Y := zero_le_one.trans (le_max_left _ _)
    have hBq : 0 ≤ extractedDualScale (frozenExtracted F jF e 2) B := zero_le_one.trans (le_max_left _ _)
    dsimp [bound]; positivity
  let Ψ e t := weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
    (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset
  let ψ (K : rows) (t : ℝ) := ∑ e∈branches, Ψ e t K.val
  have hbranch (e) (t) : (∑ K ∈ rows, ‖Ψ e t K‖^2) ≤ bound e := by
    have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
      actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
        s hc hN hbase hac hF hNF hcharF hj u m
    have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
      rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
      exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
        (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
    have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m*aw t P‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2).trans
        (haw t P hP)
    apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
      (henergy X Y B L hX hL F hF jF e (fun n b => actualCuspColumn D0 s hc u m n b*w t n b)
        (actualCuspWeightedColumn_norm_le_one G0 D0 s hc u m (w t) (hw t))
        rows nset bset Pset (fun P => actualSlotPhase F (S P) jF s u m*aw t P) hrows hn hb hP hslot)
    dsimp [Ψ]
    have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
        actualRowPhaseExtension F jF s u m K*r t K‖ ≤ 1 := by
      simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK))).trans (hr t K hK)
    have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
        actualRowPhaseExtension F jF s u m K*r t K‖^2 ≤ 1 := (sq_le_one_iff₀ (norm_nonneg _)).mpr hphase
    rw [weightedReflectedBranchHybridRow,norm_mul,mul_pow]
    exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)
  have hbound (t) : (∑ K, ‖ψ K t‖^2) ≤ cap := by
    refine (Finset.sum_le_sum fun K _ => CubicEisenstein.norm_sum_sq_le_card branches (fun e => Ψ e t K.val)).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => ?_) (Nat.cast_nonneg _)
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖Ψ e t K‖^2)]
    exact hbranch e t
  have hψ (K : rows) : AEStronglyMeasurable (ψ K) volume := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun e _ => ?_
    exact weightedReflectedBranchHybridRow_aestronglyMeasurable volume F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (weightedKernelCoordinate_measurable windows M (r₀ K.val) 0 (-2) QK _)
      (fun P _ => weightedKernelCoordinate_measurable windows M (aw₀ P) 1 (-2) QP _)
      (fun n _ b _ => weightedKernelDual_measurable windows M (w₀ n b) Qn Qb _ _)
  have hint (K : rows) := hdi.mul_bdd (hψ K) (Filter.Eventually.of_forall fun t =>
    (Real.le_sqrt (norm_nonneg _) hcap).mpr
      ((Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)))
  have hIntegral := common_measure_energy volume density ψ cap hcap hdi.norm hint hbound
  have hR : 0<R := by
    have hCC := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hscalar : 0<scalar := by
    have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
    have hs := smallScalar_pos hR
    dsimp only [scalar]
    positivity
  have hl1' : (∫ t : ℝ, ‖density t‖)≤C₀*(1+‖θ‖)^degree := by
    simpa only [pow_zero,one_mul] using hl1
  have hsquare : (∫ t : ℝ, ‖density t‖)^2≤(C₀*(1+‖θ‖)^degree)^2 :=
    (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr hl1'
  dsimp only
  conv_lhs =>
    pattern Finset.sum _ _
    arg 2
    ext K
    rw [literalDyadicRow_eq_physical F K.val (hrows' K.val K.property) S jF Pset
      (E.completion K) s hc u i QK QP hQK hQP (hKr K.val K.property) hproducts
      (fun P hP => (hPr P hP).2) W θ T r₀ aw₀, hidentity K]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscalar, mul_pow]
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hIntegral (sq_nonneg _)).trans ?_
  rw [←mul_assoc]
  refine (mul_le_mul_of_nonneg_left hsquare (mul_nonneg (sq_nonneg _) hcap)).trans ?_
  dsimp only [cap,bound]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [mul_left_comm (scalar^2) (branches.card:ℝ)]
  rw [Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heY,heB⟩ := surviving_extracted_scales F hF jF (actualCuspColumn E.referenceArithmetic s hc u m)
    nset bset Y B (fun n h => ⟨(hn n h).1.2,(hn n h).2⟩) hb e he
  rw [heY,heB]
  have hee := hshape Z hZ F jF e m T QK QP Qn Qb (Real.exp (M 2/2+M 3)) C ε hT hQK hQP hQn hQb hC.le
  dsimp only at hee
  simpa only [M, scalar, R, Real.sqrt_one, mul_one, one_mul, ←mul_assoc, show (1/2:ℝ)*QP = QP/2 by ring] using hee

end
end SevenEighths.InverseReflectedPhase

end OAI
