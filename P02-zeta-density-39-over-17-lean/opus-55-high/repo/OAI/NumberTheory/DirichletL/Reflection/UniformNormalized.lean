module
public import OAI.NumberTheory.DirichletL.Reflection.UniformPhysical
public import OAI.NumberTheory.DirichletL.Reflection.NormalizedPhysical
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical ContDiff
open MeasureTheory InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {N a c : Eis} {mode : Bool}

theorem actual_physical_shape_uniform_type_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→ Fin 3) (m : ℕ)
      (T QK QP Qn Qb A C ε : ℝ), 0<T → 0<QK → 0<QP → 0<Qn → 0<Qb → 0≤C →
    let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
    let r := ramifiedScale 1 completedRamifiedStep m
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2*(frozenBranchScale F jF e)^2*
      (C*((kK*QK)*U*B*(kP*QP))^ε*((kK*QK)+U*B)*B*
        (U+(kP*QP)+(U*(kP*QP))^(2/3:ℝ))) ≤
    (A*Real.sqrt kn*kb)^2*(6*C)*Z ^(
      InverseTerminalWidths.reflectedExponent 0 (Real.logb Z (kK*QK))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
        (InverseTerminalWidths.ramifiedWidth Z m)
        (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK))
          (Real.logb Z (kP*QP)) (Real.logb Z T) F.ideal jF e) +
      ε*(Real.logb Z (kK*QK)+Real.logb Z U+Real.logb Z B+Real.logb Z (kP*QP))+η/2) := by
  pm_180
  pm_97 Z₀ hZ₀ he literal_threshold_error_uniform Cf η hCf hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ Z hZ F jF e m T QK QP Qn Qb A C ε hT hK hP hn hb hC
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let r := ramifiedScale 1 completedRamifiedStep m
  pm_3322
  pm_4952 hz
  have hr : 0< r := ramifiedScale_pos _ _ (by norm_num)
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

theorem normalized_surviving_physical_source_energy_type_uniform
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ) (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→ PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→ Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z ^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,C₀,C,hC₀,hC,hsource⟩ := surviving_physical_source_energy_type_uniform
    (N := N) (a := a) (c := c) (mode := mode)
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows W hWsupport hW
  pm_1558
  pm_3283
  pm_3282

end SevenEighths.InverseReflectedPhase

end OAI
