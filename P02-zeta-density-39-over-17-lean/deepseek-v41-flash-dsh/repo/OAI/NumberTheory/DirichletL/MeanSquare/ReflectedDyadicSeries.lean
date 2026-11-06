module
public import OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

def initialBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

end

open ActualEisensteinCubic

theorem completed_conductor_norm_bound {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) :
    (Ideal.absNorm (∏i,P i):ℝ)≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  have hd : (∏i,P i)∣I*Q := Fintype.prod_dvd_of_coprime hcop hpool
  have hn : 0<Ideal.absNorm (I*Q) := Nat.pos_of_ne_zero (fun hz =>
    mul_ne_zero hI hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hh := Nat.le_of_dvd hn (map_dvd Ideal.absNorm hd)
  exact_mod_cast (by simpa only [map_mul] using hh)

def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0

theorem completedShellWindow_support (x : ℝ) (h : completedShellWindow x≠0) :
    |x|≤Real.log 2 := by
  have hx : -Real.log 2≤x ∧ x≤0 := by
    by_contra hn
    exact h (by simp [completedShellWindow,hn])
  apply abs_le.mpr
  exact ⟨hx.1,hx.2.trans (Real.log_nonneg (by norm_num))⟩

theorem completedShellWindow_norm (x : ℝ) : ‖completedShellWindow x‖≤1 := by
  unfold completedShellWindow
  split_ifs <;> simp

theorem completedShellWindow_log (x U : ℝ) (hx : 0<x) (hU : 0<U)
    (hlo : U/2≤x) (hhi : x≤U) : completedShellWindow (Real.log (x/U))=1 := by
  apply ite_eq_left
  constructor
  · have hhalf : (1/2:ℝ)≤x/U := (le_div_iff₀ hU).mpr (by linarith)
    have hh := Real.strictMonoOn_log.monotoneOn (by norm_num : (1/2:ℝ)∈Set.Ioi 0)
      (show x/U∈Set.Ioi 0 from div_pos hx hU) hhalf
    simpa only [one_div,Real.log_inv] using hh
  · exact Real.log_nonpos (div_nonneg hx.le hU.le) ((div_le_one hU).mpr hhi)

def reflectedDyadicCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r : ℝ)
    (n v : Ideal O) : ℂ :=
  η n v*reflectedBranch P hg j e
    (primaryGenerator (reflectionExtractedDivisor P j e 1*n))
    (primaryGenerator (reflectionExtractedDivisor P j e 2*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2*v):ℝ):ℝ):ℂ)

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def reflectedBranchBlock {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ)
    (σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  σ i k*completedSmoothDyadicBlock completedShellWindow completedShellWindow completedShellWindow
    W K Y ρ q S T (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1)) i k

end CompletedGauss

end

end OAI
