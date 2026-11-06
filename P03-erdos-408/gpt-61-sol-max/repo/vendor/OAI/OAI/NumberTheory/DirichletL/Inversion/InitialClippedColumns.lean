module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialProfile
public import OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
public import OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns


def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

theorem clippedTest_eq_source  w   c h x  :
    clippedTest w c h x = InverseInitialProfile.clippedSource w c h x := by
  unfold clippedTest childLogTest InverseInitialProfile.clippedSource
  ring

theorem child_test_clipping  w   {Z q}  (hZ : 0 < Z) (hq : 0 < q)
    (N h : ℝ) :
    childLogTest w h (q/Z^N) = logPhase h (Real.log (Z^(max 0 N-N))) *
      clippedTest w (Z^(max 0 N-N)) h (q/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,mul_comm] using
    InverseInitialProfile.clipped_column_source_identity w hZ hq N h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ)  :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns  pool   w   X   U  :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

section
variable (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f k : ActualEisensteinCubic.O) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (w : ℝ → ℂ)

theorem canonical_row_zero_of_freshColumns_empty
         
         
       X h  (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_eq_zero
  simp_all [primeProductNorm, freshColumns, secondChildColumn, childLogTest]

theorem canonical_row_clipping
         
         
       {Z}  (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      logPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem canonical_row_clipping_norm
         
         
       {Z}  (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots lists a w hZ N h,
    norm_mul,logPhase_norm,one_mul]

end

def columnEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (rows : Finset ActualEisensteinCubic.O) (D : Ideal ActualEisensteinCubic.O → ℝ)
    (W : ℝ → ℂ) (X : ℝ)  :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots lists a W X‖^2

section
variable (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal ActualEisensteinCubic.O)) (rows : Finset ActualEisensteinCubic.O) (D : Ideal ActualEisensteinCubic.O → ℝ)

theorem columnEnergy_clipping
         
         
         
     w   {Z}  (hZ : 0 < Z) (N h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  simp_all [columnEnergy, canonical_row_clipping_norm]

def normalizedColumnEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (rows : Finset ActualEisensteinCubic.O) (D : Ideal ActualEisensteinCubic.O → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ)  :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

theorem columnEnergy_normalization
         
         
         
     W   X   {Z}  (hZ : 0 < Z)  F  :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

theorem initial_columnEnergy_clipping_normalized
         
         
         
     w   {Z}  (hZ : 0 < Z)  N V h  :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z (max 0 N+V) := by
  rw [columnEnergy_clipping p hp hcop hg pool Ψ m slots lists a labels rows D w hZ N h]
  solve_by_elim [columnEnergy_normalization]

end

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ))  := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ))  := z.2 5+z.1.2.1-z.1.2.2

section
variable (z : Frequency × (Fin 6 → ℝ))

theorem leftHeight_eq   :
    leftHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 4 := by
  simp [leftHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

theorem rightHeight_eq   :
    rightHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 5 := by
  simp [rightHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

end

theorem child_height_moment_bound  K   z  :
    (1+‖leftHeight z‖)^K * (1+‖rightHeight z‖)^K ≤
      tripleHeight (2*K) z.1 * coordinateHeight (2*K) z.2 := by
  have hh := InverseAmbientProfileTower.inherited_pair_weight_bound 4 5 0 K z
  simpa only [InverseAmbientProfileTower.ambientWeight,
    InverseAmbientProfileTower.inheritedLeft,InverseAmbientProfileTower.inheritedRight,
    leftHeight,rightHeight,norm_neg,pow_zero,Finset.prod_const_one,
    mul_one,one_mul,zero_add,tripleHeight,coordinateHeight] using hh

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ)  :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

end SevenEighths.InverseInitialClippedColumns

end

end OAI
