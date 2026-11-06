module
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondUniformSubsetSource
open HeckeFamily
open CenteredMomentCommonRadialData










open CenteredMomentHeckeColumnWindow

open CenteredMomentSecondWindowBudget

open scoped HeckeO
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical



open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma control_mono {wlo whi : ℝ} (p : Profiles wlo whi)
    {S T : Finset (ℕ×ℕ)} (h : S⊆T) : p.control S≤p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma moment_mono {j k : ℕ} (h : j≤k) : profileMoment j≤profileMoment k := by
  apply integral_mono (columnDensity_moments _ logAnnulus_compact logAnnulus_smooth j)
    (columnDensity_moments _ logAnnulus_compact logAnnulus_smooth k)
  intro x
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg x]) h) (norm_nonneg _)

omit [DecidableEq ι] in
lemma factor_mono {wlo whi : ℝ} {S T : Finset (ℕ×ℕ)} (hST : S⊆T)
    (s : Input ι) (p : Profiles wlo whi) {j k : ℕ} (hjk : j≤k)
    (Q : Ideal O) {A B : ℝ} (hA : 0≤A) (hAB : A≤B) :
    profileFactor S s p j Q A≤profileFactor T s p k Q B := by
  have hp:=control_mono p hST
  have hpn:=p.control_nonneg S
  have hpn':=p.control_nonneg T
  have hm:=moment_mono hjk
  have hmn:=profileMoment_nonneg j
  have hmn':=profileMoment_nonneg k
  have hπ : (1:ℝ)≤1+2*Real.pi := by linarith [Real.pi_pos]
  have ht : (1:ℝ)≤1+‖s.t‖ := by linarith [norm_nonneg s.t]
  have h4 : 4*j≤4*k := Nat.mul_le_mul_left _ hjk
  have h2 : 2*j≤2*k := Nat.mul_le_mul_left _ hjk
  have hπpow:=pow_le_pow_right₀ hπ h4
  have htpow:=pow_le_pow_right₀ ht h2
  have hB : 0≤B := hA.trans hAB
  unfold profileFactor
  change A*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*j)*
    p.control S^2*(1+‖s.t‖)^(2*j)*slotControl s.toData^2*frozenProfile s^2*profileMoment j^2 ≤ _
  change _ ≤ B*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*k)*
    p.control T^2*(1+‖s.t‖)^(2*k)*slotControl s.toData^2*frozenProfile s^2*profileMoment k^2
  gcongr








