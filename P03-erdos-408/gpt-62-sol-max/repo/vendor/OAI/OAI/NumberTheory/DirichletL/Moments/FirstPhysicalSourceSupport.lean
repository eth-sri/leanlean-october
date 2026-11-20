module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSourceSupport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem nonzero_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ∃a:columns C C hC.1 S,∃b:columns C D hD.1 S,
      c (C*(a:Ideal O))≠0 ∧ c (D*(b:Ideal O))≠0 ∧
      V 2 (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))≠0 ∧
      V 3 (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))≠0 := by
  unfold block at hn
  have hs:=right_ne_zero_of_mul hn
  obtain ⟨z,hz,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨a,ha,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨b,hb,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  dsimp only at hs
  split_ifs at hs with hab
  · have hprod:=left_ne_zero_of_mul (left_ne_zero_of_mul hs)
    have hc:=right_ne_zero_of_mul hprod
    have hw:=right_ne_zero_of_mul (left_ne_zero_of_mul hs)
    refine ⟨a,b,?_,?_,?_,?_⟩
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
    · have hh:=right_ne_zero_of_mul hc
      rw [star_ne_zero] at hh
      exact left_ne_zero_of_mul hh
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    · exact right_ne_zero_of_mul hw
  · exact False.elim (hs rfl)

theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(a₁ a₂:ℝ)(ha₁:0≤a₁)(ha₂:0≤a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hn:CenteredMomentOriginalCommonHarmonic.coefficient s R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  have hh:=profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ (Fintype.piFinset s.pools) I (by
      simpa only [CenteredMomentOriginalCommonHarmonic.coefficient] using hn)
  simpa only [map_one,Nat.cast_one,mul_one,div_one,volume,mul_assoc] using hh

lemma log_window_upper (N H M:ℝ)(hN:0<N)(hH:0<H)
    (hlog:|Real.log (N/H)|≤M):N≤Real.exp M*H := by
  have hl:Real.log (N/H)≤M:=(le_abs_self _).trans hlog
  have he:=Real.exp_le_exp.mpr hl
  rw [Real.exp_log (div_pos hN hH)] at he
  exact (div_le_iff₀ hH).mp he

theorem block_reference_lower (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ a T M:ℝ)
    (hA:0<A₀)(hB:0<B₀)(hsource:∀I,c I≠0→a*T≤(I.absNorm:ℝ))
    (hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    a*T≤(C.absNorm:ℝ)*Real.exp M*A₀ ∧
      a*T≤(D.absNorm:ℝ)*Real.exp M*B₀ := by
  obtain ⟨i,j,hi,hj,hwi,hwj⟩:=nonzero_columns η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀ hn
  have hiN:(0:ℝ)<(i:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C C hC.1 S i).1)
  have hjN:(0:ℝ)<(j:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD.1 S j).1)
  have hni:‖eisEmbedding (element C C hC.1 S i)‖^2=((i:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hnj:‖eisEmbedding (element C D hD.1 S j)‖^2=((j:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hli:=hwin 2 _ hwi
  have hlj:=hwin 3 _ hwj
  rw [hni] at hli
  rw [hnj] at hlj
  have hsi:=hsource _ hi
  have hsj:=hsource _ hj
  simp only [map_mul,Nat.cast_mul] at hsi hsj
  constructor
  · exact hsi.trans (by nlinarith [log_window_upper _ _ M hiN hA hli])
  · exact hsj.trans (by nlinarith [log_window_upper _ _ M hjN hB hlj])

lemma reference_sqrt_lower (NC ND A₀ B₀ a T M:ℝ)
    (hNC:0≤NC)(hND:0≤ND)(hA:0≤A₀)(_hB:0≤B₀)(ha:0≤a)(hT:0≤T)
    (hl:a*T≤NC*Real.exp M*A₀)(hr:a*T≤ND*Real.exp M*B₀):
    a*T≤Real.exp M*Real.sqrt (NC*ND)*(Real.sqrt A₀*Real.sqrt B₀) := by
  have hh:=mul_le_mul hl hr (mul_nonneg ha hT) (by positivity : 0≤NC*Real.exp M*A₀)
  have hs:(a*T)^2≤(NC*ND)*(Real.exp M)^2*(A₀*B₀):=by nlinarith [hh]
  have hsqrt:=Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (mul_nonneg ha hT),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hNC hND) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hNC hND),Real.sqrt_sq (Real.exp_pos M).le,
    Real.sqrt_mul hA] at hsqrt
  nlinarith [hsqrt]

end SevenEighths.CenteredMomentFirstPhysicalSourceSupport

end

end OAI
