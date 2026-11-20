module

public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource

@[expose] public section

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalWholeSource
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentExceptionalAsymmetricSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):ℝ:=
  p.control R*q.control R*(1+‖s.t‖)^J*(1+‖v.t‖)^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

lemma profileMass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):0≤profileMass R s v p q J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s
  have hv:=slotControl_nonneg v
  unfold profileMass
  positivity

theorem actual_masked_asymmetric (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Profiles wlo whi),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,ProfileAdmissible s p Q Z B r z) →
      (∀z∈rows,ProfileAdmissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass Sprofile s v p q J:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=allocated_amplitude_source_control wlo whi ε B hwlo hwhi hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  let Ca := C^2
  have hCa : 0 < Ca := sq_pos_of_pos hC
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass Sprofile s v p q J
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass Sprofile s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
        apply Finset.sum_le_sum
        intro z hzrow
        have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Profiles wlo whi)(r0:ℝ)
            (hs:ProfileAdmissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
            ‖amplitude s D a z‖≤C*p.control Sprofile*Z^ε*(1+‖s.t‖)^J*slotControl s*Real.sqrt (volume s)/
              (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
          have hpc := Profiles.control_nonneg p Sprofile
          obtain ⟨hP,hm,hA,hz0,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
          apply norm_le_of_squared _ _ _ _ _
          · exact mul_nonneg (by positivity) (slotControl_nonneg s)
          · exact (volume_pos s).le
          · exact s.reduction_pos D a
          · exact Real.rpow_pos_of_pos (hz) _
          · exact hbound (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
              α s Z hZ.1 hP z hm hA hz0 hml hm2 hcond hex D a r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂

        have hpc := Profiles.control_nonneg p Sprofile
        have hqc := Profiles.control_nonneg q Sprofile
        have hl:=hpoint I s p r (hs z hzrow) a
        have hr:=hpoint L v q rRight (hv z hzrow) b
        have hr':‖amplitude v D b z‖≤
            C*q.control Sprofile*Z^ε*(1+‖v.t‖)^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
          apply hr.trans
          apply div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg (by positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
            (v.reduction_pos D b)
          exact le_mul_of_one_le_right (v.reduction_pos D b).le (Real.one_le_rpow hZ.1.le (le_max_right _ _))
        apply (mul_le_mul hl hr' (norm_nonneg _) (by
          exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
            (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (hz).le _)))).trans_eq
        rw [←raw_cap_weight s v (hs z hzrow).1 D a b Z r hZ.1,
          ←reduction_cap_identity s v D a b Z r hZ.1]
        have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (hz).le,Real.rpow_two]
        rw [hp]
        dsimp [Ca,profileMass]
        ring
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];ring
  apply (whole_masked_le s v Ds rows).trans
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-max r 0)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs (max r 0)) (mul_nonneg (by positivity) (profileMass_nonneg Sprofile s v p q J))
    _=_:=by
      rw [show 2*ε+δ-max r 0=2*ε+(δ-max r 0) by ring,Real.rpow_add hz]
      ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
