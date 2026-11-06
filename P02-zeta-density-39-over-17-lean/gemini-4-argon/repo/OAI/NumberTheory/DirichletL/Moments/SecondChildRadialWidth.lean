module
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondWidthDrop

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondChildRadialWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondActualWidth

theorem physicalBlock_live_dyadic_witness (η:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩

section Family
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith
