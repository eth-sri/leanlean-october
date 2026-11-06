module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}

def delta (D:Parameters.HighData Δ) := D.t/4
def stageError (D:Parameters.HighData Δ) := D.t/4
def kappaPlain (_D:Parameters.HighData Δ) := 3/4+2*Δ

section
variable (D : Parameters.HighData Δ)


theorem fixed_parameters  :
    0<delta D ∧ delta D≤1/4 ∧ 0<stageError D ∧
    delta D+stageError D≤D.t ∧ 3/4<kappaPlain D ∧ 0<kappaPlain D := by
  have hΔ:0<Δ:=by linarith [D.t_pos,D.t_delta]
  dsimp [delta,stageError,kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma source_base_gt_one (_D:Parameters.HighData Δ)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap  :
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

end

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

section
variable (D : Parameters.HighData Δ) (F : Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i) (S : ProbeFinalAssembly.SourceData D) (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (bΦ : ℝ) (hU : 1<U)


include hU in
theorem actual_fiber_lengths  
      :
    0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact plain_length_eq F hU

lemma width_bands   m (hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  grind [delta, fixed_parameters, max]

include F Q hU in
theorem unmarked_state_admission  
     
         
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ 2*length U (U^F.m)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  grind

theorem source_label_fixed_allowance  
      :
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget   base :
    base+delta D+stageError D≤base+D.t := by
  linarith [(fixed_parameters D).2.2.2.1]

end

end SevenEighths.CenteredMomentDetectorPlainMomentParameters

end

end OAI
