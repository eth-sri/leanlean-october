module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.FourierDecayCore
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.LogCurveDecoupling
public import LaterPairs.Native.ParabolaBilinearLocalization

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                         

                                                                               
                                                                        
                                                                         
                                                                         
                                                                       
                                                                      

                                                                            
                                                 

noncomputable section
open Set Filter MeasureTheory GafniTao
open scoped Topology ContDiff BigOperators FourierTransform ENNReal NNReal
namespace TaoTrudgianYang2025.LogarithmicSixth

def logRemainderCutoff (p : ℝ × ℝ) (s : ℝ) : ℂ :=
  (modelPhaseBufferedCutoff (-2) 2 (1/2) s : ℂ)*
    fordAdditiveCharacter (p.1*s^3*smoothLogCubicProfile (p.2*s))

private theorem logRemainderCutoff_joint_smooth :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => logRemainderCutoff q.1 q.2) := by
  have hcut : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      (modelPhaseBufferedCutoff (-2) 2 (1/2) q.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((modelPhaseBufferedCutoff_contDiff _ _ _).comp contDiff_snd)
  have hprofile : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      smoothLogCubicProfile (q.1.2*q.2)) :=
    smoothLogCubicProfile_smooth.comp ((contDiff_fst.snd).mul contDiff_snd)
  have hphase : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      q.1.1*q.2^3*smoothLogCubicProfile (q.1.2*q.2)) :=
    (((contDiff_fst.fst).mul (contDiff_snd.pow 3))).mul hprofile
  unfold logRemainderCutoff fordAdditiveCharacter
  exact hcut.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hphase)).cexp)

private theorem logRemainderCutoff_smooth (p : ℝ × ℝ) :
    ContDiff ℝ ∞ (logRemainderCutoff p) := by
  have hm : ContDiff ℝ ∞ (fun s : ℝ => (p,s)) := contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using logRemainderCutoff_joint_smooth.comp hm

private theorem logRemainderCutoff_support (p : ℝ × ℝ) :
    tsupport (logRemainderCutoff p) ⊆ Icc (-2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hk : s∈tsupport (modelPhaseBufferedCutoff (-2) 2 (1/2)) := by
    apply subset_closure
    intro hz
    exact hs (by rw [logRemainderCutoff,hz,Complex.ofReal_zero,zero_mul])
  have hb := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/2) hk
  constructor <;> linarith [hb.1,hb.2]

private theorem norm_slice_iteratedFDeriv
    (F : (ℝ × ℝ) × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (s : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun x => F (p,x)) s‖≤‖iteratedFDeriv ℝ j F (p,s)‖ := by
  let L : ℝ →L[ℝ] (ℝ × ℝ) × ℝ := ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
  have hL : ‖L‖=1 := ContinuousLinearMap.norm_inr ℝ (ℝ × ℝ) ℝ
  have hf : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => F ((p,0)+q)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he : (fun x => F (p,x))=(fun q => F ((p,0)+q)) ∘ L := by
    ext x; simp [L]
  rw [he,L.iteratedFDeriv_comp_right hf s (i:=j)
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)),iteratedFDeriv_comp_add_left]
  have hp : (p,0)+L s=(p,s) := by simp [L]
  rw [hp]
  have h := (iteratedFDeriv ℝ j F (p,s)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  simpa only [hL,Finset.prod_const_one,mul_one] using h

                                                                    
                                                                                
theorem logRemainderCutoff_jet_bound (j : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∀ s : ℝ, ‖iteratedDeriv j (logRemainderCutoff (a,b)) s‖≤C := by
  let F := fun q : (ℝ × ℝ) × ℝ => logRemainderCutoff q.1 q.2
  have hcont : Continuous (fun q => ‖iteratedFDeriv ℝ j F q‖) :=
    (logRemainderCutoff_joint_smooth.continuous_iteratedFDeriv
      (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
      (s:=(Icc (-1:ℝ) 1 ×ˢ Icc (-(1/4):ℝ) (1/4)) ×ˢ Icc (-2:ℝ) 2)
      hcont.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro a ha b hb s
  by_cases hs : s∈Icc (-2:ℝ) 2
  · have h := norm_slice_iteratedFDeriv F logRemainderCutoff_joint_smooth (a,b) s j
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    exact h.trans (by simpa only [norm_norm] using
      (hM ((a,b),s) ⟨⟨ha,hb⟩,hs⟩).trans (le_max_left M 1))
  · have hz : iteratedFDeriv ℝ j (logRemainderCutoff (a,b)) s=0 := by
      apply Function.notMem_support.mp
      intro h
      exact hs (logRemainderCutoff_support (a,b)
        (tsupport_iteratedFDeriv_subset j (subset_closure h)))
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv,hz,norm_zero]
    exact zero_le_one.trans (le_max_right M 1)

theorem logRemainderCutoff_fourier_decay (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∀ ξ : ℝ, (1+|ξ|)^j*‖𝓕 (logRemainderCutoff (a,b)) ξ‖≤C := by
  obtain ⟨C,hC,hzero⟩ := logRemainderCutoff_jet_bound 0
  obtain ⟨D,hD,hjet⟩ := logRemainderCutoff_jet_bound j
  refine ⟨(2:ℝ)^j*4*(C+D),by positivity,?_⟩
  intro a ha b hb ξ
  have h := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order j
    (logRemainderCutoff_smooth (a,b)) (by norm_num : (-2:ℝ)≤2)
    ((subset_tsupport _).trans (logRemainderCutoff_support (a,b)))
    (by linarith : 0≤C) (by linarith : 0≤D)
    (hzero a ha b hb) (hjet a ha b hb) ξ
  simpa only [show (2:ℝ)-(-2)=4 by norm_num] using h

                                                                           
                                                                            
theorem exists_logCubic_multiplier_kernel :
    ∃ C : ℝ, 0<C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∃ K : ℝ → ℂ, Continuous K ∧
        Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
        (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖)≤C ∧
        (∀ ξ : ℝ, ‖K ξ‖≤C/(1+|ξ|)^102) ∧
        ∀ s∈Icc (-1:ℝ) 1,
          fordAdditiveCharacter (a*s^3*logCubicProfile (b*s))=
            ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  let P := Icc (-1:ℝ) 1 ×ˢ Icc (-(1/4):ℝ) (1/4)
  have hd : ∃ D : ℝ, 0<D ∧ ∀ p∈P, ∀ ξ : ℝ, (1+|ξ|)^102*‖𝓕 (logRemainderCutoff p) ξ‖ ≤ D := by
    obtain ⟨D,hD,h⟩ := logRemainderCutoff_fourier_decay 102
    exact ⟨D,hD,fun p hp => h p.1 hp.1 p.2 hp.2⟩
  obtain ⟨C,hC,h⟩ := exists_cutoff_multiplier_kernel logRemainderCutoff
    (fun p s => p.1*s^3*logCubicProfile (p.2*s)) (fun p _ => (logRemainderCutoff_smooth p).continuous)
    (fun p _ => isCompact_Icc.of_isClosed_subset isClosed_closure (logRemainderCutoff_support p)) hd (by
      intro p hp s hs
      have hbs : |p.2*s| ≤ 1/2 := by
        rw [abs_mul]
        linarith [mul_le_mul (abs_le.mpr hp.2) (abs_le.mpr hs) (abs_nonneg s) (by norm_num)]
      rw [logRemainderCutoff,modelPhaseBufferedCutoff_one (by norm_num)
        (by linarith [hs.1]) (by linarith [hs.2]),Complex.ofReal_one,one_mul,smoothLogCubicProfile_agrees hbs])
  exact ⟨C,hC,fun a ha b hb => h (a,b) ⟨ha,hb⟩⟩

                                                                             
theorem logarithmic_physical_phase {A : ℝ} (hA : 0<A)
    (α t δ s : ℝ) (hs : 0<A+δ*s) :
    α*(A+δ*s)^2+t*Real.log (A+δ*s)=
      (α*A^2+t*Real.log A)+(2*A*δ*α+δ*t/A)*s+
        (δ^2*α-δ^2*t/(2*A^2))*s^2+
        (t*δ^3/A^3)*s^3*logCubicProfile (δ/A*s) := by
  have hn : 0<1+δ/A*s := by
    have he : 1+δ/A*s=(A+δ*s)/A := by field_simp
    rw [he]
    exact div_pos hs hA
  have hfactor : A+δ*s=A*(1+δ/A*s) := by field_simp
  have hlog : Real.log (A+δ*s)=Real.log A+Real.log (1+δ/A*s) := by
    rw [hfactor,Real.log_mul hA.ne' hn.ne']
  have he := logCubicProfile_identity (δ/A*s)
  rw [hlog]
  have hm := congrArg (fun x : ℝ => t*x) he
  field_simp at hm ⊢
  nlinarith only [hm]

                                                                         
                                                                          
theorem exists_logCubic_finite_moment :
    ∃ C : ℝ, 0<C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        ‖∑ i∈S, z i*fordAdditiveCharacter (a*(s i)^3*logCubicProfile (b*s i))‖^6≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i∈S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  obtain ⟨C,hC,hkern⟩ := exists_logCubic_multiplier_kernel
  refine ⟨C^6,by positivity,?_⟩
  intro a ha b hb ι S z s hs
  obtain ⟨K,hKc,hKi,hmass,henv,hrep⟩ := hkern a ha b hb
  exact finite_moment_of_multiplier S z s hs (fun x => a*x^3*logCubicProfile (b*x)) hC hKc hKi hmass henv hrep

                                                                         
                                                                          
theorem exists_logarithmic_physical_sixth_transfer :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) → ∀ (A δ t α : ℝ), 0<A →
      |δ/A|≤1/4 → |t*δ^3/A^3|≤1 →
      ‖∑ i∈S, z i*fordAdditiveCharacter
        (α*(A+δ*s i)^2+t*Real.log (A+δ*s i))‖^6≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i∈S, z i*fordAdditiveCharacter
            ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_logCubic_finite_moment
  refine ⟨C,hC,?_⟩
  intro ι S z s hs A δ t α hA hδ ht
  let l := 2*A*δ*α+δ*t/A
  let q := δ^2*α-δ^2*t/(2*A^2)
  let z' := fun i => z i*fordAdditiveCharacter (l*s i+q*(s i)^2)
  have h := hbound (t*δ^3/A^3) (abs_le.mp ht) (δ/A) (abs_le.mp hδ) S z' s hs
  have hpos (i : ι) (hi : i∈S) : 0<A+δ*s i := by
    have hb : |δ/A*s i|≤1/4 := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hδ (abs_le.mpr (hs i hi))
        (abs_nonneg (s i)) (by norm_num : (0:ℝ)≤1/4)
    have he : A+δ*s i=A*(1+δ/A*s i) := by field_simp
    rw [he]
    apply mul_pos hA
    linarith [(abs_le.mp hb).1]
  have hleft :
      (∑ i∈S, z i*fordAdditiveCharacter (α*(A+δ*s i)^2+t*Real.log (A+δ*s i)))=
        fordAdditiveCharacter (α*A^2+t*Real.log A)*
          (∑ i∈S, z' i*fordAdditiveCharacter
            ((t*δ^3/A^3)*(s i)^3*logCubicProfile (δ/A*s i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmic_physical_phase hA α t δ (s i) (hpos i hi)]
    dsimp only [z',l,q]
    simp only [fordAdditiveCharacter_add]
    ring
  have hright (ξ : ℝ) :
      (∑ i∈S, z' i*fordAdditiveCharacter (ξ*s i))=
        ∑ i∈S, z i*fordAdditiveCharacter ((l+ξ)*s i+q*(s i)^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [z']
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  rw [hleft,norm_mul,sargos_character_norm,one_mul]
  simpa only [hright,l,q] using h

                                                                                
private theorem logSix_periodic_unit_shift (f : ℝ → ℝ)
    (hp : Function.Periodic f 1) (a : ℝ) :
    (∫ v : ℝ in Icc (0:ℝ) 1, f (v+a))=∫ v : ℝ in Icc (0:ℝ) 1, f v := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_zero,add_comm] using hp.intervalIntegral_add_eq a 0

private theorem logSix_periodic_physical_window (f : ℝ → ℝ)
    (hf : Continuous f) (hp : Function.Periodic f 1) {A : ℝ} (hA : 0 < A) (η : ℝ) :
    (∫ t : ℝ in Icc (-A) A, f (2*t/A+η)) =
      2*A*(∫ u : ℝ in Icc (0:ℝ) 1, f u) := by
  have he (t : ℝ) : 2*t/A=t/(A/2) := by ring
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : -A ≤ A),
    intervalIntegral.integral_comp_div_add f (by positivity : A/2 ≠ 0)]
  have hleft : (-A)/(A/2)=(-2:ℝ) := by field_simp
  have hright : A/(A/2)=(2:ℝ) := by field_simp
  rw [hleft,hright]
  have hh := hp.intervalIntegral_add_zsmul_eq (4:ℤ) (-2+η)
    (fun a b => hf.intervalIntegrable a b)
  rw [hp.intervalIntegral_add_eq (-2+η) 0] at hh
  norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add] at hh
  have hend : -2+η+4=2+η := by ring
  rw [hend] at hh
  rw [hh,smul_eq_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ←integral_Icc_eq_integral_Ioc]
  ring

private theorem logSix_integer_character (k : ℤ) :
    fordAdditiveCharacter (k:ℝ)=1 := by
  unfold fordAdditiveCharacter
  have he : 2*Real.pi*Complex.I*((k:ℝ):ℂ)=(k:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

private def integerQuadraticSix {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (u v : ℝ) : ℝ :=
  ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6

private theorem integerQuadraticSix_continuous {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    Continuous (fun p : ℝ × ℝ => integerQuadraticSix S z m p.1 p.2) := by
  unfold integerQuadraticSix fordAdditiveCharacter
  fun_prop

private theorem integerQuadraticSix_periodic {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    (∀ v, Function.Periodic (fun u => integerQuadraticSix S z m u v) 1) ∧
      (∀ u, Function.Periodic (fun v => integerQuadraticSix S z m u v) 1) := by
  constructor
  · intro v u
    unfold integerQuadraticSix
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (m i:ℝ)*(u+1)+(m i:ℝ)^2*v =
      ((m i:ℝ)*u+(m i:ℝ)^2*v)+(m i:ℝ) by ring,
      fordAdditiveCharacter_add,logSix_integer_character,mul_one]
  · intro u v
    unfold integerQuadraticSix
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (m i:ℝ)*u+(m i:ℝ)^2*(v+1) =
      ((m i:ℝ)*u+(m i:ℝ)^2*v)+((m i)^2:ℤ) by push_cast; ring,
      fordAdditiveCharacter_add,logSix_integer_character,mul_one]

                                                                  
                                                                    
theorem logarithmic_quadratic_shear {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (m : ι → ℤ)
    {A δ : ℝ} (hA : A ≠ 0) (hδ : δ ≠ 0)
    (hm : ∀ i∈S, δ*s i=(m i:ℝ)-A) (α t ξ : ℝ) :
    ‖∑ i∈S, z i*fordAdditiveCharacter
      ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)‖^6 =
      ‖∑ i∈S, z i*fordAdditiveCharacter
        ((m i:ℝ)*(2*t/A+ξ/δ)+(m i:ℝ)^2*(α-t/(2*A^2)))‖^6 := by
  let u := 2*t/A+ξ/δ
  let v := α-t/(2*A^2)
  have he (i : ι) (hi : i∈S) :
      (2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2 =
        (-v*A^2-u*A)+((m i:ℝ)*u+(m i:ℝ)^2*v) := by
    have hm' : (m i:ℝ)=A+δ*s i := by linarith [hm i hi]
    rw [hm']
    dsimp only [u,v]
    field_simp
    ring
  have hsum :
      (∑ i∈S, z i*fordAdditiveCharacter
        ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)) =
      fordAdditiveCharacter (-v*A^2-u*A)*
        (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi,fordAdditiveCharacter_add]
    ring
  rw [hsum,norm_mul,sargos_character_norm,one_mul]

                                                                 
                                                                      
theorem logarithmic_quadratic_short_box {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (m : ι → ℤ)
    {A δ : ℝ} (hA : 0 < A) (hδ : δ ≠ 0)
    (hm : ∀ i∈S, δ*s i=(m i:ℝ)-A) (ξ : ℝ) :
    (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter
        ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)‖^6) =
      2*A*(∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6) := by
  let P := integerQuadraticSix S z m
  let F := fun u => ∫ v : ℝ in Icc (0:ℝ) 1, P u v
  have hPc : Continuous (fun p : ℝ × ℝ => P p.1 p.2) :=
    integerQuadraticSix_continuous S z m
  have hper := integerQuadraticSix_periodic S z m
  have hFc : Continuous F := by
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ:=volume) (f:=P) hPc 0 1
    simpa only [F,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using h
  have hFp : Function.Periodic F 1 := by
    intro u
    apply integral_congr_ae
    filter_upwards with v
    exact hper.1 v u
  simp_rw [logarithmic_quadratic_shear S z s m hA.ne' hδ hm]
  change (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
    P (2*t/A+ξ/δ) (α-t/(2*A^2)))=_
  have hinner (t : ℝ) : (∫ α : ℝ in Icc (0:ℝ) 1,
      P (2*t/A+ξ/δ) (α-t/(2*A^2)))=F (2*t/A+ξ/δ) := by
    simpa only [F,sub_eq_add_neg] using
      logSix_periodic_unit_shift (P (2*t/A+ξ/δ)) (hper.2 _) (-(t/(2*A^2)))
  simp_rw [hinner]
  rw [logSix_periodic_physical_window F hFc hFp hA (ξ/δ)]
  have hi : Integrable (fun p : ℝ × ℝ => P p.1 p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hPc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hswap := integral_integral_swap (μ:=volume.restrict (Icc (0:ℝ) 1))
    (ν:=volume.restrict (Icc (0:ℝ) 1)) (f:=P) hi
  exact congrArg (fun q : ℝ => 2*A*q) hswap

private theorem logSix_envelope_integrable :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) ∧
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹) ≤ Real.pi := by
  have hdom (ξ : ℝ) : ((1+|ξ|)^102)⁻¹ ≤ (1+ξ^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    calc
      1+ξ^2 ≤ (1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
      _ ≤ (1+|ξ|)^102 := pow_le_pow_right₀ (by linarith [abs_nonneg ξ]) (by norm_num)
  have hc : Continuous (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) :=
    (by fun_prop : Continuous (fun ξ : ℝ => (1+|ξ|)^102)).inv₀
      (fun ξ => by positivity)
  have hi := integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ ((1+|ξ|)^102)⁻¹)] using hdom ξ))
  refine ⟨hi,?_⟩
  have h := integral_mono hi integrable_inv_one_add_sq hdom
  simpa only [integral_univ_inv_one_add_sq] using h

                                                                      
                                                                           
                                                           
theorem exists_logarithmic_short_cell_quadratic :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ)
      (s : ι → ℝ) (m : ι → ℤ) (A δ : ℝ), 0 < A → δ ≠ 0 →
      |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
      (∀ i∈S, δ*s i=(m i:ℝ)-A) →
      (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6) ≤
        C*A*(∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6) := by
  obtain ⟨C,hC,htransfer⟩ := exists_logarithmic_physical_sixth_transfer
  refine ⟨2*C*Real.pi,by positivity,?_⟩
  intro ι S z s m A δ hA hδ hscale hcubic hs hm
  let B := Icc (-A) A ×ˢ Icc (0:ℝ) 1
  let P := fun p : ℝ × ℝ =>
    ‖∑ i∈S, z i*fordAdditiveCharacter ((p.2)*(m i:ℝ)^2+p.1*Real.log (m i:ℝ))‖^6
  let F := fun (ξ : ℝ) (p : ℝ × ℝ) =>
    ‖∑ i∈S, z i*fordAdditiveCharacter
      ((2*A*δ*p.2+δ*p.1/A+ξ)*s i+(δ^2*p.2-δ^2*p.1/(2*A^2))*(s i)^2)‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let J := ∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6
  have hPc : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hFc : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2) := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) (p : ℝ × ℝ) : ‖F ξ p‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (show 0 ≤ F ξ p by dsimp [F]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        ((2*A*δ*p.2+δ*p.1/A+ξ)*s i+(δ^2*p.2-δ^2*p.1/(2*A^2))*(s i)^2)‖ :=
        norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hiP : IntegrableOn P B :=
    hPc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hiV : Integrable V := logSix_envelope_integrable.1
  have hi1 : IntegrableOn (fun _p : ℝ × ℝ => (1:ℝ)) B :=
    integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  have hiF : Integrable (fun q : ℝ × (ℝ × ℝ) => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict B)) := by
    have h := (hiV.mul_prod hi1).mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using h
  have hpoint (p : ℝ × ℝ) (hp : p∈B) : P p ≤ C*(∫ ξ : ℝ, V ξ*F ξ p) := by
    have ht : |p.1/A| ≤ 1 := by
      rw [abs_div,abs_of_pos hA]
      exact (div_le_one hA).mpr (abs_le.mpr hp.1)
    have ht' : |p.1*δ^3/A^3| ≤ 1 := by
      have he : p.1*δ^3/A^3=(p.1/A)*(δ^3/A^2) := by field_simp
      rw [he,abs_mul]
      simpa only [one_mul] using mul_le_mul ht hcubic (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h := htransfer S z s hs A δ p.1 p.2 hA hscale ht'
    have he (i : ι) (hi : i∈S) : A+δ*s i=(m i:ℝ) := by linarith [hm i hi]
    have heSum :
        (∑ i∈S, z i*fordAdditiveCharacter
          (p.2*(A+δ*s i)^2+p.1*Real.log (A+δ*s i))) =
        ∑ i∈S, z i*fordAdditiveCharacter
          (p.2*(m i:ℝ)^2+p.1*Real.log (m i:ℝ)) :=
      Finset.sum_congr rfl (fun i hi => by rw [he i hi])
    simpa only [heSum,P,F,V] using h
  have hmain := setIntegral_mono_on hiP
    (hiF.integral_prod_right.const_mul C) (measurableSet_Icc.prod measurableSet_Icc) hpoint
  rw [integral_const_mul] at hmain
  have hswap := integral_integral_swap (μ:=volume) (ν:=volume.restrict B)
    (f:=fun ξ p => V ξ*F ξ p) hiF
  rw [←hswap] at hmain
  have hinner (ξ : ℝ) : (∫ p : ℝ × ℝ in B, F ξ p)=2*A*J := by
    have hFi : IntegrableOn (F ξ) B :=
      (hFc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    have hprod : Integrable (F ξ)
        ((volume.restrict (Icc (-A) A)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
      rw [Measure.prod_restrict]
      exact hFi
    have hi := integral_prod (F ξ) hprod
    rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hi
    change (∫ p : ℝ × ℝ in B, F ξ p)=_ at hi
    rw [hi]
    exact logarithmic_quadratic_short_box S z s m hA hδ hm ξ
  simp_rw [integral_const_mul,hinner] at hmain
  rw [integral_mul_const] at hmain
  have hJ : 0 ≤ J := integral_nonneg (fun _ => integral_nonneg (fun _ => by positivity))
  have hbound : C*((∫ ξ : ℝ, V ξ)*(2*A*J)) ≤ (2*C*Real.pi)*A*J := by
    have hv := mul_le_mul_of_nonneg_right logSix_envelope_integrable.2
      (show 0 ≤ 2*C*A*J by positivity)
    dsimp only [V]
    nlinarith only [hv]
  have hprodP : Integrable P
      ((volume.restrict (Icc (-A) A)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hiP
  have hleft := integral_prod P hprodP
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hleft
  change (∫ p : ℝ × ℝ in B, P p)=_ at hleft
  rw [hleft] at hmain
  exact hmain.trans hbound

                                                                  
                                                                              
theorem exists_logarithmic_short_cell_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨D,hD,hlog⟩ := exists_logarithmic_short_cell_quadratic
  obtain ⟨E,hE,hquad⟩ := exists_bourgain_quadratic_weighted_finite_interval hε
  refine ⟨D*E,by positivity,?_⟩
  intro Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  have h := hlog ι S z s m A δ hA hδ hscale hcubic hs hm
  have hq := hquad Q hQ ι S z m L B hB hinterval hz
  have hh := mul_le_mul_of_nonneg_left hq (mul_nonneg hD.le hA.le)
  exact h.trans (hh.trans_eq (by ring))

                                                                    
                                                                        
theorem exists_logarithmic_short_cell_sixth_translated {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B t₀ : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ))‖^6) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_short_cell_sixth hε
  refine ⟨C,hC,?_⟩
  intro Q hQ ι S z s m A δ B t₀ L hA hδ hB hscale hcubic hs hm hinterval hz
  let z' := fun i => z i*fordAdditiveCharacter (t₀*Real.log (m i:ℝ))
  have hz' (k : ℤ) : (∑ i∈S.filter (fun i => m i=k), ‖z' i‖) ≤ B := by
    simpa only [z',norm_mul,sargos_character_norm,mul_one] using hz k
  have hh := h Q hQ ι S z' s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz'
  have he (t α : ℝ) :
      (∑ i∈S, z' i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))) =
      ∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [z']
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  simpa only [he] using hh

                                                                    
                                                                      
theorem logSix_lorentz_of_window {A M : ℝ} (hA : 0 < A)
    (f : ℝ → ℝ) (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    (H : ℝ) (hb : ∀ t, ‖f t‖ ≤ H)
    (hwindow : ∀ x, (∫ t : ℝ in Icc (-A) A, f (t+x)) ≤ M) :
    (∫ t : ℝ, (1+(t/A)^2)⁻¹*f t) ≤ (3*Real.pi/2)*M := by
  let I := Icc (-A) A
  let W := fun t : ℝ => (1+(t/A)^2)⁻¹
  have hW : Integrable W := integrable_inv_one_add_sq.comp_div hA.ne'
  have hWf := hW.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hshift (x t : ℝ) (ht : t∈I) : W (x+t) ≤ 3*W x := by
    have ht' : |t/A| ≤ 1 := by
      rw [abs_div,abs_of_pos hA]
      exact (div_le_one hA).mpr (abs_le.mpr ht)
    have ht₂ : (t/A)^2 ≤ 1 := by
      simpa only [one_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg (t/A)) ht' 2
    dsimp only [W]
    rw [add_div,←one_div,←one_div,mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (x/A+2*(t/A))]
  have hpoint (t : ℝ) (ht : t∈I) :
      (∫ x : ℝ, W x*f x) ≤ 3*(∫ x : ℝ, W x*f (x+t)) := by
    have hiR := hW.mul_bdd
      (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hb (x+t)))
    calc
      _ = ∫ x : ℝ, W (x+t)*f (x+t) :=
        (integral_add_right_eq_self (μ:=volume) (fun x => W x*f x) t).symm
      _ ≤ ∫ x : ℝ, 3*(W x*f (x+t)) :=
        integral_mono (hWf.comp_add_right t) (hiR.const_mul 3)
          (fun x => (mul_le_mul_of_nonneg_right (hshift x t ht) (hf₀ (x+t))).trans_eq (by ring))
      _ = _ := integral_const_mul 3 _
  have hi1 : IntegrableOn (fun _t : ℝ => (1:ℝ)) I :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiF : Integrable (fun p : ℝ × ℝ => W p.1*f (p.1+p.2))
      (volume.prod (volume.restrict I)) := by
    have h := (hW.mul_prod hi1).mul_bdd
      (hf.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hb (p.1+p.2)))
    convert h using 1
    funext p
    simp only [mul_one,Function.comp_apply,Pi.add_apply]
  have hiConst : IntegrableOn (fun _t : ℝ => ∫ x : ℝ, W x*f x) I :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmain := setIntegral_mono_on hiConst (hiF.integral_prod_right.const_mul 3)
    measurableSet_Icc hpoint
  rw [setIntegral_const,integral_const_mul] at hmain
  have hmassI : volume.real I=2*A := by
    dsimp only [I]
    rw [Real.volume_real_Icc_of_le (by linarith : -A ≤ A)]
    ring
  rw [hmassI,smul_eq_mul] at hmain
  have hswap := integral_integral_swap (f:=fun x t : ℝ => W x*f (x+t)) hiF
  rw [←hswap] at hmain
  simp_rw [integral_const_mul] at hmain
  have hinner (x : ℝ) : (∫ t : ℝ in I, f (x+t)) ≤ M := by
    simpa only [add_comm,I] using hwindow x
  have hiAvg : Integrable (fun x => W x*(∫ t : ℝ in I, f (x+t))) := by
    simpa only [integral_const_mul] using hiF.integral_prod_left
  have hle := integral_mono hiAvg (hW.mul_const M)
    (fun x => mul_le_mul_of_nonneg_left (hinner x) (by positivity))
  have hmassW : (∫ x : ℝ, W x)=A*Real.pi := by
    have h := Measure.integral_comp_div (fun y : ℝ => (1+y^2)⁻¹) A
    simpa only [W,integral_univ_inv_one_add_sq,abs_of_pos hA,smul_eq_mul] using h
  rw [integral_mul_const,hmassW] at hle
  have hh : 2*A*(∫ x : ℝ, W x*f x) ≤ 3*(A*Real.pi*M) := hmain.trans (by gcongr)
  apply (mul_le_mul_iff_right₀ (show 0 < 2*A by positivity)).mp
  nlinarith only [hh]

                                                                   
                                                                         
                                              
theorem exists_logarithmic_short_cell_lorentz {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_short_cell_sixth_translated hε
  refine ⟨(3*Real.pi/2)*C,by positivity,?_⟩
  intro Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  let f := fun t => ∫ α : ℝ in Icc (0:ℝ) 1, P t α
  have hPc : Continuous (Function.uncurry P) := by
    unfold P Function.uncurry fordAdditiveCharacter
    fun_prop
  have hfc : Continuous f := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ:=volume) (f:=P) hPc 0 1
    simpa only [f,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hh
  have hf₀ (t : ℝ) : 0 ≤ f t := integral_nonneg (fun α => by dsimp [P]; positivity)
  have hPb (t α : ℝ) : ‖P t α‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (show 0 ≤ P t α by dsimp [P]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hfb (t : ℝ) : ‖f t‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    have hh := norm_setIntegral_le_of_norm_le_const_ae
      (μ:=volume) (s:=Icc (0:ℝ) 1) (f:=P t) isCompact_Icc.measure_lt_top
      (Filter.Eventually.of_forall (fun α => hPb t α))
    simpa only [f,Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1),
      sub_zero,mul_one] using hh
  have hwindow (x : ℝ) : (∫ t : ℝ in Icc (-A) A, f (t+x)) ≤
      C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) :=
    h Q hQ ι S z s m A δ B x L hA hδ hB hscale hcubic hs hm hinterval hz
  have hh := logSix_lorentz_of_window hA f hfc hf₀ ((∑ i∈S, ‖z i‖)^6) hfb hwindow
  exact hh.trans_eq (by ring)

private theorem logSix_lorentz_periodic (f : ℝ → ℝ)
    (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    (H : ℝ) (hb : ∀ t, ‖f t‖ ≤ H) (hp : Function.Periodic f 1) :
    (∫ t : ℝ, (1+t^2)⁻¹*f t) ≤ 3*Real.pi*(∫ u : ℝ in Icc (0:ℝ) 1, f u) := by
  have hwindow (x : ℝ) : (∫ t : ℝ in Icc (-1:ℝ) 1, f (t+x)) =
      2*(∫ u : ℝ in Icc (0:ℝ) 1, f u) := by
    rw [integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
      intervalIntegral.integral_comp_add_right]
    have hh := hp.intervalIntegral_add_zsmul_eq (2:ℤ) (-1+x)
      (fun a b => hf.intervalIntegrable a b)
    rw [hp.intervalIntegral_add_eq (-1+x) 0] at hh
    norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add] at hh
    rw [show -1+x+2=1+x by ring] at hh
    rw [hh,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      ←integral_Icc_eq_integral_Ioc]
  have h := logSix_lorentz_of_window (by norm_num : (0:ℝ) < 1)
    f hf hf₀ H hb (fun x => (hwindow x).le)
  simp only [div_one] at h
  exact h.trans_eq (by ring)

private theorem logSix_lorentz_second_coordinate
    (P : ℝ → ℝ → ℝ) (hPc : Continuous (Function.uncurry P))
    (hP₀ : ∀ t α, 0 ≤ P t α) (H : ℝ) (hPb : ∀ t α, ‖P t α‖ ≤ H)
    (hper : ∀ t, Function.Periodic (P t) 1)
    (W : ℝ → ℝ) (hW : Integrable W) (hW₀ : ∀ t, 0 ≤ W t) :
    (∫ t : ℝ, W t*(∫ α : ℝ, (1+α^2)⁻¹*P t α)) ≤
      3*Real.pi*(∫ t : ℝ, W t*(∫ α : ℝ in Icc (0:ℝ) 1, P t α)) := by
  have hperiod (t : ℝ) :
      (∫ α : ℝ, (1+α^2)⁻¹*P t α) ≤
        3*Real.pi*(∫ α : ℝ in Icc (0:ℝ) 1, P t α) :=
    logSix_lorentz_periodic (P t) (hPc.comp (continuous_const.prodMk continuous_id))
      (hP₀ t) H (hPb t) (hper t)
  have hi1 : IntegrableOn (fun _α : ℝ => (1:ℝ)) (Icc (0:ℝ) 1) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiC : Integrable (fun p : ℝ × ℝ => W p.1*P p.1 p.2)
      (volume.prod (volume.restrict (Icc (0:ℝ) 1))) := by
    have hi := (hW.mul_prod hi1).mul_bdd hPc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hPb p.1 p.2))
    convert hi using 1
    funext p
    simp only [mul_one,Function.uncurry]
  have hiAvg : Integrable (fun t => W t*(∫ α : ℝ in Icc (0:ℝ) 1, P t α)) := by
    simpa only [integral_const_mul] using hiC.integral_prod_left
  have hmain :
      (∫ t : ℝ, W t*(∫ α : ℝ, (1+α^2)⁻¹*P t α)) ≤
      ∫ t : ℝ, 3*Real.pi*(W t*(∫ α : ℝ in Icc (0:ℝ) 1, P t α)) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => mul_nonneg
        (hW₀ t)
        (integral_nonneg (fun α => mul_nonneg (by positivity) (hP₀ t α)))))
      (hiAvg.const_mul (3*Real.pi))
    filter_upwards with t
    exact (mul_le_mul_of_nonneg_left (hperiod t)
      (hW₀ t)).trans_eq (by ring)
  rw [integral_const_mul] at hmain
  exact hmain

private theorem logarithmic_product_weight_period_reduction {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {A : ℝ} (hA : 0 < A) :
    (∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ, (1+α^2)⁻¹*
      ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) ≤
      3*Real.pi*(∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) := by
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  have hPc : Continuous (Function.uncurry P) := by
    unfold P Function.uncurry fordAdditiveCharacter
    fun_prop
  have hP₀ (t α : ℝ) : 0 ≤ P t α := by dsimp [P]; positivity
  have hPb (t α : ℝ) : ‖P t α‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (hP₀ t α)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hper (t : ℝ) : Function.Periodic (P t) 1 := by
    intro α
    unfold P
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (α+1)*(m i:ℝ)^2+t*Real.log (m i:ℝ) =
      (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))+((m i)^2:ℤ) by push_cast; ring,
      fordAdditiveCharacter_add,logSix_integer_character,mul_one]
  exact logSix_lorentz_second_coordinate P hPc hP₀ ((∑ i∈S, ‖z i‖)^6)
    hPb hper (fun t => (1+(t/A)^2)⁻¹)
    (integrable_inv_one_add_sq.comp_div hA.ne') (fun t => by positivity)

                                                                         
                                                                              
theorem exists_logarithmic_short_cell_product_weight {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ, (1+α^2)⁻¹*
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_short_cell_lorentz hε
  refine ⟨3*Real.pi*C,by positivity,?_⟩
  intro Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  have hmain := logarithmic_product_weight_period_reduction S z m hA
  have hsource := h Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  have hh := mul_le_mul_of_nonneg_left hsource (show 0 ≤ 3*Real.pi by positivity)
  exact hmain.trans (hh.trans_eq (by ring))

                                                                
                                                                       
theorem logarithmic_physical_band_gap {X δ ξ η : ℝ}
    (hX : 1 ≤ X) (hδ : 4/X ≤ δ^2)
    (hgap : δ^2 ≤ logCurveBandGauge (1/4) ξ η) :
    1/100 ≤ |X^2*ξ/4| ∨ 1/(100*X) ≤ |ξ/8-η/64| := by
  have hX₀ : 0 < X := by linarith
  by_contra h
  push Not at h
  have hξsmall : X^2*|ξ|/4 < (1/100:ℝ) := by
    simpa only [abs_div,abs_mul,abs_of_nonneg (sq_nonneg X),
      abs_of_pos (by norm_num : (0:ℝ) < 4)] using h.1
  have hξ : X*|ξ| < (1/25:ℝ) := by
    have hx := mul_le_mul_of_nonneg_right
      (show X ≤ X^2 by nlinarith) (abs_nonneg ξ)
    nlinarith only [hξsmall,hx]
  have hv : X*|ξ/8-η/64| < (1/100:ℝ) := by
    have hh : |ξ/8-η/64| < (1/100)/X := by
      convert h.2 using 1
      ring
    have hh' := (lt_div_iff₀ hX₀).mp hh
    simpa only [mul_comm] using hh'
  have hη : X*|η| < 1 := by
    have hh : |η| ≤ 8*|ξ|+64*|ξ/8-η/64| := by
      have he : η=8*ξ-64*(ξ/8-η/64) := by ring
      calc
        |η| = |8*ξ-64*(ξ/8-η/64)| := congrArg abs he
        _ ≤ |8*ξ|+|64*(ξ/8-η/64)| := abs_sub _ _
        _ = _ := by norm_num [abs_mul]
    have hh' := mul_le_mul_of_nonneg_left hh hX₀.le
    nlinarith only [hh',hξ,hv]
  have hGauge : logCurveBandGauge (1/4) ξ η ≤ (25/16:ℝ)*(|η|+2*|ξ|) := by
    have hsec : |η-2*(ξ/(1+(1/4:ℝ)))| ≤ |η|+2*|ξ| := by
      have hh := abs_sub η (2*(ξ/(1+(1/4:ℝ))))
      norm_num [abs_mul,abs_div] at hh ⊢
      linarith [abs_nonneg ξ]
    have hmax : max |η| |η-2*(ξ/(1+(1/4:ℝ)))| ≤ |η|+2*|ξ| :=
      max_le (by linarith [abs_nonneg ξ]) hsec
    have hmul := mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ) ≤ 25/16)
    convert hmul using 1
    norm_num only [logCurveBandGauge,parabolaBandGauge]
  have hg := mul_le_mul_of_nonneg_left (hgap.trans hGauge) hX₀.le
  have hd := (div_le_iff₀ hX₀).mp hδ
  nlinarith only [hg,hd,hξ,hη]

private def logarithmicPhysicalCoordinates (X : ℝ) (hX : X ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (X^2*p.1/4+p.2/8,-p.2/64)
  invFun p := ((4*p.1+32*p.2)/X^2,-64*p.2)
  left_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def logarithmicPhysicalWeight (X : ℝ) (p : ℝ × ℝ) : ℝ :=
  parabolaRapidKernel 1 0 p.1*parabolaRapidKernel X 0 p.2

theorem logarithmicPhysicalWeight_nonneg (X : ℝ) (p : ℝ × ℝ) :
    0 ≤ logarithmicPhysicalWeight X p :=
  mul_nonneg (parabolaRapidKernel_nonneg _ _ _) (parabolaRapidKernel_nonneg _ _ _)

theorem logarithmicPhysicalWeight_integrable {X : ℝ} (hX : 0 < X) :
    Integrable (logarithmicPhysicalWeight X) :=
  (integrable_parabolaRapidKernel (by norm_num : (0:ℝ) < 1) 0).mul_prod
    (integrable_parabolaRapidKernel hX 0)

private theorem logarithmicPhysicalWeight_fourier_zero {X u v : ℝ}
    (hX : 0 < X) (hgap : 1/100 ≤ |u| ∨ 1/(100*X) ≤ |v|) :
    (∫ p : ℝ × ℝ, (logarithmicPhysicalWeight X p : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2))=0 := by
  have hc : Continuous (fun p : ℝ × ℝ => fordAdditiveCharacter (u*p.1+v*p.2)) := by
    unfold fordAdditiveCharacter
    fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => (logarithmicPhysicalWeight X p : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2)) :=
    (logarithmicPhysicalWeight_integrable hX).ofReal.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => (sargos_character_norm _).le))
  have hprod := integral_prod _ hi
  rw [←Measure.volume_eq_prod] at hprod
  rw [hprod]
  have he (α t : ℝ) :
      (logarithmicPhysicalWeight X (α,t) : ℂ)*fordAdditiveCharacter (u*α+v*t) =
      ((parabolaRapidKernel 1 0 α : ℂ)*fordAdditiveCharacter (u*α))*
        ((parabolaRapidKernel X 0 t : ℂ)*fordAdditiveCharacter (v*t)) := by
    rw [fordAdditiveCharacter_add]
    dsimp only [logarithmicPhysicalWeight]
    push_cast
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const]
  rcases hgap with h | h
  · rw [integral_parabolaRapidKernel_character_zero (by norm_num : (0:ℝ) < 1)
      (by simpa only [mul_one] using h),zero_mul]
  · rw [integral_parabolaRapidKernel_character_zero hX h,mul_zero]

                                                                     
                                                                         
theorem logarithmicPhysicalWeight_band {X δ : ℝ} (hX : 1 ≤ X) (hδ : 4/X ≤ δ^2) :
    LogCurveWeightBand (1/4) δ
      (fun p : ℝ × ℝ => logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2)) := by
  have hX₀ : 0 < X := by linarith
  let e := logarithmicPhysicalCoordinates X hX₀.ne'
  refine ⟨fun p => logarithmicPhysicalWeight_nonneg _ _,
    logCurve_rescaling_integrable e.symm (logarithmicPhysicalWeight_integrable hX₀),?_⟩
  intro ξ η hgap
  obtain ⟨c,hc,hint⟩ := logCurve_rescaling_integral (F:=ℂ) e.symm
  let f := fun p : ℝ × ℝ => (logarithmicPhysicalWeight X p : ℂ)*
    fordAdditiveCharacter (ξ*(e p).1+η*(e p).2)
  have heq :
      (∫ p : ℝ × ℝ,
        (logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2) : ℂ)*
          fordAdditiveCharacter (ξ*p.1+η*p.2)) =
      ∫ p : ℝ × ℝ, f (e.symm p) := by
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    rfl
  rw [heq,hint f]
  have he (p : ℝ × ℝ) :
      ξ*(e p).1+η*(e p).2=(X^2*ξ/4)*p.1+(ξ/8-η/64)*p.2 := by
    dsimp [e,logarithmicPhysicalCoordinates]
    ring
  dsimp only [f]
  simp_rw [he]
  rw [logarithmicPhysicalWeight_fourier_zero hX₀
    (logarithmic_physical_band_gap hX hδ hgap),smul_zero]

theorem logarithmicPhysicalWeight_one_le {X : ℝ} (hX : 0 < X)
    {p : ℝ × ℝ} (hα : |p.1| ≤ 1) (ht : |p.2| ≤ X) :
    1 ≤ logarithmicPhysicalWeight X p := by
  exact one_le_mul_of_one_le_of_one_le
    (parabolaRapidKernel_one_le (by norm_num : (0:ℝ) < 1)
      (by simpa only [sub_zero] using hα))
    (parabolaRapidKernel_one_le hX (by simpa only [sub_zero] using ht))

                                                                          
                                                                           
theorem logarithmic_physical_sum_norm {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m x : ι → ℝ)
    {X : ℝ} (hX : 0 < X) (hm : ∀ i∈S, 0 < m i)
    (hx : ∀ i∈S, (m i)^2=X^2*(1+(1/4)*x i)) (α t : ℝ) :
    ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i)^2+t*Real.log (m i))‖ =
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i))
        (X^2*α/4+t/8) (-t/64)‖ := by
  have he (i : ι) (hi : i∈S) :
      α*(m i)^2+t*Real.log (m i) =
      (α*X^2+t*Real.log X)+
        (x i*(X^2*α/4+t/8)+logCurve (1/4) (x i)*(-t/64)) := by
    have h := logCurve_square_source_phase (κ:=1/4) hX (hm i hi) (hx i hi) α t
    convert h using 1
    ring
  have hsum :
      (∑ i∈S, z i*fordAdditiveCharacter (α*(m i)^2+t*Real.log (m i))) =
      fordAdditiveCharacter (α*X^2+t*Real.log X)*
        sargosPlanarSum S z x (fun i => logCurve (1/4) (x i))
          (X^2*α/4+t/8) (-t/64) := by
    unfold sargosPlanarSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi,fordAdditiveCharacter_add]
    ring
  rw [hsum,norm_mul,sargos_character_norm,one_mul]

def logarithmicPhysicalSixMoment {ι : Type*} (X : ℝ)
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, logarithmicPhysicalWeight X p*
    ‖∑ i∈S, z i*fordAdditiveCharacter (p.1*(m i)^2+p.2*Real.log (m i))‖^6

                                                                      
                                                   
theorem exists_logarithmicPhysicalSixMoment_transport {X : ℝ} (hX : 0 < X) :
    ∃ c > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m x : ι → ℝ),
      (∀ i∈S, 0 < m i) →
      (∀ i∈S, (m i)^2=X^2*(1+(1/4)*x i)) →
      logCurveWeightedBilinearMoment (1/4)
        (fun p : ℝ × ℝ => logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2))
        S S z z x x = c*logarithmicPhysicalSixMoment X S z m := by
  let e := logarithmicPhysicalCoordinates X hX.ne'
  obtain ⟨c,hc,hint⟩ := logCurve_rescaling_integral (F:=ℝ) e.symm
  refine ⟨c,hc,?_⟩
  intro ι S z m x hm hx
  let f := fun p : ℝ × ℝ => logarithmicPhysicalWeight X p*
    ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) (e p).1 (e p).2‖^6
  have heq :
      logCurveWeightedBilinearMoment (1/4)
        (fun p : ℝ × ℝ => logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2))
        S S z z x x = ∫ p : ℝ × ℝ, f (e.symm p) := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    change logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2)*
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) p.1 p.2‖^2*
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) p.1 p.2‖^4 =
      logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2)*
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) p.1 p.2‖^6
    ring
  rw [heq,hint f,smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [f,logarithmicPhysicalSixMoment]
  rw [logarithmic_physical_sum_norm S z m x hX hm hx]
  rfl

                                                                  
                                                                        
                                                                          
theorem exists_logarithmicPhysicalSixMoment_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (X : ℝ), 1 ≤ X →
      4/X ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (m x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ i∈S j, 0 < m j i) →
        (∀ j, ∀ i∈S j, (m j i)^2=X^2*(1+(1/4)*x j i)) →
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        logarithmicPhysicalSixMoment X (Finset.univ.sigma S)
          (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2) ≤
          C*(2:ℝ)^(ε*n)*((2:ℝ)^n)^2*
            ∑ j, logarithmicPhysicalSixMoment X (S j) (z j) (m j) := by
  obtain ⟨D,hD,hdec⟩ := exists_logCurveDecouplingBound_dyadic (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n X hX hwidth ι S z m x hm hx hgrid
  have hX₀ : 0 < X := by linarith
  let W := fun p : ℝ × ℝ => logarithmicPhysicalWeight X
    ((4*p.1+32*p.2)/X^2,-64*p.2)
  have hW : LogCurveWeightBand (1/4) (1/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using logarithmicPhysicalWeight_band hX hwidth
  obtain ⟨c,hc,htransport⟩ := exists_logarithmicPhysicalSixMoment_transport hX₀
  have hcell (j : Fin (2^n)) :
      (logCurveWeightedSixNorm (1/4) W (S j) (z j) (x j))^6 =
      c*logarithmicPhysicalSixMoment X (S j) (z j) (m j) := by
    rw [logCurveWeightedSixNorm_pow_six (1/4) W hW.1 hW.2.1]
    exact htransport ι (S j) (z j) (m j) (x j) (hm j) (hx j)
  have hwhole :
      (logCurveWeightedSixNorm (1/4) W (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2) (fun ji => x ji.1 ji.2))^6 =
      c*logarithmicPhysicalSixMoment X (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2) := by
    rw [logCurveWeightedSixNorm_pow_six (1/4) W hW.1 hW.2.1]
    exact htransport (Sigma fun _ : Fin (2^n) => ι) (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2) (fun ji => x ji.1 ji.2)
      (fun ji hji => hm ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
      (fun ji hji => hx ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
  have hnorm := (hdec n).2 (1/4) (by norm_num) ι W hW S z x hgrid
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6=D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hholder := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => (logCurveWeightedSixNorm (1/4) W (S j) (z j) (x j))^2)
    (fun _ _ => sq_nonneg _) 2
  norm_num only [show (2+1:ℕ)=3 by omega,←pow_mul,
    show (2*3:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat] at hholder
  simp_rw [hcell] at hholder
  rw [←Finset.mul_sum] at hholder
  have hmain := hcube.trans (mul_le_mul_of_nonneg_left hholder
    (show 0 ≤ D^6*(2:ℝ)^(ε*n) by positivity))
  rw [hwhole] at hmain
  apply (mul_le_mul_iff_right₀ hc).mp
  convert hmain using 1
  ring

                                                                       
                                                                          
theorem exists_logarithmicPhysicalWeight_le_lorentz :
    ∃ C > (0:ℝ), ∀ (X A : ℝ), 0 < X → X ≤ A → ∀ p : ℝ × ℝ,
      logarithmicPhysicalWeight X p ≤ C*(1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹ := by
  obtain ⟨D,hD,hdec⟩ := parabolaRapidKernel_decay 2
  have hkernel (R y : ℝ) :
      parabolaRapidKernel R 0 y ≤ D*(1+(y/R)^2)⁻¹ := by
    have h := hdec R 0 y
    simp only [sub_zero] at h
    have hs : 1+(y/R)^2 ≤ (1+|y/R|)^2 := by
      nlinarith [sq_abs (y/R),abs_nonneg (y/R)]
    have hp := (mul_le_mul_of_nonneg_right hs (parabolaRapidKernel_nonneg _ _ _)).trans h
    apply (le_div_iff₀ (by positivity : 0 < 1+(y/R)^2)).mpr
    simpa only [mul_comm] using hp
  refine ⟨D^2,by positivity,?_⟩
  intro X A hX hXA p
  have hA : 0 < A := hX.trans_le hXA
  have hα : parabolaRapidKernel 1 0 p.1 ≤ D*(1+p.1^2)⁻¹ := by
    simpa only [div_one] using hkernel 1 p.1
  have hratio : |p.2/A| ≤ |p.2/X| := by
    rw [abs_div,abs_div,abs_of_pos hA,abs_of_pos hX]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hX hXA
  have hs : (p.2/A)^2 ≤ (p.2/X)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hratio 2
  have ht : parabolaRapidKernel X 0 p.2 ≤ D*(1+(p.2/A)^2)⁻¹ :=
    (hkernel X p.2).trans (mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (by linarith : 1+(p.2/A)^2 ≤ 1+(p.2/X)^2)) hD.le)
  have hp := mul_le_mul hα ht (parabolaRapidKernel_nonneg _ _ _) (by positivity)
  exact hp.trans_eq (by ring)

                                                                    
                                                                        
                                     
theorem exists_logarithmicPhysicalSixMoment_short_cell {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (X A δ B : ℝ) (L : ℤ),
        0 < X → X ≤ A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨D,hD,hweight⟩ := exists_logarithmicPhysicalWeight_le_lorentz
  obtain ⟨C,hC,hcell⟩ := exists_logarithmic_short_cell_product_weight hε
  refine ⟨D*C,by positivity,?_⟩
  intro Q hQ ι S z s m X A δ B L hX hXA hδ hB hscale hcubic hs hm hinterval hz
  have hA : 0 < A := hX.trans_le hXA
  let P := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6
  have hPc : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hP₀ (p : ℝ × ℝ) : 0 ≤ P p := by dsimp [P]; positivity
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (hP₀ p)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hiL : Integrable (fun p : ℝ × ℝ => (1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹*P p) :=
    (integrable_inv_one_add_sq.mul_prod
      (integrable_inv_one_add_sq.comp_div hA.ne')).mul_bdd hPc.aestronglyMeasurable
        (Filter.Eventually.of_forall hPb)
  have hiR : Integrable (fun p : ℝ × ℝ => logarithmicPhysicalWeight X p*P p) :=
    (logarithmicPhysicalWeight_integrable hX).mul_bdd hPc.aestronglyMeasurable
      (Filter.Eventually.of_forall hPb)
  have hmain : logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤
      ∫ p : ℝ × ℝ, D*((1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹*P p) := by
    apply integral_mono hiR (hiL.const_mul D)
    intro p
    exact (mul_le_mul_of_nonneg_right (hweight X A hX hXA p) (hP₀ p)).trans_eq (by ring)
  rw [integral_const_mul] at hmain
  have hprod := integral_prod_symm _ hiL
  rw [←Measure.volume_eq_prod] at hprod
  have hinter : (∫ p : ℝ × ℝ, (1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹*P p) =
      ∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ, (1+α^2)⁻¹*P (α,t)) := by
    rw [hprod]
    apply integral_congr_ae
    filter_upwards with t
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with α
    ring
  rw [hinter] at hmain
  have hsource := hcell Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  exact hmain.trans ((mul_le_mul_of_nonneg_left hsource hD.le).trans_eq (by ring))

private theorem logarithmic_grid_center {X K j : ℝ}
    (hX : 0 < X) (hK : 0 < K) (hj : 0 ≤ j) (hjK : j ≤ K) :
    let A := Real.sqrt (X^2*(1+j/(4*K)))
    X ≤ A ∧ A ≤ 2*X ∧ A^2=X^2*(1+j/(4*K)) := by
  dsimp
  have hu : 0 ≤ j/(4*K) := by positivity
  have hu₁ : j/(4*K) ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*K)).mpr
    linarith
  have hsq := Real.sq_sqrt (show 0 ≤ X^2*(1+j/(4*K)) by positivity)
  have h₀ := Real.sqrt_nonneg (X^2*(1+j/(4*K)))
  have hl := mul_nonneg (sq_nonneg X) hu
  have hh := mul_le_mul_of_nonneg_left hu₁ (sq_nonneg X)
  exact ⟨by nlinarith,by nlinarith,hsq⟩

private theorem logarithmic_grid_radius {X K A : ℝ}
    (hX : 0 < X) (hK : 1 ≤ K) (hXA : X ≤ A) (hscale : X ≤ 16*K^2) :
    let δ := X/(8*K)
    0 < δ ∧ |δ/A| ≤ 1/4 ∧ |δ^3/A^2| ≤ 1 := by
  dsimp
  have hK₀ : 0 < K := by linarith
  have hA : 0 < A := hX.trans_le hXA
  have hδ : 0 < X/(8*K) := by positivity
  have hδle : X/(8*K) ≤ X/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*K)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hK hX.le]
  refine ⟨hδ,?_,?_⟩
  · rw [abs_of_pos (div_pos hδ hA)]
    apply (div_le_iff₀ hA).mpr
    linarith
  · rw [abs_of_pos (by positivity : 0 < (X/(8*K))^3/A^2)]
    have hden : X^2 ≤ A^2 := by nlinarith
    have hcmp := div_le_div_of_nonneg_left (show 0 ≤ (X/(8*K))^3 by positivity)
      (sq_pos_of_pos hX) hden
    have he : (X/(8*K))^3/X^2=X/(512*K^3) := by field_simp; ring
    rw [he] at hcmp
    apply hcmp.trans
    apply (div_le_iff₀ (by positivity : 0 < 512*K^3)).mpr
    have hpow : K^2 ≤ K^3 := by nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
    nlinarith [sq_nonneg K]

private theorem logarithmic_grid_cell_range {X K j A m x : ℝ}
    (hX : 0 < X) (hK : 0 < K) (hXA : X ≤ A)
    (hA : A^2=X^2*(1+j/(4*K))) (hm : 0 < m)
    (hmx : m^2=X^2*(1+x/4)) (hx : x∈Icc (j/K) ((j+1)/K)) :
    A ≤ m ∧ m ≤ A+X/(8*K) := by
  have hxlo := (div_le_iff₀ hK).mp hx.1
  have hxhi := (le_div_iff₀ hK).mp hx.2
  have hdiff : m^2-A^2=X^2*(x-j/K)/4 := by
    rw [hmx,hA]
    field_simp
    ring
  have hlo : 0 ≤ m^2-A^2 := by
    rw [hdiff]
    exact div_nonneg (mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hx.1)) (by norm_num)
  have hAm : A ≤ m := by nlinarith
  have hgap : m^2-A^2 ≤ X^2/(4*K) := by
    rw [hdiff]
    have h := mul_le_mul_of_nonneg_left
      (show x-j/K ≤ 1/K by apply (le_div_iff₀ hK).mpr; field_simp at hxlo ⊢; nlinarith)
      (sq_nonneg X)
    have hh := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 4)
    convert hh using 1
    field_simp
  have hfac := mul_nonneg (sub_nonneg.mpr hAm)
    (show 0 ≤ m+A-2*X by linarith)
  have he : 2*X*(X/(8*K))=X^2/(4*K) := by ring
  have hh : 2*X*(m-A) ≤ 2*X*(X/(8*K)) := by nlinarith
  have hbound := (mul_le_mul_iff_right₀ (show 0 < 2*X by positivity)).mp hh
  exact ⟨hAm,by linarith⟩

private theorem logarithmic_grid_integer_interval {X K A : ℝ}
    (hK : 1 ≤ K) (hscale : 4*K^2 ≤ X) :
    let Q := Nat.ceil (X/(8*K))+2
    let L := Int.floor A-1
    1 ≤ Q ∧ (Q:ℝ) ≤ X/K ∧
      ∀ m : ℤ, A ≤ (m:ℝ) → (m:ℝ) ≤ A+X/(8*K) → L < m ∧ m ≤ L+Q := by
  dsimp
  have hK₀ : 0 < K := by linarith
  have hX : 0 < X := by nlinarith
  have hδ : 0 ≤ X/(8*K) := by positivity
  have hceil := Nat.ceil_lt_add_one hδ
  have hfloor := Int.floor_le A
  have hfloor' := Int.lt_floor_add_one A
  have hceil' := Nat.le_ceil (X/(8*K))
  refine ⟨by omega,?_,?_⟩
  · push_cast
    have hratio : 4 ≤ X/K := by
      apply (le_div_iff₀ hK₀).mpr
      nlinarith
    have he : X/(8*K)=(X/K)/8 := by ring
    rw [he] at hceil ⊢
    linarith
  · intro m hmlo hmhi
    constructor
    · have hh : ((Int.floor A-1:ℤ):ℝ) < m := by push_cast; linarith
      exact_mod_cast hh
    · have hh : (m:ℝ) ≤ ((Int.floor A-1:ℤ):ℝ)+(Nat.ceil (X/(8*K))+2:ℕ) := by
        push_cast
        linarith
      exact_mod_cast hh

                                                                
                                                                  
                                                                 
theorem exists_logarithmicPhysicalSixMoment_grid_cell {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X K j : ℝ), 1 ≤ K → 4*K^2 ≤ X → X ≤ 16*K^2 →
      0 ≤ j → j ≤ K → ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ)
        (m : ι → ℤ) (x : ι → ℝ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2=X^2*(1+(1/4)*x i)) →
        (∀ i∈S, x i∈Icc (j/K) ((j+1)/K)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤
          C*X*B^6*(X/K)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,hcell⟩ := exists_logarithmicPhysicalSixMoment_short_cell hε
  refine ⟨2*C,by positivity,?_⟩
  intro X K j hK hl hu hj hjK ι S z m x B hB hm hx hgrid hz
  have hK₀ : 0 < K := by linarith
  have hX : 0 < X := by nlinarith
  let A := Real.sqrt (X^2*(1+j/(4*K)))
  let δ := X/(8*K)
  let Q := Nat.ceil δ+2
  let L := Int.floor A-1
  obtain ⟨hXA,hAX,hAsq⟩ := logarithmic_grid_center hX hK₀ hj hjK
  change X ≤ A at hXA
  change A ≤ 2*X at hAX
  obtain ⟨hδ,hδA,hcubic⟩ := logarithmic_grid_radius hX hK hXA hu
  change 0 < δ at hδ
  obtain ⟨hQ,hQbound,hinterval⟩ := logarithmic_grid_integer_interval (A:=A) hK hl
  change 1 ≤ Q at hQ
  change (Q:ℝ) ≤ X/K at hQbound
  have hrange (i : ι) (hi : i∈S) : A ≤ (m i:ℝ) ∧ (m i:ℝ) ≤ A+δ := by
    exact logarithmic_grid_cell_range hX hK₀ hXA hAsq (hm i hi)
      (by convert hx i hi using 1; ring) (hgrid i hi)
  have hs (i : ι) (hi : i∈S) : ((m i:ℝ)-A)/δ∈Icc (-1:ℝ) 1 := by
    have hh := hrange i hi
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith
    · apply (div_le_iff₀ hδ).mpr
      linarith
  have hmul (i : ι) (_hi : i∈S) : δ*(((m i:ℝ)-A)/δ)=(m i:ℝ)-A := by
    field_simp
  have hI (i : ι) (hi : i∈S) : L < m i ∧ m i ≤ L+Q :=
    hinterval (m i) (hrange i hi).1 (hrange i hi).2
  have hh := hcell Q hQ ι S z (fun i => ((m i:ℝ)-A)/δ) m X A δ B L
    hX hXA hδ.ne' hB hδA hcubic hs hmul hI hz
  have hp : (Q:ℝ)^((3:ℝ)+ε) ≤ (X/K)^((3:ℝ)+ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hQbound (by positivity)
  calc
    _ ≤ C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := hh
    _ ≤ C*(2*X)*B^6*(X/K)^((3:ℝ)+ε) := by gcongr
    _ = _ := by ring

private theorem logarithmic_grid_scale_identity {X : ℝ} (hX : 0 < X)
    (n : ℕ) (ε : ℝ) :
    (2:ℝ)^(ε*n)*((2:ℝ)^n)^3*X*(X/(2:ℝ)^n)^((3:ℝ)+ε) = X^((4:ℝ)+ε) := by
  have hK : 0 < (2:ℝ)^n := by positivity
  have he : (2:ℝ)^(ε*n)=((2:ℝ)^n)^ε := by
    rw [mul_comm,Real.rpow_natCast_mul (by norm_num)]
  rw [he]
  generalize (2:ℝ)^n = K at hK ⊢
  rw [Real.div_rpow hX.le hK.le,Real.rpow_add hX,
    Real.rpow_add hK,Real.rpow_add hX]
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
  have hr : K^ε ≠ 0 := (Real.rpow_pos_of_pos hK ε).ne'
  field_simp

                                                                     
                                                                          
                                                   
theorem exists_logarithmicPhysicalSixMoment_grid {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (X : ℝ),
      4*((2:ℝ)^n)^2 ≤ X → X ≤ 16*((2:ℝ)^n)^2 →
      ∀ (ι : Type) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (m : Fin (2^n) → ι → ℤ)
        (x : Fin (2^n) → ι → ℝ) (B : ℝ), 0 ≤ B →
        (∀ j, ∀ i∈S j, 0 < (m j i:ℝ)) →
        (∀ j, ∀ i∈S j, (m j i:ℝ)^2=X^2*(1+(1/4)*x j i)) →
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ k : ℤ, (∑ i∈(S j).filter (fun i => m j i=k), ‖z j i‖) ≤ B) →
        logarithmicPhysicalSixMoment X (Finset.univ.sigma S)
          (fun ji => z ji.1 ji.2) (fun ji => (m ji.1 ji.2:ℝ)) ≤
          C*B^6*X^((4:ℝ)+ε) := by
  obtain ⟨D,hD,hdec⟩ := exists_logarithmicPhysicalSixMoment_dyadic hε
  obtain ⟨C,hC,hcell⟩ := exists_logarithmicPhysicalSixMoment_grid_cell hε
  refine ⟨D*C,by positivity,?_⟩
  intro n X hl hu ι S z m x B hB hm hx hgrid hz
  have hK : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hX : 1 ≤ X := by nlinarith
  have hX₀ : 0 < X := by linarith
  have hwidth : 4/X ≤ (1/(2:ℝ)^n)^2 := by
    rw [div_pow,one_pow]
    apply (div_le_div_iff₀ hX₀ (by positivity)).mpr
    simpa only [one_mul] using hl
  have hmain := hdec n X hX hwidth ι S z (fun j i => (m j i:ℝ)) x hm hx hgrid
  have hcells (j : Fin (2^n)) :
      logarithmicPhysicalSixMoment X (S j) (z j) (fun i => (m j i:ℝ)) ≤
        C*X*B^6*(X/(2:ℝ)^n)^((3:ℝ)+ε) := by
    apply hcell X ((2:ℝ)^n) (j:ℕ) hK hl hu (Nat.cast_nonneg _) ?_
      ι (S j) (z j) (m j) (x j) B hB (hm j) (hx j) ?_ (hz j)
    · exact_mod_cast j.isLt.le
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgrid j
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hcells j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat] at hsum
  have hh := hmain.trans (mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ D*(2:ℝ)^(ε*n)*((2:ℝ)^n)^2 by positivity))
  have he : D*(2:ℝ)^(ε*n)*((2:ℝ)^n)^2*
      ((2:ℝ)^n*(C*X*B^6*(X/(2:ℝ)^n)^((3:ℝ)+ε))) =
      (D*C)*B^6*X^((4:ℝ)+ε) := by
    calc
      _ = (D*C)*B^6*((2:ℝ)^(ε*n)*((2:ℝ)^n)^3*X*
        (X/(2:ℝ)^n)^((3:ℝ)+ε)) := by ring
      _ = _ := by rw [logarithmic_grid_scale_identity hX₀]
  exact hh.trans_eq he


private def logarithmicClosedGridCell (n : ℕ) (x : ℝ) : Fin (2^n) :=
  ⟨min ⌊((2^n:ℕ):ℝ)*x⌋₊ (2^n-1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩

private theorem logarithmicClosedGridCell_mem (n : ℕ) {x : ℝ}
    (hx : x∈Icc (0:ℝ) 1) :
    x∈Icc (((logarithmicClosedGridCell n x:ℕ):ℝ)/((2^n:ℕ):ℝ))
      ((((logarithmicClosedGridCell n x:ℕ):ℝ)+1)/((2^n:ℕ):ℝ)) := by
  let M := 2^n
  have hM : 0<M := by dsimp [M]; positivity
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hlo := Nat.floor_le (mul_nonneg hMr.le hx.1)
  have hmin : ((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)≤⌊(M:ℝ)*x⌋₊ := by
    exact_mod_cast min_le_left ⌊(M:ℝ)*x⌋₊ (M-1)
  change x∈Icc (((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)/M)
    ((((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)+1)/M)
  constructor
  · apply (div_le_iff₀ hMr).mpr
    nlinarith [hmin.trans hlo]
  · apply (le_div_iff₀ hMr).mpr
    by_cases hc : ⌊(M:ℝ)*x⌋₊≤M-1
    · rw [min_eq_left hc]
      have hh := Nat.lt_floor_add_one ((M:ℝ)*x)
      linarith
    · rw [min_eq_right (le_of_not_ge hc)]
      have hm : M-1+1=M := Nat.sub_add_cancel hM
      have hm' : ((M-1:ℕ):ℝ)+1=M := by exact_mod_cast hm
      rw [hm']
      nlinarith [hx.2]

                                                                   
                                                                        
                                                                              
theorem exists_logarithmicPhysicalSixMoment_block {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X : ℝ), 4 ≤ X →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2∈Icc (X^2) (5*X^2/4)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤ C*B^6*X^((4:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,hgrid⟩ := exists_logarithmicPhysicalSixMoment_grid hε
  refine ⟨C,hC,?_⟩
  intro X hX ι S z m B hB hm hblock hz
  have hX₀ : 0 < X := by linarith
  obtain ⟨n,hnlo,hnhi⟩ := exists_nat_pow_near (show (1:ℝ) ≤ X/4 by linarith)
    (by norm_num : (1:ℝ) < 4)
  have hpow : (4:ℝ)^n=((2:ℝ)^n)^2 := by
    rw [←pow_mul,pow_mul']
    norm_num
  have hl : 4*((2:ℝ)^n)^2 ≤ X := by rw [hpow] at hnlo; linarith
  have hu : X ≤ 16*((2:ℝ)^n)^2 := by rw [pow_succ,hpow] at hnhi; linarith
  let x := fun i => 4*((m i:ℝ)^2/X^2-1)
  let g := fun i => logarithmicClosedGridCell n (x i)
  let U := fun j => S.filter (fun i => g i=j)
  have hx (i : ι) (hi : i∈S) : x i∈Icc (0:ℝ) 1 := by
    have hh := hblock i hi
    have hlo : 1 ≤ (m i:ℝ)^2/X^2 := (le_div_iff₀ (sq_pos_of_pos hX₀)).mpr (by simpa using hh.1)
    have hhi : (m i:ℝ)^2/X^2 ≤ 5/4 :=
      (div_le_iff₀ (sq_pos_of_pos hX₀)).mpr (by linarith only [hh.2])
    dsimp only [x]
    constructor <;> linarith
  have hsq (i : ι) (_hi : i∈S) : (m i:ℝ)^2=X^2*(1+(1/4)*x i) := by
    dsimp only [x]
    field_simp
    ring
  have hcell (j : Fin (2^n)) (i : ι) (hi : i∈U j) :
      x i∈Icc ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    obtain ⟨hi,hgi⟩ := Finset.mem_filter.mp hi
    have hh := logarithmicClosedGridCell_mem n (hx i hi)
    change x i∈Icc ((g i:ℕ)/((2^n:ℕ):ℝ)) (((g i:ℕ)+1)/((2^n:ℕ):ℝ)) at hh
    rwa [hgi] at hh
  have hfiber (j : Fin (2^n)) (k : ℤ) :
      (∑ i∈(U j).filter (fun i => m i=k), ‖z i‖) ≤ B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)) (hz k)
    intro i hi
    obtain ⟨hi,hmk⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hmk⟩
  have hh := hgrid n X hl hu ι U (fun _ => z) (fun _ => m) (fun _ => x) B hB
    (fun _ i hi => hm i (Finset.mem_filter.mp hi).1)
    (fun _ i hi => hsq i (Finset.mem_filter.mp hi).1) hcell hfiber
  have heq : logarithmicPhysicalSixMoment X (Finset.univ.sigma U)
      (fun ji => z ji.2) (fun ji => (m ji.2:ℝ)) =
      logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) := by
    unfold logarithmicPhysicalSixMoment
    apply integral_congr_ae
    filter_upwards with p
    congr 2
    rw [Finset.sum_sigma]
    apply congrArg norm
    exact Finset.sum_fiberwise_of_maps_to (fun i (_hi : i∈S) => Finset.mem_univ (g i))
      (fun i => z i*fordAdditiveCharacter (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ)))
  rwa [heq] at hh

theorem logarithmicPhysical_box_le {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℝ) {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ in Icc (-X) X, ∫ α : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i)^2+t*Real.log (m i))‖^6) ≤
      logarithmicPhysicalSixMoment X S z m := by
  let P := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i)^2+p.2*Real.log (m i))‖^6
  let B := Icc (0:ℝ) 1 ×ˢ Icc (-X) X
  have hPc : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hP₀ (p : ℝ × ℝ) : 0 ≤ P p := by dsimp [P]; positivity
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (hP₀ p)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (p.1*(m i)^2+p.2*Real.log (m i))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hiP : IntegrableOn P B :=
    hPc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hiW : Integrable (fun p : ℝ × ℝ => logarithmicPhysicalWeight X p*P p) :=
    (logarithmicPhysicalWeight_integrable hX).mul_bdd hPc.aestronglyMeasurable
      (Filter.Eventually.of_forall hPb)
  have hpoint (p : ℝ × ℝ) (hp : p∈B) : P p ≤ logarithmicPhysicalWeight X p*P p := by
    have hα : |p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.1],hp.1.2⟩
    have ht : |p.2| ≤ X := abs_le.mpr hp.2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (logarithmicPhysicalWeight_one_le hX hα ht) (hP₀ p)
  have hlocal := setIntegral_mono_on hiP hiW.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  have hwhole := setIntegral_le_integral (s:=B) hiW
    (Filter.Eventually.of_forall (fun p => mul_nonneg
      (logarithmicPhysicalWeight_nonneg X p) (hP₀ p)))
  have hiProd : Integrable P
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (-X) X))) := by
    rwa [Measure.prod_restrict,←Measure.volume_eq_prod]
  have hprod := integral_prod_symm P hiProd
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hprod
  change (∫ p in B, P p)=_ at hprod
  rw [hprod] at hlocal
  exact hlocal.trans hwhole

                                                                   
                                                              
theorem exists_logarithmic_block_sixth_translated {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X : ℝ), 4 ≤ X →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B t₀ : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2∈Icc (X^2) (5*X^2/4)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-X) X, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ))‖^6) ≤ C*B^6*X^((4:ℝ)+ε) := by
  obtain ⟨C,hC,hblock⟩ := exists_logarithmicPhysicalSixMoment_block hε
  refine ⟨C,hC,?_⟩
  intro X hX ι S z m B t₀ hB hm hrange hz
  let c := fun i => z i*fordAdditiveCharacter (t₀*Real.log (m i:ℝ))
  have hcn (i : ι) : ‖c i‖=‖z i‖ := by
    simp only [c,norm_mul,sargos_character_norm,mul_one]
  have hcz (k : ℤ) : (∑ i∈S.filter (fun i => m i=k), ‖c i‖) ≤ B := by
    simpa only [hcn] using hz k
  have hmain := (logarithmicPhysical_box_le S c (fun i => (m i:ℝ))
    (by linarith : 0 < X)).trans (hblock X hX ι S c m B hB hm hrange hcz)
  have he (α t : ℝ) :
      (∑ i∈S, c i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))) =
      ∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [c]
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  simpa only [he] using hmain

private theorem logSix_long_window {A T M : ℝ} (hA : 0 < A) (hT : 0 ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    (hwindow : ∀ x, (∫ t : ℝ in Icc (-A) A, f (t+x)) ≤ M) :
    (∫ t : ℝ in Icc (-T) T, f t) ≤ (T/A+1)*M := by
  let q := Nat.ceil (T/A)
  let a := fun k : ℕ => -T+2*A*k
  have hM : 0 ≤ M := (integral_nonneg (fun t => hf₀ (t+0))).trans (hwindow 0)
  have hceil : T/A ≤ (q:ℝ) := Nat.le_ceil _
  have hTq : T ≤ A*q := (div_le_iff₀ hA).mp hceil |>.trans_eq (by ring)
  have hcover : Icc (-T) T ⊆ Icc (a 0) (a q) := by
    intro t ht
    dsimp only [a]
    norm_num only [Nat.cast_zero,mul_zero,add_zero]
    exact ⟨ht.1,by linarith [ht.2]⟩
  have hmono := setIntegral_mono_set
    (hf.continuousOn.integrableOn_compact (μ:=volume) (K:=Icc (a 0) (a q)) isCompact_Icc)
    (Filter.Eventually.of_forall hf₀) (Filter.Eventually.of_forall hcover)
  have hcell (k : ℕ) : (∫ t : ℝ in a k..a (k+1), f t) ≤ M := by
    let c := -T+2*A*k+A
    have hh := hwindow c
    rw [integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by linarith : -A ≤ A),
      intervalIntegral.integral_comp_add_right] at hh
    have ha : -A+c=a k := by dsimp [a,c]; ring
    have hb : A+c=a (k+1) := by dsimp [a,c]; push_cast; ring
    rwa [ha,hb] at hh
  have hsum := Finset.sum_le_sum (fun k (_hk : k∈Finset.range q) => hcell k)
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hf.intervalIntegrable (a k) (a (k+1)))] at hsum
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have ha : a 0 ≤ a q := by
    dsimp only [a]
    norm_num only [Nat.cast_zero,mul_zero,add_zero]
    linarith [mul_nonneg (show 0 ≤ 2*A by positivity) (Nat.cast_nonneg q)]
  rw [intervalIntegral.integral_of_le ha,←integral_Icc_eq_integral_Ioc] at hsum
  have hq : (q:ℝ) ≤ T/A+1 := (Nat.ceil_lt_add_one (div_nonneg hT hA.le)).le
  exact (hmono.trans hsum).trans (mul_le_mul_of_nonneg_right hq hM)

                                                                       
                                                                      
                                                        
theorem exists_logarithmic_block_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X T : ℝ), 4 ≤ X → 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2∈Icc (X^2) (5*X^2/4)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6) ≤ C*B^6*(T+X)*X^((3:ℝ)+ε) := by
  obtain ⟨C,hC,hblock⟩ := exists_logarithmic_block_sixth_translated hε
  refine ⟨C,hC,?_⟩
  intro X T hX hT ι S z m B hB hm hrange hz
  have hX₀ : 0 < X := by linarith
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  let f := fun t => ∫ α : ℝ in Icc (0:ℝ) 1, P t α
  have hPc : Continuous (Function.uncurry P) := by
    unfold P Function.uncurry fordAdditiveCharacter
    fun_prop
  have hfc : Continuous f := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ:=volume) (f:=P) hPc 0 1
    simpa only [f,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hh
  have hwindow (x : ℝ) : (∫ t : ℝ in Icc (-X) X, f (t+x)) ≤ C*B^6*X^((4:ℝ)+ε) :=
    hblock X hX ι S z m B x hB hm hrange hz
  have hh := logSix_long_window hX₀ hT f hfc
    (fun t => integral_nonneg (fun α => by dsimp [P]; positivity)) hwindow
  have he : (T/X+1)*(C*B^6*X^((4:ℝ)+ε))=C*B^6*(T+X)*X^((3:ℝ)+ε) := by
    rw [show (4:ℝ)+ε=((3:ℝ)+ε)+1 by ring,Real.rpow_add_one hX₀.ne']
    field_simp
  exact hh.trans_eq he

def logarithmicSixMoment {ι : Type*} (T : ℝ)
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) : ℝ :=
  ∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6

private theorem logarithmicSixMoment_eq_prod {ι : Type*} (T : ℝ)
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    logarithmicSixMoment T S z m =
      ∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T,
        ‖∑ i∈S, z i*fordAdditiveCharacter (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6 := by
  let P := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6
  have hP : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hi := hP.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (-T) T))
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  have hh := integral_prod_symm P hi
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hh
  exact hh.symm

private theorem logarithmicSixMoment_fiberwise {ι : Type*} {K : ℕ}
    (T : ℝ) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (g : ι → Fin K) :
    logarithmicSixMoment T S z m ≤
      (K:ℝ)^5*∑ j, logarithmicSixMoment T (S.filter (fun i => g i=j)) z m := by
  classical
  let R := Icc (0:ℝ) 1 ×ˢ Icc (-T) T
  let A := fun (j : Fin K) (p : ℝ × ℝ) => ∑ i∈S.filter (fun i => g i=j),
    z i*fordAdditiveCharacter (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))
  let F := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6
  have hAc (j : Fin K) : Continuous (fun p => ‖A j p‖^6) := by
    unfold A fordAdditiveCharacter
    fun_prop
  have hFc : Continuous F := by unfold F fordAdditiveCharacter; fun_prop
  have hiA (j : Fin K) : IntegrableOn (fun p => ‖A j p‖^6) R :=
    (hAc j).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hiSum : IntegrableOn (fun p => (K:ℝ)^5*∑ j, ‖A j p‖^6) R :=
    (integrable_finsetSum _ (fun j _ => hiA j)).const_mul _
  have hpoint (p : ℝ × ℝ) : F p ≤ (K:ℝ)^5*∑ j, ‖A j p‖^6 := by
    have he : (∑ j, A j p)=∑ i∈S, z i*fordAdditiveCharacter
        (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ)) :=
      Finset.sum_fiberwise_of_maps_to (fun i (_hi : i∈S) => Finset.mem_univ (g i)) _
    have hn := pow_le_pow_left₀ (norm_nonneg (∑ j, A j p))
      (norm_sum_le Finset.univ (fun j => A j p)) 6
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
      (f:=fun j => ‖A j p‖) (fun _ _ => norm_nonneg _) 5
    simp only [show (5+1:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin] at hh
    simpa only [he,F] using hn.trans hh
  have hmain := setIntegral_mono_on
    (hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    hiSum (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => hpoint p)
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hiA j)] at hmain
  simp only [logarithmicSixMoment_eq_prod]
  exact hmain

                                                                       
                                                   
theorem exists_logarithmic_dyadic_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X T : ℝ), 4 ≤ X → 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, (m i:ℝ)∈Icc X (2*X)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicSixMoment T S z m ≤ C*B^6*(T+X)*X^((3:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,hblock⟩ := exists_logarithmic_block_sixth hε
  refine ⟨16^6*C*(2:ℝ)^((4:ℝ)+ε),by positivity,?_⟩
  intro X T hX hT ι S z m B hB hm hz
  have hX₀ : 0 < X := by linarith
  let x := fun i => (m i:ℝ)/X-1
  let g := fun i => logarithmicClosedGridCell 4 (x i)
  let U := fun j => S.filter (fun i => g i=j)
  let A := fun j : Fin (2^4) => X*(1+(j:ℕ)/16)
  have hA (j : Fin (2^4)) : X ≤ A j ∧ A j ≤ 2*X := by
    have hj : (0:ℝ) ≤ (j:ℕ) := Nat.cast_nonneg _
    have hj' : ((j:ℕ):ℝ) ≤ 16 := by exact_mod_cast (show (j:ℕ) ≤ 16 by omega)
    have hlo := mul_nonneg hX₀.le hj
    have hhi := mul_le_mul_of_nonneg_left hj' hX₀.le
    dsimp only [A]
    constructor <;> nlinarith
  have hx (i : ι) (hi : i∈S) : x i∈Icc (0:ℝ) 1 := by
    have hh := hm i hi
    have hlo : 1 ≤ (m i:ℝ)/X := (le_div_iff₀ hX₀).mpr (by simpa only [one_mul] using hh.1)
    have hhi : (m i:ℝ)/X ≤ 2 := (div_le_iff₀ hX₀).mpr hh.2
    dsimp only [x]
    constructor <;> linarith
  have hxeq (i : ι) : (m i:ℝ)=X*(1+x i) := by dsimp [x]; field_simp; ring
  have hrange (j : Fin (2^4)) (i : ι) (hi : i∈U j) :
      A j ≤ (m i:ℝ) ∧ (m i:ℝ) ≤ (17/16)*A j := by
    obtain ⟨hi,hgi⟩ := Finset.mem_filter.mp hi
    have hh := logarithmicClosedGridCell_mem 4 (hx i hi)
    change x i∈Icc ((g i:ℕ)/((2^4:ℕ):ℝ)) (((g i:ℕ)+1)/((2^4:ℕ):ℝ)) at hh
    rw [hgi] at hh
    norm_num only [Nat.reducePow,Nat.cast_ofNat] at hh
    have hlo := mul_le_mul_of_nonneg_left hh.1 hX₀.le
    have hhi := mul_le_mul_of_nonneg_left hh.2 hX₀.le
    have hcenter := (hA j).1
    rw [hxeq i]
    dsimp only [A] at hcenter ⊢
    constructor <;> nlinarith
  have hfiber (j : Fin (2^4)) (k : ℤ) :
      (∑ i∈(U j).filter (fun i => m i=k), ‖z i‖) ≤ B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)) (hz k)
    intro i hi
    obtain ⟨hi,hk⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hk⟩
  have hcell (j : Fin (2^4)) : logarithmicSixMoment T (U j) z m ≤
      C*(2:ℝ)^((4:ℝ)+ε)*B^6*(T+X)*X^((3:ℝ)+ε) := by
    have hAj : 4 ≤ A j := hX.trans (hA j).1
    have hmj (i : ι) (hi : i∈U j) : 0 < (m i:ℝ) := by
      have hh := (hrange j i hi).1
      linarith
    have hsq (i : ι) (hi : i∈U j) :
        (m i:ℝ)^2∈Icc ((A j)^2) (5*(A j)^2/4) := by
      have hh := hrange j i hi
      have hpos := hmj i hi
      constructor
      · nlinarith
      · have hprod := mul_nonneg (sub_nonneg.mpr hh.2)
          (show 0 ≤ (17/16)*A j+(m i:ℝ) by positivity)
        nlinarith [sq_nonneg (A j)]
    have hh := hblock (A j) T hAj hT ι (U j) z m B hB hmj hsq (hfiber j)
    have hmono : C*B^6*(T+A j)*(A j)^((3:ℝ)+ε) ≤
        C*B^6*(2*(T+X))*(2*X)^((3:ℝ)+ε) := by gcongr <;> linarith [(hA j).2]
    apply hh.trans (hmono.trans_eq ?_)
    rw [Real.mul_rpow (by norm_num) hX₀.le,
      show (4:ℝ)+ε=((3:ℝ)+ε)+1 by ring,Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0)]
    ring
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hcell j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hh := (logarithmicSixMoment_fiberwise T S z m g).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

private theorem logarithmicSixMoment_small {ι : Type*} {T B : ℝ}
    (hT : 0 ≤ T) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ)
    (hm : ∀ i∈S, 1 ≤ m i ∧ m i ≤ 4)
    (hz : ∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) :
    logarithmicSixMoment T S z m ≤ 2*T*(4*B)^6 := by
  classical
  have hmass : (∑ i∈S, ‖z i‖) ≤ 4*B := by
    have he := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_Icc.mpr (hm i hi)) (fun i => ‖z i‖)
    rw [←he]
    apply (Finset.sum_le_sum (fun k (_hk : k∈Finset.Icc (1:ℤ) 4) => hz k)).trans_eq
    norm_num [show Int.toNat (4:ℤ)=4 by decide]
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  have hP₀ (t α : ℝ) : 0 ≤ P t α := by dsimp [P]; positivity
  have hb (t α : ℝ) : ‖P t α‖ ≤ (4*B)^6 := by
    rw [Real.norm_of_nonneg (hP₀ t α)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hh := norm_sum_le S (fun i => z i*fordAdditiveCharacter
      (α*(m i:ℝ)^2+t*Real.log (m i:ℝ)))
    simp only [norm_mul,sargos_character_norm,mul_one] at hh
    exact hh.trans hmass
  have hinner (t : ℝ) : (∫ α : ℝ in Icc (0:ℝ) 1, P t α) ≤ (4*B)^6 := by
    have hh := norm_setIntegral_le_of_norm_le_const_ae
      (μ:=volume) (s:=Icc (0:ℝ) 1) (f:=P t) isCompact_Icc.measure_lt_top
      (Filter.Eventually.of_forall (hb t))
    rw [Real.norm_of_nonneg (integral_nonneg (hP₀ t))] at hh
    simpa only [Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1),sub_zero,mul_one] using hh
  have hmain : (∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1, P t α) ≤
      ∫ _t : ℝ in Icc (-T) T, (4*B)^6 := by
    have hc : IntegrableOn (fun _t : ℝ => (4*B)^6) (Icc (-T) T) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => integral_nonneg (hP₀ t))) hc
    exact Filter.Eventually.of_forall hinner
  have he : (∫ _t : ℝ in Icc (-T) T, (4*B)^6)=2*T*(4*B)^6 := by
    rw [setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (by linarith : -T ≤ T)]
    ring
  exact hmain.trans_eq he

                                                                      
                                                                         
theorem exists_logarithmic_sixth_log_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 1 ≤ m i ∧ m i ≤ N) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicSixMoment T S z m ≤
          C*((Nat.log 2 N+1:ℕ):ℝ)^6*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
  classical
  obtain ⟨D,hD,hdyadic⟩ := exists_logarithmic_dyadic_sixth hε
  let C := max D (2*4^6)
  have hC : 0 < C := hD.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro N hN T hT ι S z m B hB hm hz
  let K := Nat.log 2 N+1
  let p := fun i => (m i).toNat
  let g := fun i => (⟨min (Nat.log 2 (p i)) (Nat.log 2 N),
    (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩ : Fin K)
  let U := fun j => S.filter (fun i => g i=j)
  have hp (i : ι) (hi : i∈S) : 1 ≤ p i ∧ p i ≤ N := by
    have hh := hm i hi
    dsimp only [p]
    omega
  have hpInt (i : ι) (hi : i∈S) : (p i:ℤ)=m i :=
    Int.toNat_of_nonneg (by have := (hm i hi).1; omega)
  have hlabel (j : Fin K) (i : ι) (hi : i∈U j) : Nat.log 2 (p i)=(j:ℕ) := by
    obtain ⟨hi,hgi⟩ := Finset.mem_filter.mp hi
    have hg := congrArg (fun j : Fin K => (j:ℕ)) hgi
    dsimp only [g] at hg
    rwa [min_eq_left (Nat.log_mono_right (hp i hi).2)] at hg
  have hfiber (j : Fin K) (k : ℤ) :
      (∑ i∈(U j).filter (fun i => m i=k), ‖z i‖) ≤ B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)) (hz k)
    intro i hi
    obtain ⟨hi,hk⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hk⟩
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpowN : 1 ≤ (N:ℝ)^((3:ℝ)+ε) := Real.one_le_rpow hN₁ (by positivity)
  have hcell (j : Fin K) : logarithmicSixMoment T (U j) z m ≤
      C*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
    by_cases hj : 2 ≤ (j:ℕ)
    · have hX : (4:ℝ) ≤ (2:ℝ)^(j:ℕ) := by
        simpa only [show (2:ℝ)^2=4 by norm_num] using
          pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj
      have hjN : (j:ℕ) ≤ Nat.log 2 N := by have := j.isLt; dsimp [K] at this; omega
      have hXN : (2:ℝ)^(j:ℕ) ≤ N := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hjN).trans
          (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
      have hrange (i : ι) (hi : i∈U j) : (m i:ℝ)∈Icc ((2:ℝ)^(j:ℕ)) (2*(2:ℝ)^(j:ℕ)) := by
        have his := (Finset.mem_filter.mp hi).1
        have hlo := Nat.pow_log_le_self 2 (by have := (hp i his).1; omega : p i ≠ 0)
        have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (p i)
        rw [hlabel j i hi] at hlo hhi
        rw [pow_succ] at hhi
        have hpr : (p i:ℝ)=(m i:ℝ) := by exact_mod_cast hpInt i his
        constructor
        · have hh : (2:ℝ)^(j:ℕ) ≤ (p i:ℝ) := by exact_mod_cast hlo
          rwa [hpr] at hh
        · have hh : (p i:ℝ) ≤ 2*(2:ℝ)^(j:ℕ) := by exact_mod_cast (show p i ≤ 2*2^(j:ℕ) by omega)
          rwa [hpr] at hh
      have hh := hdyadic ((2:ℝ)^(j:ℕ)) T hX hT ι (U j) z m B hB hrange (hfiber j)
      apply hh.trans
      gcongr
      exact le_max_left _ _
    · have hrange (i : ι) (hi : i∈U j) : 1 ≤ m i ∧ m i ≤ 4 := by
        have his := (Finset.mem_filter.mp hi).1
        have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (p i)
        rw [hlabel j i hi] at hhi
        have hpow : 2^((j:ℕ)+1) ≤ (4:ℕ) := by
          simpa only [show (2:ℕ)^2=4 by norm_num] using
            Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) (show (j:ℕ)+1 ≤ 2 by omega)
        have he := hpInt i his
        exact ⟨(hm i his).1,by omega⟩
      have hh := logarithmicSixMoment_small hT (U j) z m hrange (hfiber j)
      have hcoeff : 2*4^6 ≤ C := le_max_right _ _
      calc
        _ ≤ 2*T*(4*B)^6 := hh
        _ = (2*4^6)*B^6*T := by ring
        _ ≤ C*B^6*T := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (by positivity)) hT
        _ ≤ C*B^6*(T+N) := mul_le_mul_of_nonneg_left
          (by linarith only [hN₁] : T ≤ T+N) (by positivity)
        _ ≤ C*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) :=
          le_mul_of_one_le_right (show 0 ≤ C*B^6*(T+(N:ℝ)) by positivity) hpowN
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hcell j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hh := (logarithmicSixMoment_fiberwise T S z m g).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))
  exact hh.trans_eq (by dsimp only [K]; ring)

private theorem logSix_shell_count {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    (((Nat.log 2 N+1:ℕ):ℝ))^6 ≤ (2*(1+6/η))^6*(N:ℝ)^η := by
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := zero_lt_one.trans_le hN₁
  have hp : (2:ℝ)^(Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) _) hp
  rw [Real.log_pow] at hl
  have hlogtwo : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hmul := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (Nat.log 2 N))
  have hcount : ((Nat.log 2 N+1:ℕ):ℝ) ≤ 2*(1+Real.log N) := by
    push_cast
    nlinarith only [hl,hmul]
  have hbudget := one_add_log_le_rpow_budget hN₁ (show 0 < η/6 by positivity)
  have he : 1/(η/6)=6/η := by field_simp
  rw [he] at hbudget
  have hpoint := hcount.trans (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0:ℝ) ≤ 2))
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 N+1)) hpoint 6
  have hexp : ((N:ℝ)^(η/6))^6=(N:ℝ)^η := by
    rw [←Real.rpow_mul_natCast hN₀.le]
    congr 1
    norm_num
  simpa only [mul_pow,hexp,mul_assoc] using hs

                                                              
                                                                              
                                                                 
theorem exists_logarithmic_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 1 ≤ m i ∧ m i ≤ N) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicSixMoment T S z m ≤ C*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨D,hD,hbound⟩ := exists_logarithmic_sixth_log_loss (ε:=ε/2) (by positivity)
  let E := (2*(1+6/(ε/2)))^6
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨D*E,by positivity,?_⟩
  intro N hN T hT ι S z m B hB hm hz
  have hN₀ : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount := logSix_shell_count hN (show 0 < ε/2 by positivity)
  change (((Nat.log 2 N+1:ℕ):ℝ))^6 ≤ E*(N:ℝ)^(ε/2) at hcount
  have hh := hbound N hN T hT ι S z m B hB hm hz
  have hmain : D*((Nat.log 2 N+1:ℕ):ℝ)^6*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε/2) ≤
      D*(E*(N:ℝ)^(ε/2))*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε/2) := by gcongr
  apply hh.trans (hmain.trans_eq ?_)
  calc
    _ = (D*E)*B^6*(T+N)*((N:ℝ)^(ε/2)*(N:ℝ)^((3:ℝ)+ε/2)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN₀]
      congr 2
      ring

                                                                    
                                                                   
end TaoTrudgianYang2025.LogarithmicSixth
