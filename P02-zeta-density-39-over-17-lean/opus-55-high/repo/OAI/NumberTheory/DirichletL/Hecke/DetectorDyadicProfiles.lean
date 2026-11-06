module
public import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicSupport
public import OAI.NumberTheory.DirichletL.CompactProfileFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open CubicReflectionKernel
section
variable (F : (ℝ × ℝ) → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
include F hF
theorem section_deriv_smooth :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  pc_241

theorem section_iteratedDeriv_smooth (j : ℕ) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem compact_family_deriv_integrable (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ × ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by pf_188

theorem compact_family_deriv_L1_bound (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  pm_1406
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  grind

theorem compact_family_fourier_power_bound (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by pf_46

theorem compact_family_fourier_weighted_bound (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by pf_47
end

def ratioProfile (V W : ℝ→ℂ) (R x : ℝ) : ℂ := V (R*x)*W x

def logFamily (V W : ℝ→ℂ) (p : ℝ×ℝ) (y : ℝ) : ℂ :=
  Real.exp (-p.2*y) • ratioProfile V W p.1 (Real.exp (-y))

section
variable (V W : ℝ→ℂ)
include V W
lemma logFamily_smooth (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily V W)) := by
  unfold Function.uncurry logFamily ratioProfile
  have he : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => Real.exp (-p.1.2*p.2)) := by fun_prop
  have hv : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => V (p.1.1*Real.exp (-p.2))) :=
    hV.comp (by fun_prop)
  have hw : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => W (Real.exp (-p.2))) :=
    hW.comp (by fun_prop)
  exact he.smul (hv.mul hw)

lemma ratioProfile_support (R : ℝ) :
    Function.support (ratioProfile V W R)⊆Function.support W := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).2

lemma logFamily_support (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily V W p)⊆Icc (-Real.log b) (-Real.log a) := by
  exact mellinLogFamily_support (ratioProfile V W p.1) a b ha
    ((ratioProfile_support V W p.1).trans hW) p.2

theorem ratioProfile_mellin_bound
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (Rmax lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R∈Icc 0 Rmax, ∀ σ∈Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (ratioProfile V W R) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := compact_family_fourier_weighted_bound
    (logFamily V W) (logFamily_smooth V W hV hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support V W a b ha hWs)
    (Icc 0 Rmax ×ˢ Icc lo hi) (isCompact_Icc.prod isCompact_Icc) j
  pm_6337 R hR mellin_eq_logFamily_fourier
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (mellinLogFamily (ratioProfile V W R) σ) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j * ((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily V W (R,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow, mul_assoc]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (R,σ) ⟨hR,hσ⟩ _) (by positivity)

lemma inverseProfile_eq_ratio (Dstar D : ℝ) :
    HeckeDetectorDyadicBridge.inverseProfile V W Dstar D =ratioProfile V W (D /Dstar) := by
  funext x
  unfold HeckeDetectorDyadicBridge.inverseProfile ratioProfile
  congr 2
  ring

theorem exists_profile_bounds (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (lo hi : ℝ) :
    ∃ C : ℕ→ℝ, (∀ j, 0<C j) ∧
      (∀ j : ℕ, ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin W ((σ : ℂ)+t*Complex.I)‖≤C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0<Dstar → 0≤D → D ≤4*Dstar →
        ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile V W Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤C j) := by
  choose Cp hCp hbP using fun j => compact_source_mellin_strip_decay W a b ha hWs hW lo hi j
  choose Ci hCi hbI using fun j => ratioProfile_mellin_bound V W hV hW a b ha hWs 4 lo hi j
  refine ⟨fun j => Cp j+Ci j,fun j => add_pos (hCp j) (hCi j),?_,?_⟩
  · intro j σ hσ t
    exact (hbP j σ hσ t).trans (le_add_of_nonneg_right (hCi j).le)
  · intro j Dstar D hDs hD hratio σ hσ t
    rw [inverseProfile_eq_ratio]
    exact (hbI j (D /Dstar) ⟨div_nonneg hD hDs.le,(div_le_iff₀ hDs).mpr hratio⟩ σ hσ t).trans
      (le_add_of_nonneg_left (hCp j).le)
end

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
