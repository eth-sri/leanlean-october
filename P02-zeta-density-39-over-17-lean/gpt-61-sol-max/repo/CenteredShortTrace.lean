module
import Mathlib
public import CenteredDilatedReflection
public import GuthMaynard.Improvement.SourceRatioHeightBudget

@[expose] public section

noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- Strict dyadic endpoints agree with shellEnergy's [H,2H) convention. -/
theorem strict_dyadic_prefix {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (height weight : ι → ℝ) {Y : ℝ} (hY : 0 ≤ Y) (J : ℕ) :
    (∑ q ∈ S.filter (fun q => height q < (2:ℝ)^J*Y), weight q) =
      (∑ q ∈ S.filter (fun q => height q < Y), weight q) +
      ∑ j ∈ range J, ∑ q ∈ S.filter
        (fun q => (2:ℝ)^j*Y ≤ height q ∧ height q < (2:ℝ)^(j+1)*Y), weight q := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hstep : (2:ℝ)^J*Y ≤ (2:ℝ)^(J+1)*Y := by bound
    have hlo : (S.filter (fun q => height q < (2:ℝ)^(J+1)*Y)).filter
        (fun q => height q < (2:ℝ)^J*Y) = S.filter (fun q => height q < (2:ℝ)^J*Y) := by grind
    have hhi : (S.filter (fun q => height q < (2:ℝ)^(J+1)*Y)).filter
        (fun q => ¬height q < (2:ℝ)^J*Y) = S.filter
        (fun q => (2:ℝ)^J*Y ≤ height q ∧ height q < (2:ℝ)^(J+1)*Y) := by
      ext q
      simp only [mem_filter,not_lt]
      tauto
    have hh := sum_filter_add_sum_filter_not (S.filter (fun q => height q < (2:ℝ)^(J+1)*Y))
      (fun q => height q < (2:ℝ)^J*Y) weight
    rw [hlo,hhi] at hh
    rw [← hh,ih,sum_range_succ]
    ring

/-- The actual least dyadic cover has only a logarithmic number of shells.
The factor 8 in the reflected-length assumption below is recorded explicitly. -/
theorem reflection_shell_count {T L : ℝ} (hT : 1 < T) (hL : 1 ≤ L)
    (hY : Real.pi*L/8 ≤ T) :
    ∃ J : ℕ, T < (2:ℝ)^J*(Real.pi*L/8) ∧
      (∀ j < J, (2:ℝ)^j*(Real.pi*L/8) < 2*T) ∧
      (J:ℝ) ≤ 4+Real.log T/Real.log 2 := by
  have hLp : 0 < L := by linarith
  have hYp : 0 < Real.pi*L/8 := by positivity
  obtain ⟨J,hcover,hmin,_,_⟩ := GuthMaynard.Improvement.source_least_height_cover hYp
    (show Real.pi*L/8 ≤ 2*T by linarith)
  refine ⟨J,lt_of_lt_of_le (by linarith) hcover,hmin,?_⟩
  cases hJ : J with
  | zero =>
    simp only [Nat.cast_zero]
    have hlT := Real.log_nonneg hT.le
    positivity
  | succ j =>
    have hh := hmin j (by omega)
    have hylo : 1/4 ≤ Real.pi*L/8 := by nlinarith [Real.pi_gt_three]
    have hp : (2:ℝ)^j < 8*T := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < (2:ℝ)^j) hp.le
    rw [Real.log_pow,show (8:ℝ)=2^3 by norm_num,Real.log_mul (by norm_num) (by linarith),
      Real.log_pow] at hlog
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hj : (j:ℝ) ≤ 3+Real.log T/Real.log 2 := by
      calc
        _ ≤ (3*Real.log 2+Real.log T)/Real.log 2 := (le_div_iff₀ htwo).mpr (by simpa using hlog)
        _ = _ := by field_simp
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

section
variable (w : MathCollab.Density.ReflectionCutoff)
include w

/-- A squared cutoff is still an actual smooth reflection cutoff. -/
def reflectionSquare  :
    MathCollab.Density.ReflectionCutoff where
  toFun x := (w x)^2
  smooth := w.smooth.pow 2
  support := by
    apply subset_trans (closure_mono ?_) w.support
    simp_all

section
variable (L : ℝ) (W : Finset ℝ)
include L W

/-- The literal discrete Gram matrix with the published squared cutoff. -/
def cutoffGramMatrix  :
    Matrix W W ℂ := fun t u => ∑' n : ℕ,
      (((w ((n:ℝ)/L))^2:ℝ):ℂ)*MathCollab.Density.dirichletPhase ((n:ℝ)/L) (t-u)

/-- The continuous term is kept independently of the discrete Gram sum. -/
def cutoffContinuousMatrix  :
    Matrix W W ℂ := fun t u => (L:ℂ)*
      MathCollab.Density.cutoffIntegral (reflectionSquare w) (t-u)

def cutoffCenteredMatrix  :
    Matrix W W ℂ := cutoffGramMatrix w L W-cutoffContinuousMatrix w L W

theorem cutoff_centered_entry  (t u : W) :
    cutoffCenteredMatrix w L W t u =
      MathCollab.Density.hKernel (reflectionSquare w) L (t-u) := rfl

theorem cutoff_centered_hermitian  : (cutoffCenteredMatrix w L W).IsHermitian := by
  ext t u
  simp only [Matrix.conjTranspose_apply,cutoff_centered_entry]
  rw [show (u:ℝ)-t = -((t:ℝ)-u) by ring,MathCollab.Density.hKernel_neg]
  simp

/-- The signed second trace is exactly the finite centered-kernel energy. -/
theorem cutoff_centered_trace_identity  :
    Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W) =
      ((∑ t ∈ W, ∑ u ∈ W,
        ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2:ℝ):ℂ) := by
  let H := cutoffCenteredMatrix w L W
  have hh : H.conjTranspose=H := cutoff_centered_hermitian w L W
  change Matrix.trace (H*H) = _
  nth_rw 2 [← hh]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
  have he (t u : W) : H t u*star (H t u) = ((‖H t u‖^2:ℝ):ℂ) := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.mul_conj' (H t u)
  simp_rw [he]
  simp only [H,cutoff_centered_entry,Complex.ofReal_sum]
  rw [Finset.sum_coe_sort W (fun t => ∑ u : W,
    ((‖MathCollab.Density.hKernel (reflectionSquare w) L (t-(u:ℝ))‖^2:ℝ):ℂ))]
  apply sum_congr rfl
  intro t _
  exact Finset.sum_coe_sort W (fun u =>
    ((‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2:ℝ):ℂ))
end


/-- The full discrete centered energy; near-diagonal terms and shell-count
losses have been discharged. Fixed reflected-length factors are absorbed
in the constant; the exact undilated length T/L governs the hypothesis. -/
theorem centered_energy_short_range 
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (T/L)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        C*T^η*L*(W.card : ℝ)^2 := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨C,B,hC,hB,hshell⟩ := centered_shell_dilated_short_range w hK (A := 2) (by norm_num) hδ (D := 2) (by norm_num)
  obtain ⟨B₀,hB₀,hnear⟩ := GuthMaynard.Improvement.centeredKernel_near w (A := 2) (by norm_num)
  let D := 4+1/((η/2)*Real.log 2)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1+B₀^2+D*(C+B),by positivity,?_⟩
  intro T t₀ L hT hL W hR hlen hW hsep
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := by linarith
  let Y := Real.pi*L/8
  have hYp : 0 < Y := by dsimp [Y]; positivity
  have hd1 := Real.one_le_rpow hT.le hδ.le
  have hη1 := Real.one_le_rpow hT.le hη.le
  have hpow : T^(η/2)*T^(η/2)=T^η := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  have hdist (t : ℝ) (ht : t ∈ W) (u : ℝ) (hu : u ∈ W) : |t-u| ≤ T := by grind
  have hn (v : ℝ) (hv : |v| ≤ Y) : ‖MathCollab.Density.hKernel w L v‖^2 ≤ B₀^2 := by
    have hh := hnear L v hLp hv
    rw [GuthMaynard.Improvement.centeredKernel_eq_density_hKernel w hLp] at hh
    have hfrac : B₀*L/L^2 ≤ B₀ := by field_simp <;> nlinarith
    exact pow_le_pow_left₀ (norm_nonneg _) (hh.trans hfrac) 2
  have hnearSum : (∑ p ∈ (W ×ˢ W).filter (fun p => |p.1-p.2| < Y),
      ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) ≤ B₀^2*(W.card:ℝ)^2 := by
    calc
      _ ≤ ∑ _p ∈ (W ×ˢ W).filter (fun p => |p.1-p.2| < Y), B₀^2 :=
        sum_le_sum (fun p hp => hn _ (mem_filter.mp hp).2.le)
      _ ≤ ∑ _p ∈ W ×ˢ W, B₀^2 := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := by simp [card_product]; ring
  have hbase : B₀^2*(W.card:ℝ)^2 ≤ B₀^2*T^η*L*(W.card:ℝ)^2 := by
    have hx : 1 ≤ T^η*L := one_le_mul_of_one_le_of_one_le hη1 hL
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg B₀)
    simpa only [mul_one,mul_assoc] using mul_le_mul_of_nonneg_right hh (sq_nonneg (W.card:ℝ))
  by_cases hYT : Y ≤ T
  · obtain ⟨J,hcover,hmin,hJ⟩ := reflection_shell_count hT hL hYT
    have hfilter : (W ×ˢ W).filter (fun p => |p.1-p.2| < (2:ℝ)^J*Y) = W ×ˢ W := by
      apply filter_eq_self.mpr
      intro p hp
      exact (hdist p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2).trans_lt hcover
    have he := strict_dyadic_prefix (W ×ˢ W) (fun p => |p.1-p.2|)
      (fun p => ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) hYp.le J
    rw [hfilter] at he
    have hs (j : ℕ) (hj : j ∈ range J) :
        (∑ p ∈ (W ×ˢ W).filter
          (fun p => (2:ℝ)^j*Y ≤ |p.1-p.2| ∧ |p.1-p.2| < (2:ℝ)^(j+1)*Y),
          ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) ≤
        (C+B)*T^(η/2)*L*(W.card:ℝ)^2 := by
      let H := (2:ℝ)^j*Y
      have hHp : 0 < H := by dsimp [H]; positivity
      have hHT : H < 2*T := hmin j (mem_range.mp hj)
      have hlenH : (H/(2*L))^K ≤ W.card := by
        have hdiv : H/(2*L) ≤ T/L :=
          (div_le_div_iff₀ (by positivity : 0 < 2*L) hLp).mpr (by nlinarith)
        exact (pow_le_pow_left₀ (by positivity) hdiv K).trans hlen
      have hh := hshell T t₀ L H hT hLp hHp W hR hlenH hW hsep
      have her : L^(2-2*(2:ℝ)) ≤ L := by
        simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (2:ℝ)-2*2 ≤ 1)
      have heq : (∑ p ∈ (W ×ˢ W).filter
          (fun p => (2:ℝ)^j*Y ≤ |p.1-p.2| ∧ |p.1-p.2| < (2:ℝ)^(j+1)*Y),
          ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) =
          MathCollab.Density.shellEnergy w L H W := by
        simp only [sum_filter,sum_product,MathCollab.Density.shellEnergy,H,pow_succ]
        ring
      rw [heq]
      calc
        _ ≤ C*T^(η/2)*L*(W.card:ℝ)^2+B*(W.card:ℝ)^2*L^(2-2*(2:ℝ)) := hh
        _ ≤ C*T^(η/2)*L*(W.card:ℝ)^2+B*(W.card:ℝ)^2*L := by gcongr
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ B*L*(W.card:ℝ)^2)]
    have hJD : (J:ℝ) ≤ D*T^(η/2) := by
      calc
        _ ≤ 4+Real.log T/Real.log 2 := hJ
        _ ≤ 4*T^(η/2)+(T^(η/2)/(η/2))/Real.log 2 := by
          apply add_le_add (by linarith)
          exact div_le_div_of_nonneg_right (Real.log_le_rpow_div hTp.le hδ) htwo.le
        _ = _ := by dsimp [D]; field_simp
    calc
      _ = ∑ p ∈ W ×ˢ W, ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2 := (sum_product _ _ _).symm
      _ = _ := he
      _ ≤ B₀^2*(W.card:ℝ)^2+∑ _j ∈ range J, (C+B)*T^(η/2)*L*(W.card:ℝ)^2 :=
        add_le_add hnearSum (sum_le_sum hs)
      _ = B₀^2*(W.card:ℝ)^2+(J:ℝ)*((C+B)*T^(η/2)*L*(W.card:ℝ)^2) := by simp
      _ ≤ B₀^2*T^η*L*(W.card:ℝ)^2+(D*T^(η/2))*((C+B)*T^(η/2)*L*(W.card:ℝ)^2) := by gcongr
      _ = (B₀^2+D*(C+B))*T^η*L*(W.card:ℝ)^2 := by rw [← hpow]; ring
      _ ≤ _ := by gcongr; linarith
  · have hfull : (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        B₀^2*(W.card:ℝ)^2 := by
      calc
        _ ≤ ∑ _t ∈ W, ∑ _u ∈ W, B₀^2 := by
          apply sum_le_sum
          intro t ht
          apply sum_le_sum
          grind
        _ = _ := by simp; ring
    exact hfull.trans (hbase.trans (by gcongr; nlinarith))
end



