module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Clean.Contractions

public import Erdos821.S2.ContractionTask
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Filter
open Erdos821.Blueprint.Graph

section

namespace Erdos821.S2Contr

section
variable (ell : ℕ) (hell : 0 < ell) (F : FixedData) (P : PrimeGroups) (J : ℕ) (x Ca G : ℝ) (hx : 4 ≤ x)

theorem normBound_mono {α : Type*} {mass : α → ℝ} {K : α → α → ℂ}
    {C D : ℝ} (hCD : C ≤ D) (hK : NormBound mass K C) :
    NormBound mass K D := by solve_by_elim [_root_.Erdos821.P3Clean.normBound_mono]

include hell in
private theorem choose_lower_linear       :
    J + 1 ≤ Nat.choose (J + ell) ell := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hrec : Nat.choose (J + 1 + ell) ell =
        Nat.choose (J + ell) (ell - 1) + Nat.choose (J + ell) ell := by
      calc
        Nat.choose (J + 1 + ell) ell =
            Nat.choose (J + ell).succ (ell - 1).succ := by
              congr 2 <;> omega
        _ = Nat.choose (J + ell) (ell - 1) +
            Nat.choose (J + ell) (ell - 1).succ := Nat.choose_succ_succ _ _
        _ = _ := by rw [show (ell - 1).succ = ell by omega]
    have hpos : 0 < Nat.choose (J + ell) (ell - 1) :=
      Nat.choose_pos (by omega)
    rw [hrec]
    omega

include hell in
private theorem log_choose_tendsto     :
    Tendsto (fun J : ℕ => Real.log (Nat.choose (J + ell) ell : ℝ)) atTop atTop := by
  have hsucc : Tendsto (fun J : ℕ => J + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with J hJ
    omega
  have hcast : Tendsto (fun J : ℕ => ((J + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsucc
  apply Filter.tendsto_atTop_mono ?_ (Real.tendsto_log_atTop.comp hcast)
  intro J
  change Real.log ((J + 1 : ℕ) : ℝ) ≤
    Real.log (Nat.choose (J + ell) ell : ℝ)
  apply Real.log_le_log
  · positivity
  · exact_mod_cast choose_lower_linear ell hell J

private theorem omission_power_lower    
        (hL : 0 < L x)
    (hsmall : F.c₀ * T x ≤ (P.smallGroups.card : ℝ)) :
    (L x) ^ (F.c₀ * Real.log (Nat.choose (J + F.ell) F.ell : ℝ)) ≤
      (omissionNumber F P J : ℝ) := by
  let c : ℕ := Nat.choose (J + F.ell) F.ell
  have hcposN : 0 < c := by
    dsimp [c]
    exact Nat.choose_pos (by omega)
  
  have hcOne : 1 ≤ (c : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hcposN)
  have hOpos : 0 < (omissionNumber F P J : ℝ) := by
    unfold omissionNumber
    positivity
  have hlogc : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg hcOne
  have hlogO : Real.log (omissionNumber F P J : ℝ) =
      (P.smallGroups.card : ℝ) * Real.log (c : ℝ) := by
    simp [omissionNumber, c, Nat.cast_pow, Real.log_pow]
  have hlog : Real.log (L x) * (F.c₀ * Real.log (c : ℝ)) ≤
      Real.log (omissionNumber F P J : ℝ) := by
    rw [show Real.log (L x) = T x by rfl, hlogO]
    have hmul := mul_le_mul_of_nonneg_right hsmall hlogc
    grind
  rw [Real.rpow_def_of_pos hL]
  calc
    Real.exp (Real.log (L x) * (F.c₀ * Real.log (c : ℝ))) ≤
        Real.exp (Real.log (omissionNumber F P J : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (omissionNumber F P J : ℝ) := Real.exp_log hOpos

private theorem rpow_mono_exp {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) :
    x ^ a ≤ x ^ b := by
  bound

include hx in
private theorem gap_two_bound     :
    4 * x ^ (-G - 2) ≤ (1 / 2 : ℝ) * x ^ (-G) := by
  have hxpos : 0 < x := by linarith
  have hx2 : 8 ≤ x ^ (2 : ℕ) := by nlinarith [sq_nonneg (x - 4)]
  have hfrac : 4 / x ^ (2 : ℕ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < x ^ (2 : ℕ))).2
    nlinarith
  have hpow2 : x ^ (-2 : ℝ) = (x ^ (2 : ℕ))⁻¹ := by
    simp_all
  have hadd : x ^ (-G - 2) = x ^ (-G) * x ^ (-2 : ℝ) := by
    rw [show -G - 2 = -G + (-2) by ring, Real.rpow_add hxpos]
  calc
    4 * x ^ (-G - 2) = (4 / x ^ (2 : ℕ)) * x ^ (-G) := by
      rw [hadd, hpow2]
      ring
    _ ≤ (1 / 2 : ℝ) * x ^ (-G) :=
      mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg hxpos.le _)

include hx in
private theorem gap_four_bound     :
    2 * x ^ (-G - 4) ≤ (1 / 2 : ℝ) * x ^ (-G) := by
  have hxpos : 0 < x := by linarith
  have hx2 : 8 ≤ x ^ (2 : ℕ) := by nlinarith [sq_nonneg (x - 4)]
  have hx4 : 4 ≤ x ^ (4 : ℕ) := by
    nlinarith [sq_nonneg (x ^ (2 : ℕ) - 4)]
  have hfrac : 2 / x ^ (4 : ℕ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < x ^ (4 : ℕ))).2
    nlinarith
  have hpow4 : x ^ (-4 : ℝ) = (x ^ (4 : ℕ))⁻¹ := by
    simp_all
  have hadd : x ^ (-G - 4) = x ^ (-G) * x ^ (-4 : ℝ) := by
    rw [show -G - 4 = -G + (-4) by ring, Real.rpow_add hxpos]
  calc
    2 * x ^ (-G - 4) = (2 / x ^ (4 : ℕ)) * x ^ (-G) := by
      rw [hadd, hpow4]
      ring
    _ ≤ (1 / 2 : ℝ) * x ^ (-G) :=
      mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg hxpos.le _)

private theorem rare_decay_bound      
       x  (hL : 4 ≤ L x)
    (hsmall : F.c₀ * T x ≤ (P.smallGroups.card : ℝ))
    (hgain : Ca + G + 3 < (F.c₀ / 2) *
      Real.log (Nat.choose (J + F.ell) F.ell : ℝ)) :
    2 * (L x) ^ Ca * Real.sqrt ((memoryCutoff x : ℝ) / omissionNumber F P J) ≤
      (1 / 2 : ℝ) * (L x) ^ (-G) := by
  let c : ℝ := Nat.choose (J + F.ell) F.ell
  let d : ℝ := (F.c₀ / 2) * Real.log c
  have hLpos : 0 < L x := by linarith
  have hcut : (memoryCutoff x : ℝ) ≤ 2 * (L x) ^ (2 : ℕ) := by
    have hceil : (memoryCutoff x : ℝ) < (L x) ^ (2 : ℕ) + 1 := by
      simpa only [memoryCutoff] using
        (Nat.ceil_lt_add_one (sq_nonneg (L x)))
    have hLsq : 1 ≤ (L x) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (L x - 4)]
    linarith
  have hO : (L x) ^ (F.c₀ * Real.log c) ≤ (omissionNumber F P J : ℝ) := by
    solve_by_elim [omission_power_lower]
  
  have hdiv : (memoryCutoff x : ℝ) / (omissionNumber F P J : ℝ) ≤
      (2 * (L x) ^ (2 : ℕ)) / (L x) ^ (F.c₀ * Real.log c) := by
    bound
  have hsqrtCut : Real.sqrt (2 * (L x) ^ (2 : ℕ)) =
      Real.sqrt 2 * L x := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
      abs_of_pos hLpos]
  have hsqrtO : Real.sqrt ((L x) ^ (F.c₀ * Real.log c)) = (L x) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLpos.le]
    congr 1
    dsimp [d]
    ring
  have hsqrtDiv : Real.sqrt ((2 * (L x) ^ (2 : ℕ)) /
      (L x) ^ (F.c₀ * Real.log c)) =
      Real.sqrt 2 * L x / (L x) ^ d := by
    rw [Real.sqrt_div (by positivity), hsqrtCut, hsqrtO]
  have hratio : Real.sqrt ((memoryCutoff x : ℝ) /
      (omissionNumber F P J : ℝ)) ≤ Real.sqrt 2 * L x / (L x) ^ d := by
    calc
      _ ≤ Real.sqrt ((2 * (L x) ^ (2 : ℕ)) /
          (L x) ^ (F.c₀ * Real.log c)) := Real.sqrt_le_sqrt hdiv
      _ = _ := hsqrtDiv
  have hcombine : (L x) ^ Ca * (Real.sqrt 2 * L x / (L x) ^ d) =
      Real.sqrt 2 * (L x) ^ (Ca + 1 - d) := by
    calc
      _ = Real.sqrt 2 * ((L x) ^ Ca * (L x) ^ (1 : ℝ)) / (L x) ^ d := by
        rw [Real.rpow_one]
        ring
      _ = Real.sqrt 2 * (L x) ^ (Ca + 1) / (L x) ^ d := by
        rw [← Real.rpow_add hLpos]
      _ = _ := by rw [Real.rpow_sub hLpos]; ring
  have hExp : Ca + 1 - d ≤ -G - 2 := by
    dsimp [d] at hgain ⊢
    linarith
  have hpow : (L x) ^ (Ca + 1 - d) ≤ (L x) ^ (-G - 2) :=
    rpow_mono_exp (by linarith) hExp
  have hs2 : 2 * Real.sqrt 2 ≤ (4 : ℝ) := by
    have hs : Real.sqrt 2 ≤ 2 := by
      norm_num
    nlinarith
  calc
    2 * (L x) ^ Ca * Real.sqrt ((memoryCutoff x : ℝ) /
        omissionNumber F P J)
        ≤ 2 * (L x) ^ Ca * (Real.sqrt 2 * L x / (L x) ^ d) := by
          bound
    _ = 2 * Real.sqrt 2 * (L x) ^ (Ca + 1 - d) := by
      grind
    _ ≤ 4 * (L x) ^ (-G - 2) := by
      bound
    _ ≤ _ := gap_two_bound (L x) G hL

private theorem clean_decay_bound (G Eid Cs x : ℝ) (hL : 4 ≤ x)
    (hEid : G + Cs + 4 ≤ Eid) :
    2 * x ^ (-Eid + Cs) ≤ (1 / 2 : ℝ) * x ^ (-G) := by
  have hExp : -Eid + Cs ≤ -G - 4 := by linarith
  calc
    2 * x ^ (-Eid + Cs) ≤ 2 * x ^ (-G - 4) := by
      bound
    _ ≤ _ := gap_four_bound x G hL

theorem WholeEdgeContractionTask_proof    r  :
    Erdos821.S2Core.WholeEdgeContractionTask F r := by
  intro hRare hClean G hG
  obtain ⟨Cs, hCleanBound⟩ := hClean
  let Eid : ℝ := max 1 (G + Cs + 4)
  have hEid : 0 < Eid := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hEidLower : G + Cs + 4 ≤ Eid := le_max_right _ _
  refine ⟨Eid, hEid, ?_⟩
  intro m C₁
  obtain ⟨Ca, hRareBound⟩ := hRare m C₁
  have hChoose := log_choose_tendsto F.ell
    (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) F.ell_pos)
  let Jgain : ℝ := (2 / F.c₀) * (Ca + G + 4)
  have hJEventually : ∀ᶠ J : ℕ in atTop,
      Jgain ≤ Real.log (Nat.choose (J + F.ell) F.ell : ℝ) :=
    Filter.tendsto_atTop.1 hChoose Jgain
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.1 hJEventually
  have hScaleEventually : ∀ᶠ x : ℝ in atTop, 4 ≤ L x := by
    simpa [L] using (Filter.tendsto_atTop.1 Real.tendsto_log_atTop (4 : ℝ))
  obtain ⟨xScale, hScale⟩ := Filter.eventually_atTop.1 hScaleEventually
  refine ⟨J₀, ?_⟩
  intro J hJ C₂
  obtain ⟨xRare, hRareX⟩ := hRareBound J C₂
  obtain ⟨xClean, hCleanX⟩ := hCleanBound m C₁ J C₂ Eid hEid
  refine ⟨max xScale (max xRare xClean), ?_⟩
  intro x hx P hP A hA hk hk' hIdeal theta i
  have hxScale : 4 ≤ L x := hScale x (le_trans (le_max_left _ _) hx)
  have hsmall : F.c₀ * T x ≤ (P.smallGroups.card : ℝ) := hP.1
  have hJgain : Ca + G + 3 < (F.c₀ / 2) *
      Real.log (Nat.choose (J + F.ell) F.ell : ℝ) := by
    have h := hJ₀ J hJ
    have hc₀ : 0 < F.c₀ := F.c₀_pos
    have hscaled : Ca + G + 4 ≤ (F.c₀ / 2) *
        Real.log (Nat.choose (J + F.ell) F.ell : ℝ) := by
      calc
        _ = (F.c₀ / 2) * Jgain := by
          dsimp [Jgain]
          field_simp [ne_of_gt hc₀]
        _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
    linarith
  have hxRare : xRare ≤ x := by
    apply le_trans _ hx
    norm_num
  have hxClean : xClean ≤ x := by
    apply le_trans _ hx
    norm_num
  have hRareAt := hRareX x hxRare P hP A hA hk hk' theta i
    (fun _ _ _ => (1 : ℂ)) (by intro s t c; simp)
  have hCleanAt := hCleanX x hxClean P hP A hA hk hk' hIdeal theta i
  have hrareConst := rare_decay_bound F P J Ca G x hxScale hsmall hJgain
  have hcleanConst := clean_decay_bound G Eid Cs (L x) hxScale hEidLower
  let keep : P.MemoryState (J + F.ell) → Prop :=
    fun s => P.memorySize s ≤ memoryCutoff x
  let Kclean : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℂ :=
    projectKernel keep (Erdos821.S2Core.memoryEdgeKernel A (N x) r.rho theta i .clean
      (fun _ _ _ => 1))
  let Kdirty : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℂ :=
    projectKernel keep (Erdos821.S2Core.memoryEdgeKernel A (N x) r.rho theta i .dirty
      (fun _ _ _ => 1))
  let Kall : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℂ :=
    projectKernel keep (Erdos821.S2Core.memoryEdgeKernel A (N x) r.rho theta i .all
      (fun _ _ _ => 1))
  have hKernel : Kall = fun s t => Kclean s t + Kdirty s t := by
    funext s t
    simp only [Kall, Kclean, Kdirty]
    have hAll := Erdos821.S2Core.memoryEdgeKernel_all A (N x) r.rho theta i
      (fun _ _ _ => (1 : ℂ)) s t
    by_cases hkeep : keep s ∧ keep t
    · simp only [projectKernel, ite_eq_left hkeep]
      exact hAll
    · simp [projectKernel, hkeep]
  have hCleanNorm : NormBound (P.memoryMass F J (N x)) Kclean
      (2 * (L x) ^ (-Eid + Cs)) := by
    simpa only [Kclean] using hCleanAt
  have hDirtyNorm : NormBound (P.memoryMass F J (N x)) Kdirty
      (2 * (L x) ^ Ca * Real.sqrt ((memoryCutoff x : ℝ) / omissionNumber F P J)) := by
    simpa only [Kdirty] using hRareAt
  have hSumNorm := Erdos821.S2Core.normBound_add (P.memoryMass F J (N x)) Kclean Kdirty
    (2 * (L x) ^ (-Eid + Cs))
    (2 * (L x) ^ Ca * Real.sqrt ((memoryCutoff x : ℝ) / omissionNumber F P J))
    hCleanNorm hDirtyNorm
  have hconst : 2 * (L x) ^ (-Eid + Cs) +
      2 * (L x) ^ Ca * Real.sqrt ((memoryCutoff x : ℝ) / omissionNumber F P J) ≤
        (L x) ^ (-G) := by
    linarith
  have hTargetNorm := normBound_mono hconst hSumNorm
  change NormBound (P.memoryMass F J (N x)) Kall ((L x) ^ (-G))
  rw [hKernel]
  exact hTargetNorm

end

end Erdos821.S2Contr
