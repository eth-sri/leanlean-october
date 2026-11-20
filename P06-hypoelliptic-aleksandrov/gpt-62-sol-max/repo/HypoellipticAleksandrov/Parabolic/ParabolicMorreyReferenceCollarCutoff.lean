module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff
import HypoellipticAleksandrov.Parabolic.WeakJetExtension
import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
import HypoellipticAleksandrov.Analysis.SmoothCutoff
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
This module fixes a normalized reference collar cutoff and derives its exact
selected-jet product estimate from the four restricted-component `MemLp`
certificates. It proves no Hölder, PDE, or representative theorem.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- The literal closed reference collar is contained in the open unit source box. -/
private theorem reference_closed_collar_subset_unit_box (d : Nat) :
    parabolicClosedBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0 ⊆
      parabolicBox (d := d) 1 1 0 0 := by
  rintro ⟨t, v⟩ hz
  rw [mem_parabolicClosedBox_iff] at hz
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · norm_num at hz ⊢
    linarith
  · norm_num at hz ⊢
    linarith
  · intro i
    simpa only [Pi.zero_apply, sub_zero] using lt_of_le_of_lt (hz.2.2 i) (by norm_num)

private lemma eq_zero_off_tsupport {d : ℕ} {f : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hz : z ∉ tsupport f) : f z = 0 := notMem_support.mp (fun h => hz (subset_tsupport f h))

section
variable {d : ℕ} {U : Set (TimeVelocity d)} {eta q : TimeVelocity d → ℝ} (hU : IsOpen U)
  (heta : ContDiff ℝ 2 eta) (hetaU : tsupport eta ⊆ U) (hq : ContDiffOn ℝ 2 q U)
include U hU heta hetaU hq

/-- The derivative product rule holds globally when the first factor is a cutoff
    supported where the second factor is smooth. -/
private lemma fderiv_cutoff_mul :
    fderiv ℝ (eta * q) = eta • fderiv ℝ q + q • fderiv ℝ eta := by
  funext z
  by_cases hz : z ∈ U
  · exact fderiv_mul (heta.differentiable (by norm_num) z)
      ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  · have he : z ∉ tsupport eta := fun h => hz (hetaU h)
    have hp : z ∉ tsupport (eta * q) := fun h => he (tsupport_mul_subset_left (f := eta) (g := q) h)
    simp [Pi.add_apply, Pi.smul_apply, eq_zero_off_tsupport he,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) he, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp]

/-- The ordered velocity-Hessian product rule for a cutoff. -/
private lemma velocityHessian_cutoff_mul (i j : Fin d) :
    (fun z => velocityHessian (eta * q) z i j) =
      (eta * fun z => velocityHessian q z i j) +
        (fun z => velocityGradient eta z i * velocityGradient q z j) +
        (fun z => velocityGradient eta z j * velocityGradient q z i) +
        (fun z => velocityHessian eta z i j * q z) := by
  funext z
  by_cases hz : z ∈ U
  · have hq' := hq.contDiffAt (hU.mem_nhds hz)
    have he := heta.differentiable (by norm_num) z
    have hq₁ := hq'.differentiableAt (by norm_num)
    have he₂ := (heta.contDiffAt.fderiv_right (m := 1) (by norm_num) :
      ContDiffAt ℝ 1 (fderiv ℝ eta) z).differentiableAt (by norm_num)
    have hq₂ := (hq'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    change fderiv ℝ (fderiv ℝ (eta * q)) z (0, Pi.single i 1) (0, Pi.single j 1) = _
    rw [fderiv_cutoff_mul hU heta hetaU hq, fderiv_add (he.smul hq₂) (hq₁.smul he₂),
      fderiv_smul he hq₂, fderiv_smul hq₁ he₂]
    simp [velocityHessian, velocityGradient]
    ring
  · have he : z ∉ tsupport eta := fun h => hz (hetaU h)
    have hp : z ∉ tsupport (eta * q) := fun h => he (tsupport_mul_subset_left (f := eta) (g := q) h)
    simp [eq_zero_off_tsupport he,
      eq_zero_off_tsupport (z := z) (fun h => he (velocityGradient_tsupport (i := i) eta h)),
      eq_zero_off_tsupport (z := z) (fun h => he (velocityGradient_tsupport (i := j) eta h)),
      eq_zero_off_tsupport (z := z) (fun h => he (velocityHessian_tsupport (i := i) (j := j) eta h)),
      eq_zero_off_tsupport (z := z) (fun h => hp (velocityHessian_tsupport (i := i) (j := j) (eta * q) h))]

end

section
variable {d : Nat} {eta : TimeVelocity d → Real}

theorem timeDerivative_cutoff_continuous
    (heta : ContDiff Real 2 eta) : Continuous (timeDerivative eta) := by
  exact ((heta.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

theorem velocityHessian_cutoff_continuous
    {i j : Fin d} (heta : ContDiff Real 2 eta) :
    Continuous (fun z => velocityHessian eta z i j) := by
  unfold velocityHessian
  have hfirst :=
    heta.fderiv_right (m := 1) (by norm_num)
  simpa using (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
    continuous_const

end

private lemma exists_uniform_jet_bound {d : ℕ} {eta : TimeVelocity d → ℝ}
    (he : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : HasCompactSupport eta) :
    ∃ M : ℝ, 0 < M ∧ ∀ k z, ‖parabolicJetComponent eta k z‖ ≤ M := by
  have h (k : ParabolicJetIndex d) : ∃ B : ℝ, ∀ z, ‖parabolicJetComponent eta k z‖ ≤ B := by
    rcases k with (_ | (_ | (i | ⟨i, j⟩)))
    exacts [he.continuous.bounded_above_of_compact_support hc,
      (timeDerivative_continuous he).bounded_above_of_compact_support (timeDerivative_compact hc),
      (velocityGradient_continuous he).bounded_above_of_compact_support (velocityGradient_compact hc),
      (velocityHessian_continuous he).bounded_above_of_compact_support (velocityHessian_compact hc)]
  choose b hb using h
  obtain ⟨B, hB⟩ := Finite.bddAbove_range b
  exact ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), fun k z =>
    (hb k z).trans ((hB (mem_range_self k)).trans (le_max_right _ _))⟩

private lemma cutoff_mul_lpNorm_le {d : ℕ} {U : Set (TimeVelocity d)}
    {a f : TimeVelocity d → ℝ} {M : ℝ} (hU : MeasurableSet U) (hM : 0 ≤ M)
    (ha : Continuous a) (haU : tsupport a ⊆ U) (haM : ∀ z, ‖a z‖ ≤ M)
    (hf : ParabolicMemLpOn U (parabolicExponent d) f) :
    MemLp (a * f) (parabolicExponent d) volume ∧
      parabolicLpNorm d (a * f) ≤ M * parabolicLpNormOn d f U := by
  have heq : a * U.indicator f = a * f := by
    ext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, eq_zero_off_tsupport (f := a) (fun h => hz (haU h))]
  have h := Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hM ha.aestronglyMeasurable
    ((memLp_indicator_iff_restrict hU).2 hf) (.of_forall fun z => by simpa using haM z)
  change MemLp (a * U.indicator f) _ _ ∧
    parabolicLpNorm d (a * U.indicator f) ≤ M * (eLpNorm (U.indicator f) _ _).toReal at h
  rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hU] at h
  exact h

private theorem parabolicExponent_one_le (d : Nat) :
    (1 : ENNReal) ≤ parabolicExponent d := le_add_of_nonneg_left bot_le

/-- The normalized reference collar cutoff has a selected-jet product bound
against the literal unit source box. -/
theorem exists_parabolicMorreyReferenceCollarCutoffJetConst (d : Nat) :
    ∃ eta : TimeVelocity d -> Real, ∃ C : Real, 0 < C ∧
      ContDiff Real (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
      (∀ᶠ z in 𝓝ˢ
        (parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0), eta z = 1) ∧
      tsupport eta ⊆ parabolicBox 1 1 0 0 ∧
      ∀ q : TimeVelocity d -> Real,
        ContDiffOn Real 2 q (parabolicBox 1 1 0 0) ->
        ParabolicMemLpOn (parabolicBox 1 1 0 0) (parabolicExponent d) q ->
        ParabolicMemLpOn (parabolicBox 1 1 0 0) (parabolicExponent d)
          (timeDerivative q) ->
        (∀ i : Fin d, ParabolicMemLpOn (parabolicBox 1 1 0 0)
          (parabolicExponent d) (fun z => velocityGradient q z i)) ->
        (∀ i j : Fin d, ParabolicMemLpOn (parabolicBox 1 1 0 0)
          (parabolicExponent d) (fun z => velocityHessian q z i j)) ->
        parabolicSmoothJetLpNorm d (fun z => eta z * q z) <=
          C * (parabolicLpNormOn d q (parabolicBox 1 1 0 0) +
               parabolicLpNormOn d (timeDerivative q) (parabolicBox 1 1 0 0) +
               ∑ i : Fin d, parabolicLpNormOn d
                 (fun z => velocityGradient q z i) (parabolicBox 1 1 0 0) +
               ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                 (fun z => velocityHessian q z i j) (parabolicBox 1 1 0 0))  := by
  let U := parabolicBox (d := d) 1 1 0 0
  have hU : IsOpen U := isOpen_parabolicBox 1 1 0 0
  obtain ⟨eta, he, hec, heU, _, heone⟩ := Analysis.exists_smooth_cutoff_on_nhds
    (isCompact_parabolicClosedBox 1 (1 / 2 : ℝ) (1 / 4 : ℝ) 0) hU
      (reference_closed_collar_subset_unit_box d)
  have he₂ : ContDiff ℝ 2 eta := he.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨M, hM, hbound⟩ := exists_uniform_jet_bound he hec
  let C : ℝ := (1 + 2 + 2 * d + 4 * (d : ℝ)^2) * M
  refine ⟨eta, C, by dsimp [C]; positivity, he, hec, heone, heU, ?_⟩
  intro q hq hv ht hg hh
  let L := fun f => parabolicLpNormOn d f U
  let S := ∑ k, L (parabolicJetComponent q k)
  have hS k : L (parabolicJetComponent q k) ≤ S :=
    Finset.single_le_sum (f := fun k => L (parabolicJetComponent q k))
      (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ k)
  let B (f : TimeVelocity d → ℝ) (r : ℝ) :=
    MemLp f (parabolicExponent d) volume ∧ parabolicLpNorm d f ≤ r * (M * S)
  have addB {f g r s} (hf : B f r) (hg : B g s) : B (f + g) (r + s) :=
    ⟨hf.1.add hg.1, (lpNorm_add_le hf.1 (parabolicExponent_one_le d)).trans (by
      rw [add_mul]; exact add_le_add hf.2 hg.2)⟩
  have mulB (k l : ParabolicJetIndex d) :
      B (parabolicJetComponent eta k * parabolicJetComponent q l) 1 := by
    have ha : Continuous (parabolicJetComponent eta k) := by
      rcases k with (_ | (_ | (i | ⟨i, j⟩)))
      exacts [he.continuous, timeDerivative_continuous he,
        velocityGradient_continuous he, velocityHessian_continuous he]
    have hs : tsupport (parabolicJetComponent eta k) ⊆ U := by
      rcases k with (_ | (_ | (i | ⟨i, j⟩)))
      exacts [heU, (timeDerivative_tsupport eta).trans heU,
        (velocityGradient_tsupport eta).trans heU, (velocityHessian_tsupport eta).trans heU]
    have hf : ParabolicMemLpOn U (parabolicExponent d) (parabolicJetComponent q l) := by
      rcases l with (_ | (_ | (i | ⟨i, j⟩)))
      exacts [hv, ht, hg i, hh i j]
    obtain ⟨hmem, hle⟩ := cutoff_mul_lpNorm_le hU.measurableSet hM.le ha hs (hbound k) hf
    exact ⟨hmem, by simpa only [one_mul] using hle.trans (mul_le_mul_of_nonneg_left (hS l) hM.le)⟩
  let v : ParabolicJetIndex d := .inl ()
  let t : ParabolicJetIndex d := .inr (.inl ())
  let g (i : Fin d) : ParabolicJetIndex d := .inr (.inr (.inl i))
  let h (i j : Fin d) : ParabolicJetIndex d := .inr (.inr (.inr (i,j)))
  have h₀ : B (eta * q) 1 := mulB v v
  have h₁ : B (timeDerivative (eta * q)) (1 + 1) := by
    have e : timeDerivative (eta * q) =
        eta * timeDerivative q + timeDerivative eta * q := by
      funext z
      simp [timeDerivative, fderiv_cutoff_mul hU he₂ heU hq, mul_comm]
    rw [e]
    exact addB (mulB v t) (mulB t v)
  have h₂ (i : Fin d) : B (fun z => velocityGradient (eta * q) z i) (1 + 1) := by
    have e : (fun z => velocityGradient (eta * q) z i) =
        (fun z => eta z * velocityGradient q z i) + (fun z => velocityGradient eta z i * q z) := by
      funext z
      simp [velocityGradient, fderiv_cutoff_mul hU he₂ heU hq, mul_comm]
    rw [e]
    exact addB (mulB v (g i)) (mulB (g i) v)
  have h₃ (i j : Fin d) : B (fun z => velocityHessian (eta * q) z i j) (1 + 1 + 1 + 1) := by
    rw [velocityHessian_cutoff_mul hU he₂ heU hq]
    exact addB (addB (addB (mulB v (h i j)) (mulB (g i) (g j))) (mulB (g j) (g i))) (mulB (h i j) v)
  have hm : ParabolicSmoothJetMemLp d (eta * q) := ⟨h₀.1, h₁.1, fun i => (h₂ i).1, fun i j => (h₃ i j).1⟩
  change parabolicSmoothJetLpNorm d (eta * q) ≤ _
  rw [parabolicSmoothJetLpNorm_eq_components hm, ← sum_parabolicJetComponent L q]
  calc
    _ ≤ 1 * (M * S) + (1 + 1) * (M * S) + (∑ _ : Fin d, (1 + 1) * (M * S)) +
        ∑ _ : Fin d, ∑ _ : Fin d, (1 + 1 + 1 + 1) * (M * S) := by
      exact add_le_add (add_le_add (add_le_add h₀.2 h₁.2)
        (Finset.sum_le_sum fun i _ => (h₂ i).2))
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (h₃ i j).2)
    _ = C * S := by simp [C]; ring

end HypoellipticAleksandrov.Parabolic
