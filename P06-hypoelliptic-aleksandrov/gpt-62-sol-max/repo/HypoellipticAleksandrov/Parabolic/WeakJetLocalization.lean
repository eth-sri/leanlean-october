module

public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization

/-! # Localizing selected weak jets by a single cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {d : ℕ} {b q QW : TimeVelocity d → ℝ} {QG : TimeVelocity d → PDE.Vec d}
  {QH : TimeVelocity d → PDE.Mat d}

/-- On a neighborhood where the cutoff is constant its entire first and second jet vanishes. -/
lemma jet_of_eventuallyEq_const {z : TimeVelocity d} {c : ℝ} (h : b =ᶠ[𝓝 z] fun _ => c) :
    b z = c ∧ timeDerivative b z = 0 ∧ (∀ i, velocityGradient b z i = 0) ∧
      ∀ i j, velocityHessian b z i j = 0 := by
  have h' : fderiv ℝ b =ᶠ[𝓝 z] (0 : TimeVelocity d → TimeVelocity d →L[ℝ] ℝ) :=
    by simpa only [fderiv_fun_const] using h.fderiv (𝕜 := ℝ)
  have h'' : fderiv ℝ (fderiv ℝ b) z = 0 := by rw [h'.fderiv_eq, fderiv_zero, Pi.zero_apply]
  exact ⟨h.self_of_nhds, by simp [timeDerivative, h'.self_of_nhds],
    fun i => by simp [velocityGradient, h'.self_of_nhds], fun i j => by simp [velocityHessian, h'']⟩

private lemma tsupport_subset_of_cutoff {f : TimeVelocity d → ℝ}
    (h : ∀ z, z ∉ tsupport b → f z = 0) : tsupport f ⊆ tsupport b := by
  rw [← (isClosed_tsupport (f := b)).closure_eq]
  exact closure_mono fun z hz => by by_contra hz'; exact hz (h z hz')

lemma localized_jet_tsupport_subset (b q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d) :
    tsupport (localizedScalar b q) ⊆ tsupport b ∧
    tsupport (localizedTimeDeriv b q QW) ⊆ tsupport b ∧
    (∀ j, tsupport (localizedGradient b q QG j) ⊆ tsupport b) ∧
    ∀ j i, tsupport (localizedHessian b q QG QH j i) ⊆ tsupport b := by
  have hz (z : TimeVelocity d) (h : z ∉ tsupport b) :=
    jet_of_eventuallyEq_const (c := (0 : ℝ)) (notMem_tsupport_iff_eventuallyEq.mp h)
  exact ⟨tsupport_mul_subset_left,
    tsupport_subset_of_cutoff fun z h => by
      rcases hz z h with ⟨h₁,h₂,_,_⟩; simp [localizedTimeDeriv, h₁, h₂],
    fun j => tsupport_subset_of_cutoff fun z h => by
      rcases hz z h with ⟨h₁,_,h₃,_⟩; simp [localizedGradient, h₁, h₃],
    fun j i => tsupport_subset_of_cutoff fun z h => by
      rcases hz z h with ⟨h₁,_,h₃,h₄⟩; simp [localizedHessian, h₁, h₃, h₄]⟩

/-- On the open thickening of a plateau the cutoff changes none of the selected jet values. -/
lemma localized_jet_eqOn_plateau {K : Set (TimeVelocity d)} {δ : ℝ}
    (q QW : TimeVelocity d → ℝ) (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hbOne : EqOn b 1 (Metric.cthickening δ K)) :
    let S := Metric.thickening δ K
    EqOn (localizedScalar b q) q S ∧ EqOn (localizedTimeDeriv b q QW) QW S ∧
    (∀ j, EqOn (localizedGradient b q QG j) (fun z => QG z j) S) ∧
    ∀ j i, EqOn (localizedHessian b q QG QH j i) (fun z => QH z j i) S := by
  dsimp only
  have h (z : TimeVelocity d) (hz : z ∈ Metric.thickening δ K) : b =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [Metric.isOpen_thickening.mem_nhds hz] with y hy
    exact hbOne (Metric.thickening_subset_cthickening δ K hy)
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun j z hz => ?_, fun j i z hz => ?_⟩ <;>
    obtain ⟨hv, ht, hg, hh⟩ := jet_of_eventuallyEq_const (h z hz) <;>
    simp [localizedScalar, localizedTimeDeriv, localizedGradient, localizedHessian, hv, ht, hg, hh]

variable {U : Set (TimeVelocity d)}

private lemma globalize_localized_L2 (hU : IsOpen U) (hbSub : tsupport b ⊆ U)
    {f : TimeVelocity d → ℝ} (hf : ParabolicMemLpOn U 2 f) (hs : tsupport f ⊆ tsupport b) :
    MemLp f 2 volume :=
  hf.memLp_of_support_subset hU.measurableSet ((subset_tsupport f).trans (hs.trans hbSub))

/-- Globalization of the first-order spatial jet of a cutoff product. -/
theorem localized_gradient_jet_univ (hU : IsOpen U)
    (hq : ParabolicMemLpOn U 2 q) (hG : ∀ j, ParabolicMemLpOn U 2 (fun z => QG z j))
    (hqG : ∀ j, HasWeakVelocityPartialDerivOn U j q (fun z => QG z j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport b) (hbSub : tsupport b ⊆ U) :
    MemLp (localizedScalar b q) 2 volume ∧ (∀ j, MemLp (localizedGradient b q QG j) 2 volume) ∧
    (∀ j, HasWeakVelocityPartialDerivOn univ j (localizedScalar b q) (localizedGradient b q QG j)) ∧
    tsupport (localizedScalar b q) ⊆ U ∧ ∀ j, tsupport (localizedGradient b q QG j) ⊆ U := by
  obtain ⟨hS, _, hSg, _⟩ := localized_jet_tsupport_subset b q 0 QG 0
  refine ⟨globalize_localized_L2 hU hbSub (hq.mul_continuous_compact hb.continuous hc) hS,
    fun j => globalize_localized_L2 hU hbSub (localizedGradient_memLp hq (hG j) hb hc) (hSg j),
    fun j => ?_, hS.trans hbSub, fun j => (hSg j).trans hbSub⟩
  exact ((hqG j).mul_contDiff hb (hq.locallyIntegrableOn (by norm_num))
    ((hG j).locallyIntegrableOn (by norm_num))).univ_of_tsupport_subset hU
      (hS.trans hbSub) ((hSg j).trans hbSub)

/-- A smooth cutoff supported in the open carrier globalizes the selected spatial weak jet.
The Hessian indices may be restricted, for example to the diagonal. -/
theorem localized_spatial_jet_univ {P : Fin d → Fin d → Prop} (hU : IsOpen U)
    (hq : ParabolicMemLpOn U 2 q) (hG : ∀ j, ParabolicMemLpOn U 2 (fun z => QG z j))
    (hH : ∀ j i, P j i → ParabolicMemLpOn U 2 (fun z => QH z j i))
    (hqG : ∀ j, HasWeakVelocityPartialDerivOn U j q (fun z => QG z j))
    (hGH : ∀ j i, P j i → HasWeakVelocityPartialDerivOn U i (fun z => QG z j) (fun z => QH z j i))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport b) (hbSub : tsupport b ⊆ U) :
    (∀ j, HasWeakVelocityPartialDerivOn univ j (localizedScalar b q) (localizedGradient b q QG j)) ∧
    (∀ j i, P j i → HasWeakVelocityPartialDerivOn univ i
      (localizedGradient b q QG j) (localizedHessian b q QG QH j i)) ∧
    MemLp (localizedScalar b q) 2 volume ∧ (∀ j, MemLp (localizedGradient b q QG j) 2 volume) ∧
    ∀ j i, P j i → MemLp (localizedHessian b q QG QH j i) 2 volume := by
  obtain ⟨hR, hG', hqG', _, hSg⟩ := localized_gradient_jet_univ hU hq hG hqG hb hc hbSub
  obtain ⟨_, _, _, hSh⟩ := localized_jet_tsupport_subset b q 0 QG QH
  have h₂ j i hij := localizedHessian_memLp_hasWeakDeriv (by norm_num) hq (hG j) (hG i) (hH j i hij)
    (hqG i) (hGH j i hij) hb hc
  exact ⟨hqG', fun j i hij => (h₂ j i hij).2.univ_of_tsupport_subset hU (hSg j) ((hSh j i).trans hbSub),
    hR, hG', fun j i hij => globalize_localized_L2 hU hbSub (h₂ j i hij).1 (hSh j i)⟩

/-- Globalization for the time component of a selected weak jet. -/
theorem localized_time_jet_univ (hU : IsOpen U) (hq : ParabolicMemLpOn U 2 q)
    (hW : ParabolicMemLpOn U 2 QW) (hqW : HasWeakTimeDerivOn U q QW)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport b) (hbSub : tsupport b ⊆ U) :
    HasWeakTimeDerivOn univ (localizedScalar b q) (localizedTimeDeriv b q QW) ∧
      MemLp (localizedTimeDeriv b q QW) 2 volume := by
  obtain ⟨hS, hSt, _, _⟩ := localized_jet_tsupport_subset b q QW 0 0
  exact ⟨(hqW.mul_contDiff hb (hq.locallyIntegrableOn (by norm_num)) (hW.locallyIntegrableOn (by norm_num)))
    |>.univ_of_tsupport_subset hU (hS.trans hbSub) (hSt.trans hbSub),
    globalize_localized_L2 hU hbSub (localizedTimeDeriv_memLp hq hW hb hc) hSt⟩

end HypoellipticAleksandrov.Parabolic
