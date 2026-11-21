module

public import DedekindZetaZeroFree.Analysis.Calculus.DominatedJets

public import DedekindZetaZeroFree.Analysis.RightFrame.PullbackWords
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.RightFrame.CauchyCoefficient

open PullbackWords

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : Type*}

def cauchyCoefficient (h : ℂ → E → ℂ) (s₀ : ℂ) (r : ℝ) (k : ℕ) : E → ℂ :=
  fun x => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun z => (z - s₀) ^ (-((k : ℤ) + 1)) * h z x) s₀ r

section

open Filter MeasureTheory
open scoped Topology ContDiff BigOperators

variable [FiniteDimensional ℝ E]

private theorem cm_cont {X : Type*} [TopologicalSpace X] (n : ℕ)
    (F : X → E [×n]→L[ℝ] ℂ) (S : Set X)
    (h : ∀ m, ContinuousOn (fun x => F x m) S) : ContinuousOn F S := by
  induction n with
  | zero =>
    have hh := (continuousMultilinearCurryFin0 ℝ E ℂ).symm.continuous.comp_continuousOn
      (h 0)
    simpa only [Function.comp_def, ← continuousMultilinearCurryFin0_apply,
      LinearIsometryEquiv.symm_apply_apply] using hh
  | succ n ih =>
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) ℂ
    have hh : ContinuousOn (fun x => L (F x)) S := by
      apply continuousOn_clm_apply.mpr
      intro v
      apply ih
      intro m
      exact h (Fin.cons v m)
    simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using
      L.symm.continuous.comp_continuousOn hh

private theorem jet_word (n : ℕ) (u : E → ℂ) (U : Set E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (x : E) (hx : x ∈ U) (m : Fin n → E) :
    iteratedFDeriv ℝ n u x m = constantDirectionWord (List.ofFn m) u x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y (Fin.tail m)) =ᶠ[𝓝 x]
        constantDirectionWord (List.ofFn (Fin.tail m)) u :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, constantDirectionWord, directionalWord]
    rfl

private theorem jet_joint {B : Type*} [Fintype B]
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (D : Set ℂ) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ D, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (D ×ˢ K))
    (n : ℕ) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) :
    ContinuousOn (fun p : ℂ × E => iteratedFDeriv ℝ n (h p.1) p.2) (D ×ˢ K) := by
  apply cm_cont
  intro m
  obtain ⟨N,c,w,hc,_,heq⟩ := transport U U hU hU fields hfields hframe
    id contDiffOn_id (fun _ hx => hx) (List.ofFn m)
  have hsum : ContinuousOn (fun p : ℂ × E =>
      ∑ i : Fin N, c i p.2 • directionalWord fields (w i) (h p.1) p.2) (D ×ˢ K) := by
    apply continuousOn_finset_sum
    intro i _
    exact ((hc i).continuousOn.comp continuous_snd.continuousOn
      (fun p hp => hKU hp.2)).smul (hj (w i) K hK hKU)
  apply hsum.congr
  intro p hp
  dsimp only
  rw [jet_word n (h p.1) U hU (hsp p.1 hp.1) p.2 (hKU hp.2) m]
  simpa [Function.comp_def] using (heq (h p.1) (hsp p.1 hp.1) p.2 (hKU hp.2))

private theorem word_smooth {B : Type*} (U : Set E) (hU : IsOpen U)
    (fields : B → E → E) (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : List B) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)

private theorem integral_core {B : Type*} [Fintype B]
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (D : Set ℂ) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ D, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (D ×ˢ K))
    (q : ℝ → ℂ) (hq : Continuous q) (hqD : ∀ t, q t ∈ D)
    (a : ℝ → ℂ) (ha : Continuous a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ∫ t, a t * h (q t) x ∂volume.restrict (Set.Ioc 0 (2*Real.pi))) U ∧
    ∀ x ∈ U, ∀ v : E,
      fderiv ℝ (fun y => ∫ t, a t * h (q t) y ∂volume.restrict (Set.Ioc 0 (2*Real.pi))) x v =
        ∫ t, a t * fderiv ℝ (h (q t)) x v ∂volume.restrict (Set.Ioc 0 (2*Real.pi)) := by
  let μ := volume.restrict (Set.Ioc 0 (2*Real.pi))
  let F : E → ℝ → ℂ := fun x t => a t * h (q t) x
  let J (n : ℕ) (p : ℝ × E) := iteratedFDerivWithin ℝ n (fun x => F x p.1) U p.2
  have hsm (t : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => F x t) U :=
    contDiffOn_const.mul (hsp _ (hqD t))
  have hJ (n : ℕ) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) :
      ContinuousOn (J n) (Set.univ ×ˢ K) := by
    have hbase := jet_joint U hU fields hfields hframe D h hsp hj n K hK hKU
    have hcomp : ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ n (h (q p.1)) p.2)
        (Set.univ ×ˢ K) := hbase.comp ((hq.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hqD _, hp.2⟩)
    have hprod := ((ha.comp continuous_fst).continuousOn).smul hcomp
    apply hprod.congr
    intro p hp
    dsimp [J, F]
    change iteratedFDerivWithin ℝ n (a p.1 • h (q p.1)) U p.2 = _
    rw [iteratedFDerivWithin_const_smul_apply
      (((hsp _ (hqD p.1)) p.2 (hKU hp.2)).of_le (by simp)) hU.uniqueDiffOn (hKU hp.2),
      iteratedFDerivWithin_of_isOpen n hU (hKU hp.2)]

  have hm (n : ℕ) (x : E) (hx : x ∈ U) : AEStronglyMeasurable (fun t => J n (t,x)) μ := by
    have hc : ContinuousOn (fun t => J n (t,x)) Set.univ := (hJ n {x} (isCompact_singleton : IsCompact {x}) (Set.singleton_subset_iff.mpr hx)).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t _ => ⟨Set.mem_univ t, Set.mem_singleton x⟩)
    exact (hc.mono (Set.subset_univ _)).aestronglyMeasurable measurableSet_Ioc
  have hb (n : ℕ) (x : E) (hx : x ∈ U) : ∃ s b,
      s ∈ nhds x ∧ s ⊆ U ∧ Integrable b μ ∧
      ∀ᵐ t ∂μ, ∀ v ∈ s, ‖J n (t,v)‖ ≤ b t := by
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU x hx
    let K := Metric.closedBall x (ε/2)
    have hKU : K ⊆ U := fun v hv => hεU (lt_of_le_of_lt (show dist v x ≤ ε/2 from hv) (by linarith))
    obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc 0 (2*Real.pi))).prod
      (isCompact_closedBall x (ε/2))).exists_bound_of_continuousOn
      ((hJ n K (isCompact_closedBall _ _) hKU).mono
        (Set.prod_mono (Set.subset_univ _) (Set.Subset.refl K)))
    refine ⟨K, (fun _ => C), Metric.closedBall_mem_nhds _ (by linarith), hKU,
      integrable_const C, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro v hv
    exact hC (t,v) ⟨⟨ht.1.le, ht.2⟩, hv⟩
  have result := integral_contDiffOn_of_locally_dominated_jets
    μ F U hU hsm hm hb
  refine ⟨result.1, ?_⟩
  intro x hx v
  have hint : Integrable (fun t => J 1 (t,x)) μ := by
    obtain ⟨s,b,hs,_,hib,hbd⟩ := hb 1 x hx
    exact hib.mono' (hm 1 x hx) (hbd.mono fun t ht => ht x (mem_of_mem_nhds hs))
  have heq := congrArg (fun L : E [×1]→L[ℝ] ℂ => L (fun _ => v)) (result.2 1 x hx)
  rw [ContinuousMultilinearMap.integral_apply hint] at heq
  change (iteratedFDerivWithin ℝ 1 (fun y => ∫ t, F y t ∂μ) U x) (fun _ => v) =
    ∫ t, (iteratedFDerivWithin ℝ 1 (fun y => F y t) U x) (fun _ => v) ∂μ at heq
  simp only [iteratedFDerivWithin_one_apply (hU.uniqueDiffOn (𝕜 := ℝ) x hx)] at heq
  rw [fderivWithin_of_isOpen hU hx] at heq
  refine heq.trans ?_
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]
  dsimp [F]
  rw [fderiv_const_mul (((hsp _ (hqD t)) x hx).contDiffAt (hU.mem_nhds hx)
    |>.differentiableAt (by simp))]
  rfl

private theorem coeff_integral (h : ℂ → E → ℂ) (s₀ : ℂ) (r : ℝ) (k : ℕ) :
    cauchyCoefficient h s₀ r k = fun x =>
      ∫ t, ((2*(Real.pi:ℂ)*Complex.I)⁻¹ * deriv (circleMap s₀ r) t *
        (circleMap s₀ r t - s₀)^(-((k:ℤ)+1))) * h (circleMap s₀ r t) x
        ∂volume.restrict (Set.Ioc 0 (2*Real.pi)) := by
  funext x
  rw [cauchyCoefficient, circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ← integral_const_mul]
  congr 1
  funext t
  simp only [smul_eq_mul]
  ring

private theorem coeff_core {B : Type*} [Fintype B]
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (s₀ : ℂ) (r : ℝ) (hr : 0 < r) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ Metric.closedBall s₀ r, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2)
        (Metric.closedBall s₀ r ×ˢ K)) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cauchyCoefficient h s₀ r k) U ∧
    ∀ x ∈ U, ∀ b, fderiv ℝ (cauchyCoefficient h s₀ r k) x (fields b x) =
      cauchyCoefficient (fun z => directionalWord fields [b] (h z)) s₀ r k x := by
  have hd : Continuous (deriv (circleMap s₀ r)) := by
    change Continuous (fun t => deriv (circleMap s₀ r) t)
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hn (t : ℝ) : circleMap s₀ r t - s₀ ≠ 0 := by
    exact sub_ne_zero.mpr (circleMap_ne_mem_ball (Metric.mem_ball_self hr) t)
  have ha : Continuous (fun t : ℝ =>
      (2*(Real.pi:ℂ)*Complex.I)⁻¹ * deriv (circleMap s₀ r) t *
        (circleMap s₀ r t - s₀)^(-((k:ℤ)+1))) :=
    (continuous_const.mul hd).mul
      (((continuous_circleMap s₀ r).sub continuous_const).zpow₀ _ (fun t => Or.inl (hn t)))
  have hc := integral_core U hU fields hfields hframe (Metric.closedBall s₀ r) h hsp hj
    (circleMap s₀ r) (continuous_circleMap s₀ r) (circleMap_mem_closedBall s₀ hr.le)
    _ ha
  rw [coeff_integral]
  refine ⟨hc.1, ?_⟩
  intro x hx b
  rw [hc.2 x hx (fields b x), coeff_integral]
  rfl

private theorem word_append {B : Type*} (fields : B → E → E) (v w : List B) (u : E → ℂ) :
    directionalWord fields v (directionalWord fields w u) = directionalWord fields (v++w) u := by
  induction v with
  | nil => rfl
  | cons b v ih => simp only [List.cons_append, directionalWord, ih]

private theorem commute_core {B : Type*} [Fintype B]
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (s₀ : ℂ) (r : ℝ) (hr : 0 < r) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ Metric.closedBall s₀ r, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2)
        (Metric.closedBall s₀ r ×ˢ K)) (k : ℕ) (w : List B) :
    ∀ x ∈ U, directionalWord fields w (cauchyCoefficient h s₀ r k) x =
      cauchyCoefficient (fun z => directionalWord fields w (h z)) s₀ r k x := by
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    have heq : directionalWord fields w (cauchyCoefficient h s₀ r k) =ᶠ[𝓝 x]
        cauchyCoefficient (fun z => directionalWord fields w (h z)) s₀ r k :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy
    have hh := coeff_core U hU fields hfields hframe s₀ r hr
      (fun z => directionalWord fields w (h z))
      (fun z hz => word_smooth U hU fields hfields (h z) (hsp z hz) w)
      (fun v K hK hKU => by simpa only [word_append] using hj (v++w) K hK hKU) k
    dsimp only [directionalWord]
    rw [heq.fderiv_eq, hh.2 x hx b]
    rfl

end

theorem coefficient_smooth [FiniteDimensional ℝ E] [Fintype B]
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (h : ℂ → E → ℂ)
    (s₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hdisk : Metric.closedBall s₀ r ⊆ Ω)
    (hspatial : ∀ z ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hjoint : ∀ (w : List B) (K : Set E), IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2)
        (Metric.closedBall s₀ r ×ˢ K))
    (hholomorphic : ∀ x ∈ U, DifferentiableOn ℂ (fun z => h z x) Ω)
    (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cauchyCoefficient h s₀ r k) U := by
  exact (coeff_core U hU fields hfields hframe s₀ r hr h
    (fun z hz => hspatial z (hdisk hz)) hjoint k).1

theorem word_commute [FiniteDimensional ℝ E] [Fintype B]
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (h : ℂ → E → ℂ)
    (s₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hdisk : Metric.closedBall s₀ r ⊆ Ω)
    (hspatial : ∀ z ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hjoint : ∀ (v : List B) (K : Set E), IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields v (h p.1) p.2)
        (Metric.closedBall s₀ r ×ˢ K))
    (hholomorphic : ∀ x ∈ U, DifferentiableOn ℂ (fun z => h z x) Ω)
    (k : ℕ) (w : List B) :
    ∀ x ∈ U, directionalWord fields w (cauchyCoefficient h s₀ r k) x =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral
          (fun z => (z - s₀) ^ (-((k : ℤ) + 1)) * directionalWord fields w (h z) x)
          s₀ r := by
  exact commute_core U hU fields hfields hframe s₀ r hr h
    (fun z hz => hspatial z (hdisk hz)) hjoint k w

end DedekindZetaZeroFree.RightFrame.CauchyCoefficient

end
