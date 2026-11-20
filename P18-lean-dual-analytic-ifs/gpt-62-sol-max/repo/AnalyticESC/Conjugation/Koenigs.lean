module

public import AnalyticESC.Dual.Projection

@[expose] public section

/-! Linearizing coordinates are obtained by integrating the exponential of a primitive
of the nonlinearity. -/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The fixed-point equation for the dual operator of one map. -/
def IsDualFixed (f : ℂ → ℂ) (G : ℝ → ℂ) : Prop :=
  ∀ x ∈ I, G x = deriv (deriv f) x / deriv f x + deriv f x * G (f x).re

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem dualProj_const_fixed (i : Fin N) :
    IsDualFixed (Φ.f i) (fun x => Φ.dualProj (.inf fun _ => i) x) := by
  intro x hx
  dsimp only
  conv_lhs => rw [Φ.dualProj_inf_head _ (Φ.real_mem_closed hx), nonlin]
  exact congrArg (fun z => _ + deriv (Φ.f i) x * Φ.dualProj (.inf fun _ => i) z) (Φ.comp_ofReal [i] hx)

/-- Uniform contraction of the cocycle identifies any continuous common solution with every
infinite dual projection. -/
theorem eq_dualProj_of_cocycle {G : ℝ → ℂ} (hG : ContinuousOn G I) (w : ℕ → Fin N)
    (hcoc : ∀ k, IsDualFixed (Φ.f (w k)) G) : ∀ x ∈ I, G x = Φ.dualProj (.inf w) x := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  have h (n : ℕ) (w : ℕ → Fin N) (hcoc : ∀ k, IsDualFixed (Φ.f (w k)) G) (x : ℝ) (hx : x ∈ I) :
      ‖G x - Φ.dualProj (.inf w) x‖ ≤ Φ.cmax ^ n * (B + M) := by
    induction n generalizing w x with
    | zero =>
      simpa using (norm_sub_le _ _).trans (add_le_add (hB x hx)
        (hM _ _ (Φ.real_mem_closed hx)))
    | succ n ih =>
      have hz := Φ.real_mem_closed hx
      have he : Φ.f (w 0) x = ((Φ.f (w 0) x).re : ℂ) := Φ.comp_ofReal [w 0] hx
      rw [hcoc 0 x hx, Φ.dualProj_inf_head w hz, nonlin, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ',
        mul_assoc, congrArg (Φ.dualProj (.inf fun k => w (k + 1))) he]
      exact mul_le_mul (Φ.norm_deriv_le_cmax _ hz) (ih _ (fun k => hcoc (k + 1)) _ ((Φ.inClass _).re_mem_I x hx))
        (norm_nonneg _) Φ.cmax_nonneg
  intro x hx
  have ht : Tendsto (fun n => Φ.cmax ^ n * (B + M)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_const (B + M)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' ht fun n => h n w hcoc x hx))

end IFS

variable {ε : ℝ}

theorem eq_of_hasDerivAt_zero_I {u : ℝ → ℝ}
    (hu : ∀ x ∈ I, HasDerivAt u 0 x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : u x = u y := by
  apply sub_eq_zero.1 ∘ norm_le_zero_iff.1
  simpa using (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => le_rfl) hy hx

noncomputable def logDeriv (φ : ℝ → ℝ) (x : ℝ) : ℝ := deriv (deriv φ) x / deriv φ x

private theorem exists_primitive {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (nbhd ε)) :
    ∃ P, ∀ z ∈ nbhd ε, HasDerivAt P (H z) z := by
  obtain ⟨P, hP⟩ := (convex_nbhd ε).exists_forall_hasDerivWithinAt hH
  exact ⟨P, fun z hz => (hP z hz).hasDerivAt (nbhd_mem_nhds hz)⟩

open scoped ComplexConjugate in
/-- Symmetrize a primitive of `H` before exponentiating, so the derivative of the
coordinate on the interval is the positive real function `exp (Re P)`. -/
theorem exists_coord_of_logDeriv (hε : 0 < ε) {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (nbhd ε)) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧ ∀ x ∈ I, logDeriv g x = (H x).re := by
  obtain ⟨P, hP⟩ := exists_primitive hH
  let E (z : ℂ) := Complex.exp ((P z + conj (P (conj z))) / 2)
  have hconj {z : ℂ} (hz : z ∈ nbhd ε) : conj z ∈ nbhd ε := by
    obtain ⟨x, hx, h⟩ := hz
    refine ⟨x, hx, ?_⟩
    rwa [← Complex.conj_ofReal x, ← map_sub, Complex.norm_conj]
  have hE : DifferentiableOn ℂ E (nbhd ε) := by
    intro z hz
    have h : DifferentiableAt ℂ (conj ∘ P ∘ conj) z := by
      simpa using (hP _ (hconj hz)).differentiableAt.conj_conj
    exact ((((hP z hz).differentiableAt.add h).div_const 2).cexp).differentiableWithinAt
  obtain ⟨G, hG⟩ := exists_primitive hE
  let g (x : ℝ) := (G x).re
  have hGd : DifferentiableOn ℂ G (nbhd ε) := fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  have hga : AnalyticOnNhd ℝ g I := fun x hx => (hGd.analyticAt_nbhd (ofReal_mem_nbhd hε hx)).re_ofReal
  have hg (x : ℝ) (hx : (x : ℂ) ∈ nbhd ε) : HasDerivAt g (Real.exp (P x).re) x := by
    have he : (E x).re = Real.exp (P x).re := by
      dsimp only [E]
      rw [Complex.conj_ofReal, Complex.add_conj]
      aesop
    exact he ▸ (hG x hx).real_of_complex
  have hpos (x : ℝ) (hx : x ∈ I)  :=
    (hg x (ofReal_mem_nbhd hε hx)).deriv.symm ▸ Real.exp_pos _
  refine ⟨g, ⟨hga, (strictMonoOn_of_deriv_pos (convex_Icc 0 1) hga.continuousOn
    fun x hx => hpos x (interior_subset hx)).injOn⟩, fun x hx => (hpos x hx).ne', ?_⟩
  intro x hx
  have hn := ofReal_mem_nbhd hε hx
  rw [logDeriv, (eventuallyEq_of_mem (real_mem_nhds (isOpen_nbhd ε) hn) fun y hy => (hg y hy).deriv).deriv_eq, (hP x hn).real_of_complex.exp.deriv, (hg x hn).deriv]
  simp

end AnalyticESC
