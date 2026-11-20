module

public import PottsDiscontinuity.SixVertex.Cor34PerronBranch

/-! Identification of the Bethe eigenvalue with the Perron root by analytic continuation. -/

@[expose] public section

open Filter Topology Matrix Set Finset
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

open Bethe BetheAnsatz

private theorem physical_c {d : ℝ} (hd : d < -1) :
    2 < Real.sqrt (2 - 2 * d) ∧ anisotropy (Real.sqrt (2 - 2 * d)) = d := by
  grind [anisotropy, Real.lt_sqrt]

@[local fun_prop] private theorem analyticAt_ofReal {f : ℝ → ℝ} {d : ℝ}
    (hf : AnalyticAt ℝ f d) : AnalyticAt ℝ (fun t => (f t : ℂ)) d :=
  (Complex.ofRealCLM.analyticAt (f d)).comp hf

private theorem analyticAt_theta_deriv {y : ℝ → ℝ} {d : ℝ} (hd : d < -1)
    (hy : AnalyticAt ℝ y d) : AnalyticAt ℝ (fun t => deriv (fun x => theta t x (y t)) 0) d := by
  let F (q : ℝ × ℝ × ℝ) := theta q.1 q.2.1 q.2.2
  let v : ℝ × ℝ × ℝ := (0, 1, 0)
  let E := ContinuousLinearMap.apply ℝ ℝ v
  let f (t : ℝ) : ℝ × ℝ × ℝ := (t, 0, y t)
  have hf : AnalyticAt ℝ f d := by fun_prop
  have hF : AnalyticAt ℝ F (f d) := analyticAt_theta hd 0 (y d)
  refine ((E.analyticAt _).comp (hF.fderiv.comp hf)).congr ?_
  filter_upwards [Iio_mem_nhds hd] with t ht
  have h₁ := (analyticAt_theta ht 0 (y t)).differentiableAt.hasFDerivAt
  have h₂ : HasDerivAt (fun x : ℝ => (t, x, y t)) v 0 := by
    simpa [v] using (hasDerivAt_const (0 : ℝ) t).prodMk
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (y t)))
  exact (h₁.comp_hasDerivAt 0 h₂).deriv.symm

private theorem analyticAt_parityEigenvalue {N n : ℕ} {p : ℝ → Fin n → ℝ} {d : ℝ}
    (hd : d < -1) (hp : AnalyticAt ℝ p d) (hS : p d ∈ S_n n) :
    AnalyticAt ℝ (fun t => parityEigenvalue N (Real.sqrt (2 - 2 * t)) (p t)) d := by
  classical
  have hcoord (j : Fin n) : AnalyticAt ℝ (fun t => p t j) d :=
    ((ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt (p d)).comp hp
  let c (t : ℝ) := Real.sqrt (2 - 2 * t)
  have hc : AnalyticAt ℝ (fun t => (c t : ℂ) ^ 2) d := by
    refine (show AnalyticAt ℝ (fun t : ℝ => (2 - 2 * (t : ℂ))) d by fun_prop).congr ?_
    filter_upwards [Iio_mem_nhds hd] with t (ht : t < -1)
    have h : c t ^ 2 = 2 - 2 * t := Real.sq_sqrt (by linarith)
    exact_mod_cast h.symm
  have hz (j : Fin n) : AnalyticAt ℝ (fun t => z (p t j)) d := by
    unfold z
    exact analyticAt_cexp.restrictScalars.comp (by fun_prop :
      AnalyticAt ℝ (fun t => Complex.I * (p t j : ℂ)) d)
  have hL (j : Fin n) (hj : p d j ≠ 0) : AnalyticAt ℝ (fun t => L (c t) (z (p t j))) d := by
    have := sub_ne_zero.mpr (z_ne_one (hS.1 j) hj).symm
    unfold L
    fun_prop
  have hM (j : Fin n) (hj : p d j ≠ 0) : AnalyticAt ℝ (fun t => M (c t) (z (p t j))) d := by
    have := sub_ne_zero.mpr (z_ne_one (hS.1 j) hj).symm
    unfold M
    fun_prop
  unfold parityEigenvalue
  by_cases he : Even n
  · simp only [dite_eq_left he, eigenvalueRegular]
    have h := cor34_even_S_n_roots_nonzero hS he
    exact (univ.analyticAt_fun_prod fun j _ => hL j (h j)).add
      (univ.analyticAt_fun_prod fun j _ => hM j (h j))
  · let l := oddCenter he
    have hz0 : p d l = 0 :=
      cor34_odd_S_n_center_zero (q := n / 2 + 1) hS (by rw [Nat.even_iff] at he; omega)
    have hprod : AnalyticAt ℝ (fun t => ∏ j ∈ univ.erase l, M (c t) (z (p t j))) d :=
      (univ.erase l).analyticAt_fun_prod fun j hj => hM j fun h0 =>
        (ne_of_mem_erase hj) (hS.2.1.injective (h0.trans hz0.symm))
    have hderiv (j : Fin n) : AnalyticAt ℝ
        (fun t => (deriv (fun x => theta (anisotropy (c t)) x (p t j)) 0 : ℂ)) d := by
      refine (analyticAt_ofReal (analyticAt_theta_deriv hd (hcoord j))).congr ?_
      filter_upwards [Iio_mem_nhds hd] with t ht
      rw [(physical_c ht).2]
      exact (analyticAt_theta_left ht 0 (p t j)).differentiableAt.hasDerivAt.ofReal_comp.deriv.symm
    have hsum : AnalyticAt ℝ (fun t => ∑ j ∈ univ.erase l,
        (deriv (fun x => theta (anisotropy (c t)) x (p t j)) 0 : ℂ)) d :=
      (univ.erase l).analyticAt_fun_sum fun j _ => hderiv j
    simp only [dite_eq_right he, eigenvalueZero]
    exact (((analyticAt_const.add (hc.mul analyticAt_const)).add (hc.mul hsum)).mul hprod)

/-- Corollary 3.4 at the endpoint of the analytic Bethe family, in both parities. -/
theorem cor34_final_at_endpoint {N n : ℕ} {d₀ d₁ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hd₀₁ : d₀ < d₁) (ha : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ S_n n)
    (hb : ∀ d ≤ d₀, DiscreteBetheEquation d N n (p d))
    (hform : ∀ d ≤ d₀, p d = P (1 / d)) (hP : ContinuousAt P 0)
    (hP₀ : P 0 = discreteBaseSolution N n) (hn : 0 < n) (hN : 2 * n ≤ N) :
    parityEigenvalue N (Real.sqrt (2 - 2 * d₀)) (p d₀) =
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) : ℂ) := by
  let f (d : ℝ) : ℂ := pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)
  let g (d : ℝ) : ℂ := parityEigenvalue N (Real.sqrt (2 - 2 * d)) (p d)
  have ht : ∀ᶠ ε in 𝓝[<] (0 : ℝ), 1 / ε ≤ d₀ := by
    simpa using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  have he := cor34_eventually_perron hn hN hP hP₀
    (μ := fun ε => parityEigenvalue N (Real.sqrt (2 - 2 / ε)) (P ε)) (by
      filter_upwards [ht] with ε hε
      have hd := hε.trans_lt hd₀
      have h := cor34_parity_block_eigen (physical_c hd).1 (physical_c hd).2 _
        (hp _ hε) (hb _ hε)
      rw [hform _ hε] at h
      simpa only [div_eq_mul_inv, one_mul, inv_inv] using h)
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] (0 : ℝ)) := by
    simpa using tendsto_inv_atBot_nhdsLT_zero
  obtain ⟨b, hbelow⟩ := eventually_atBot.mp (hinv.eventually he)
  have hf (d : ℝ) (hd : d ≤ d₀) : AnalyticAt ℝ f d :=
    analyticAt_ofReal (cor34_analyticAt_pfRoot_transferBlock (by omega) (hd.trans_lt hd₀))
  have hg (d : ℝ) (hd : d ≤ d₀) : AnalyticAt ℝ g d :=
    analyticAt_parityEigenvalue (hd.trans_lt hd₀) (ha d (hd.trans_lt hd₀₁)) (hp d hd)
  obtain ⟨a, ha'⟩ := exists_lt (min b d₀)
  have heq : g =ᶠ[𝓝 a] f := by
    filter_upwards [Iio_mem_nhds ha'] with d hd
    have hd' := hd.le.trans (min_le_right b d₀)
    simpa [g, hform d hd'] using hbelow d (hd.le.trans (min_le_left b d₀))
  have hag : AnalyticOnNhd ℝ g (Iio d₀) := fun d hd => hg d hd.le
  have haf : AnalyticOnNhd ℝ f (Iio d₀) := fun d hd => hf d hd.le
  have hEq := hag.eqOn_of_preconnected_of_eventuallyEq haf isPreconnected_Iio
    (ha'.trans_le (min_le_right b d₀)) heq
  have hNear : g =ᶠ[𝓝[<] d₀] f := by
    filter_upwards [self_mem_nhdsWithin] with d hd using hEq hd
  exact tendsto_nhds_unique ((hg d₀ le_rfl).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (((hf d₀ le_rfl).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hNear.symm)

end PottsDiscontinuity.SixVertex
