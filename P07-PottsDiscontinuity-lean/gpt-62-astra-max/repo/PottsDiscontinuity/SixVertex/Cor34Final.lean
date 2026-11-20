module
public import PottsDiscontinuity.SixVertex.Cor34FinalAnalytic
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen
public import PottsDiscontinuity.SixVertex.WaveSelection

/-! Identify the Bethe eigenvalue for either root parity. Pairing with the
positive Perron vector gives equality on a negative tail. Both physical
expressions are analytic on the connected parameter interval, so equality
persists up to its endpoint. -/
@[expose] public section
open Set Filter Topology Matrix
namespace PottsDiscontinuity.SixVertex
open PerronFrobenius BetheAnsatz

theorem physical_endpoint {N n : ℕ} {d₀ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hn : 0 < n) (hbound : 2*n ≤ N)
    (hP : ContinuousAt P 0) (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hformula : ∀ d ≤ d₀, p d = P (1 / d)) (E : ℝ → ℂ)
    (hE : AnalyticOnNhd ℝ E (Iic d₀)) (he : ∀ d ≤ d₀,
      (transferBlock N (rowParameter d) n).map (algebraMap ℝ ℂ) *ᵥ blockWave d (p d) = E d • blockWave d (p d)) :
    (pfRoot (transferBlock N (rowParameter d₀) n) : ℂ) = E d₀ := by
  have hε : ∀ᶠ ε in 𝓝[<] (0:ℝ), 1/ε ≤ d₀ := by simpa only [one_div] using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  have h := select_physical_branch hn hbound hP hP0 (μ := fun ε => E (1/ε)) (by
    filter_upwards [hε] with ε hε
    have he' := he _ hε
    rw [hformula _ hε] at he'
    simpa [rowParameter,div_eq_mul_inv] using he')
  have inv : Tendsto (fun d : ℝ => 1/d) atBot (𝓝[<] 0) := by simpa only [one_div] using tendsto_inv_atBot_nhdsLT_zero
  obtain ⟨b,hb⟩ := eventually_atBot.mp (inv.eventually h)
  let f (d : ℝ) : ℂ := pfRoot (transferBlock N (rowParameter d) n)
  have hf : AnalyticOnNhd ℝ f (Iic d₀) := fun d hd => analytic_complex_cast (cor34_analyticAt_pfRoot_transferBlock (by omega) (hd.trans_lt hd₀))
  let a := min b d₀-1
  have ha : a < min b d₀ := by dsimp [a]; linarith
  have hh : f =ᶠ[𝓝 a] E := by
    filter_upwards [gt_mem_nhds ha] with t ht
    simpa [f,rowParameter,div_div_eq_mul_div] using (hb t (ht.le.trans (min_le_left _ _))).symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hE isPreconnected_Iic (ha.le.trans (min_le_right _ _)) hh (le_rfl)
end PottsDiscontinuity.SixVertex
