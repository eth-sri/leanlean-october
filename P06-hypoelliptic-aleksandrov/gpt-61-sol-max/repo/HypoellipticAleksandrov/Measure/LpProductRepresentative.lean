module

public import HypoellipticAleksandrov.Measure.LpProductSimple
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
Quotient-safe raw representatives for nested product `L²` functions.

The construction approximates an outer `Lp` element by finite-range simple
functions, lifts those representatives to the product, and identifies their
limit slice-by-slice through convergence in measure.
-/

 public section

open Filter Topology
open scoped ENNReal MeasureTheory

namespace HypoellipticAleksandrov

open MeasureTheory

noncomputable section

variable {α β : Type*}

private theorem exists_outer_simple_sequence
     [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (q : Lp (Lp ℝ (2 ) ν) (2 ) μ) :
    ∃ S : ℕ → Lp.simpleFunc (Lp ℝ (2 ) ν) (2 ) μ,
      Tendsto (fun n => (S n : Lp (Lp ℝ (2 ) ν) (2 ) μ))
        atTop (𝓝 q) := by


  rcases mem_closure_iff_seq_limit.mp (Lp.simpleFunc.denseRange (E := Lp ℝ (2 ) ν) (μ := μ) (by norm_num) q) with ⟨u, hu, hlim⟩
  choose S hS using hu
  refine ⟨S, ?_⟩
  convert hlim using 1
  funext n
  exact hS n

private theorem exists_product_simple_limit
     [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (q : Lp (Lp ℝ (2 ) ν) (2 ) μ) :
    ∃ (S : ℕ → Lp.simpleFunc (Lp ℝ (2 ) ν) (2 ) μ)
      (pQ : Lp ℝ (2 ) (μ.prod ν)),
      Tendsto (fun n => (S n : Lp (Lp ℝ (2 ) ν) (2 ) μ))
        atTop (𝓝 q) ∧
      Tendsto (fun n =>
        (memLp_simpleUncurry_two μ ν _
          (Lp.simpleFunc.memLp (S n))).toLp
            (simpleUncurry (Lp.simpleFunc.toSimpleFunc (S n)))) atTop (𝓝 pQ) := by
  let sharedTerm_49cddbdde4 := (Lp (Lp ℝ (2 ) ν) (2 ) μ)
  let sharedTerm_1c5d85a2c0 := ((Lp ℝ (2 ) ν))
  obtain ⟨S, hS⟩ := exists_outer_simple_sequence μ ν q
  let P  := fun n =>
    (memLp_simpleUncurry_two μ ν _
      (Lp.simpleFunc.memLp (S n))).toLp
        (simpleUncurry (Lp.simpleFunc.toSimpleFunc (S n)))
  have hdist (m n : ℕ) :
      dist (P m) (P n) =
        dist ((S m : sharedTerm_49cddbdde4))
          ((S n : sharedTerm_49cddbdde4)) := by
    simp only [P, dist_eq_norm]
    rw [norm_sub_simpleUncurry_toLp_eq]
    change ‖(Lp.simpleFunc.memLp (S m)).toLp (Lp.simpleFunc.toSimpleFunc (S m)) -
        (Lp.simpleFunc.memLp (S n)).toLp (Lp.simpleFunc.toSimpleFunc (S n))‖ =
      ‖(S m : sharedTerm_49cddbdde4) -
        (S n : sharedTerm_49cddbdde4)‖
    have hm : (Lp.simpleFunc.memLp (S m)).toLp
        (Lp.simpleFunc.toSimpleFunc (S m)) =
        (S m : sharedTerm_49cddbdde4) := by
      rw [← Lp.simpleFunc.toLp_eq_toLp]
      exact congrArg (fun r : Lp.simpleFunc sharedTerm_1c5d85a2c0
          (2 ) μ => (r : sharedTerm_49cddbdde4))
        (Lp.simpleFunc.toLp_toSimpleFunc (S m))
    have hn : (Lp.simpleFunc.memLp (S n)).toLp
        (Lp.simpleFunc.toSimpleFunc (S n)) =
        (S n : sharedTerm_49cddbdde4) := by
      rw [← Lp.simpleFunc.toLp_eq_toLp]
      exact congrArg (fun r : Lp.simpleFunc sharedTerm_1c5d85a2c0
          (2 ) μ => (r : sharedTerm_49cddbdde4))
        (Lp.simpleFunc.toLp_toSimpleFunc (S n))
    rw [hm, hn]

  obtain ⟨pQ, hP⟩ := cauchySeq_tendsto_of_complete (show CauchySeq P by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      rcases Metric.cauchySeq_iff.mp hS.cauchySeq ε hε with ⟨N, hN⟩
      refine ⟨N, fun m hm n hn => ?_⟩
      rw [hdist]
      exact hN m hm n hn)
  exact ⟨S, pQ, hS, hP⟩

/-- A nested `L²` class has a product `L²` representative with the expected slices. -/
theorem exists_uncurry_memLp_two
     [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (q : Lp (Lp ℝ (2 ) ν) (2 ) μ) :
    ∃ Q : α × β → ℝ,
      MemLp Q (2 ) (μ.prod ν) ∧
      ∀ᵐ x ∂μ, (fun y => Q (x, y)) =ᵐ[ν] fun y => q x y := by
  obtain ⟨S, pQ, hS, hP⟩ := exists_product_simple_limit μ ν q
  let P  := fun n =>
    (memLp_simpleUncurry_two μ ν _
      (Lp.simpleFunc.memLp (S n))).toLp
        (simpleUncurry (Lp.simpleFunc.toSimpleFunc (S n)))
  change Tendsto P atTop (𝓝 pQ) at hP
  refine ⟨fun z => pQ z, Lp.memLp pQ, ?_⟩
  obtain ⟨φ, hφmono, hφ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hP).exists_seq_tendsto_ae
  have hSφ : Tendsto (fun i =>
      (S (φ i) : Lp (Lp ℝ (2 ) ν) (2 ) μ)) atTop (𝓝 q) :=
    hS.comp hφmono.tendsto_atTop
  obtain ⟨ψ, hψmono, hψ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hSφ).exists_seq_tendsto_ae
  have hPraw  :=
    ae_all_iff.mpr fun n => MemLp.coeFn_toLp
      (memLp_simpleUncurry_two μ ν _
        (Lp.simpleFunc.memLp (S n)))
  have hSraw  :=
    ae_all_iff.mpr fun n => Lp.simpleFunc.toSimpleFunc_eq_toFun (S n)



  filter_upwards [hSraw, hψ, (MeasureTheory.Measure.ae_ae_of_ae_prod (show ∀ᵐ z ∂μ.prod ν,
      Tendsto (fun i => simpleUncurry (Lp.simpleFunc.toSimpleFunc
        (S (φ (ψ i)))) z) atTop (𝓝 (pQ z)) by
      filter_upwards [hPraw, (hφ.mono fun _ hz => hz.comp hψmono.tendsto_atTop)] with z hz hlim
      refine hlim.congr' ?_
      filter_upwards with i
      exact hz (φ (ψ i))))] with x hxraw hxouter hxslice

  obtain ⟨κ, hκmono, hκ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (show Tendsto (fun i => Lp.simpleFunc.toSimpleFunc
      (S (φ (ψ i))) x) atTop (𝓝 (q x)) by
        refine hxouter.congr' ?_
        filter_upwards with i
        exact (hxraw (φ (ψ i))).symm)).exists_seq_tendsto_ae
  filter_upwards [hκ, hxslice] with y hky hsy
  exact tendsto_nhds_unique (hsy.comp hκmono.tendsto_atTop) hky

end

end HypoellipticAleksandrov
