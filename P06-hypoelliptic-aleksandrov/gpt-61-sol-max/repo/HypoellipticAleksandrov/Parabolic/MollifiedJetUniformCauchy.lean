module

public import HypoellipticAleksandrov.Parabolic.LocalizedHigherJetMollification
public import HypoellipticAleksandrov.Parabolic.UniformJetCauchyEstimate
public import Mathlib.Topology.MetricSpace.Cauchy
import Aesop
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
import all HypoellipticAleksandrov.Parabolic.HigherWeakDerivativeMollification
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily.ordinaryRepresentative_memLp_volume from HypoellipticAleksandrov.Parabolic.HigherWeakDerivativeMollification


@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

noncomputable section







variable (rho : ℝ)

/-- A positive sequence of mollifier radii strictly below `rho`. -/
def shrinkingRadius  (n : ℕ) : ℝ :=
  rho / (n + 2)

section
variable (hrho : 0 < rho) (n : ℕ)

include hrho
theorem shrinkingRadius_pos   :
    0 < shrinkingRadius rho n := div_pos hrho (by positivity)

theorem shrinkingRadius_lt   :
    shrinkingRadius rho n < rho := by
  rw [shrinkingRadius, div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)]
  nlinarith
end


theorem tendsto_shrinkingRadius  :
    Tendsto (shrinkingRadius rho) atTop (nhds 0) := by
  unfold shrinkingRadius
  apply Filter.Tendsto.const_div_atTop
  exact tendsto_atTop_add_const_right atTop 2
    (tendsto_natCast_atTop_atTop )

theorem tendsto_shrinkingRadius_nhdsWithin
     (hrho : 0 < rho) :
    Tendsto (shrinkingRadius rho) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_shrinkingRadius rho,
    Eventually.of_forall (shrinkingRadius_pos rho hrho)⟩

variable {d : ℕ}

private def addAllOnes
     (alpha : TimeVelocityDerivativeIndex d 2) :
    TimeVelocityDerivativeIndex d (d + 4) :=
  ⟨alpha.1 + TimeVelocityMultiIndex.allOnes d, by
    rw [TimeVelocityMultiIndex.order_add,
      TimeVelocityMultiIndex.order_allOnes]
    omega⟩

private theorem coordinateIteratedFDeriv_sub
     (beta : TimeVelocityMultiIndex d)
    (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f)
    (hg : ContDiff ℝ PDE.smoothOrder g) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv beta (f - g) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv beta f -
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta g := by
  funext z
  rw [show f - g = fun x => f x + (-g) x by rfl]
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_at beta]
  · unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    rw [iteratedFDeriv_neg_apply]
    change _ + (-_) = _ + -_
    rfl
  · exact (contDiff_infty.mp hf beta.order).contDiffAt
  · exact ((contDiff_infty.mp hg beta.order).neg).contDiffAt

private theorem allOnes_eq_sum_single (d : ℕ) :
    TimeVelocityMultiIndex.allOnes d =
      ∑ c : TimeVelocityCoord d, Pi.single c 1 := by
  funext c
  simp [TimeVelocityMultiIndex.allOnes]

variable {d : ℕ}

private theorem coordinateIteratedFDeriv_sum_single_comp
     (s : Finset (TimeVelocityCoord d))
    (alpha : TimeVelocityMultiIndex d) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (∑ c ∈ s, Pi.single c 1)
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (alpha + ∑ c ∈ s, Pi.single c 1) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      aesop
  | @insert c s hc ih =>
      rw [Finset.sum_insert hc]
      rw [add_comm (Pi.single c 1)]
      funext z
      rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
      · rw [ih]
        symm
        rw [← add_assoc]
        rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
        · exact contDiff_infty.mp hf _
      · exact contDiff_infty.mp
          (_root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty alpha f hf) _

private theorem coordinateIteratedFDeriv_allOnes_comp
     (alpha : TimeVelocityMultiIndex d)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiff ℝ PDE.smoothOrder f) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (TimeVelocityMultiIndex.allOnes d)
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (alpha + TimeVelocityMultiIndex.allOnes d) f := by
  classical
  rw [allOnes_eq_sum_single]
  exact coordinateIteratedFDeriv_sum_single_comp
      (Finset.univ : Finset (TimeVelocityCoord d)) alpha f hf

/-- Every coordinate jet through ordinary order two is uniformly Cauchy
along the common shrinking mollifier radii. -/
theorem uniformCauchySeqOn_coordinateJet_spacetimeMollification_shrinkingRadius
     {root : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (G : ParabolicWeakDerivativeFamily d (2 * (d + 4)) Set.univ root)
    (rho : ℝ) (hrho : 0 < rho)
    (K : HypoellipticAleksandrov.Parabolic.Region d) (hK : IsCompact K)
    (hsupp : ∀ ε, 0 < ε → ε < rho →
      ∀ beta : TimeVelocityDerivativeIndex d (d + 4),
        tsupport (SpacetimeMollifier.spacetimeMollification ε
          (G.ordinaryRepresentative beta)) ⊆ K)
    (alpha : TimeVelocityDerivativeIndex d 2) :
    UniformCauchySeqOn
      (fun n => TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
          (G.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.zero d (d + 4)))))
      atTop Set.univ := by
  let sharedTerm_f3bf1a7577 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let beta  := addAllOnes alpha
  let r  := shrinkingRadius rho
  let u  := fun n =>
    SpacetimeMollifier.spacetimeMollification (r n)
      (G.ordinaryRepresentative (alpha.castLE (by omega)))
  have hrpos  := shrinkingRadius_pos rho hrho
  have hrlt  := shrinkingRadius_lt rho hrho
  have hu_eq : ∀ n,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (r n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d (d + 4)))) = u n := by
    intro n
    exact G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
      (r n) (hrpos n) (alpha.castLE (by omega))
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let C : ℝ := Real.sqrt (volume.real K)

  have ht  := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((G.tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub
          beta).comp
        (tendsto_shrinkingRadius_nhdsWithin rho hrho))
  have htail : ∀ᶠ n in atTop,
      C * ENNReal.toReal
        (eLpNorm
          (SpacetimeMollifier.spacetimeMollification (r n)
              (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta)
          (2 ) sharedTerm_f3bf1a7577) < ε / 2 := by

    have : Tendsto (fun n => C * ENNReal.toReal
        (eLpNorm
          (SpacetimeMollifier.spacetimeMollification (r n)
              (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta)
          (2 ) sharedTerm_f3bf1a7577)) atTop (nhds 0) := by
      simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (nhds C)).mul ht))
    exact (tendsto_order.1 this).2 _ (half_pos hε)
  rw [eventually_atTop] at htail
  obtain ⟨N, hN⟩ := htail
  refine ⟨N, ?_⟩
  intro m hm n hn z hz
  rw [hu_eq m, hu_eq n]
  rw [Real.dist_eq]
  let f := u m - u n
  have hfm : ContDiff ℝ PDE.smoothOrder (u m) :=
    SpacetimeMollifier.contDiff_spacetimeMollification (hrpos m) _
      ((_root_.HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily.ordinaryRepresentative_memLp_volume G (alpha.castLE (by omega))).locallyIntegrable
        (by norm_num))
  have hfn : ContDiff ℝ PDE.smoothOrder (u n) :=
    SpacetimeMollifier.contDiff_spacetimeMollification (hrpos n) _
      ((_root_.HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily.ordinaryRepresentative_memLp_volume G (alpha.castLE (by omega))).locallyIntegrable
        (by norm_num))
  have hbase (k : ℕ)  :=
    G.contDiff_spacetimeMollification_ordinaryRepresentative_zero (r k) (hrpos k)


  have hpoint := abs_le_sqrt_volume_mul_eLpNorm_coordinateIteratedFDeriv_allOnes
    d K hK f (hfm.sub hfn) (by
        apply closure_minimal _ hK.isClosed
        intro x hx
        by_contra hxK
        have hm0 : u m x = 0 := by
          apply Function.notMem_support.mp
          exact fun hxm => hxK ((subset_tsupport (u m)) hxm |> hsupp (r m) (hrpos m)
            (hrlt m) (alpha.castLE (by omega)))
        have hn0 : u n x = 0 := by
          apply Function.notMem_support.mp
          exact fun hxn => hxK ((subset_tsupport (u n)) hxn |> hsupp (r n) (hrpos n)
            (hrlt n) (alpha.castLE (by omega)))
        exact hx (by simp [f, hm0, hn0])) z
  have hgrid : TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (TimeVelocityMultiIndex.allOnes d) f =
      SpacetimeMollifier.spacetimeMollification (r m)
          (G.ordinaryRepresentative beta) -
        SpacetimeMollifier.spacetimeMollification (r n)
          (G.ordinaryRepresentative beta) := by
    rw [coordinateIteratedFDeriv_sub _ _ _ hfm hfn]
    rw [← hu_eq m, ← hu_eq n]
    rw [coordinateIteratedFDeriv_allOnes_comp alpha.1 _ (hbase m)]
    rw [coordinateIteratedFDeriv_allOnes_comp alpha.1 _ (hbase n)]
    change TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 _ -
      TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 _ = _
    rw [G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
      (r m) (hrpos m) beta]
    rw [G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
      (r n) (hrpos n) beta]
  rw [hgrid] at hpoint
  refine hpoint.trans_lt ?_
  have hmmem := _root_.HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily.ordinaryRepresentative_memLp_volume G beta


  have hmmoll : MemLp
      (SpacetimeMollifier.spacetimeMollification (r m)
        (G.ordinaryRepresentative beta)) 2 volume := by
    apply Continuous.memLp_of_hasCompactSupport
      (SpacetimeMollifier.contDiff_spacetimeMollification (hrpos m) _
        (hmmem.locallyIntegrable (by norm_num))).continuous
    exact hK.of_isClosed_subset (isClosed_tsupport (f :=
      SpacetimeMollifier.spacetimeMollification (r m)
        (G.ordinaryRepresentative beta)))
      (hsupp (r m) (hrpos m) (hrlt m) beta)
  have hnmoll : MemLp
      (SpacetimeMollifier.spacetimeMollification (r n)
        (G.ordinaryRepresentative beta)) 2 volume := by
    apply Continuous.memLp_of_hasCompactSupport
      (SpacetimeMollifier.contDiff_spacetimeMollification (hrpos n) _
        (hmmem.locallyIntegrable (by norm_num))).continuous
    exact hK.of_isClosed_subset (isClosed_tsupport (f :=
      SpacetimeMollifier.spacetimeMollification (r n)
        (G.ordinaryRepresentative beta)))
      (hsupp (r n) (hrpos n) (hrlt n) beta)
  have hmlimMem := hmmoll.sub hmmem
  have hnlimMem := hnmoll.sub hmmem

  have htri := eLpNorm_sub_le (μ := volume)
    (f := SpacetimeMollifier.spacetimeMollification (r m)
      (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta)
    (g := SpacetimeMollifier.spacetimeMollification (r n)
      (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq :
      (SpacetimeMollifier.spacetimeMollification (r m)
          (G.ordinaryRepresentative beta) -
        SpacetimeMollifier.spacetimeMollification (r n)
          (G.ordinaryRepresentative beta)) =
      (SpacetimeMollifier.spacetimeMollification (r m)
          (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta) -
        (SpacetimeMollifier.spacetimeMollification (r n)
          (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [← heq] at htri
  have htoReal := (ENNReal.toReal_le_toReal (hmmoll.sub hnmoll).eLpNorm_lt_top.ne
    (ENNReal.add_ne_top.2
      ⟨hmlimMem.eLpNorm_lt_top.ne, hnlimMem.eLpNorm_lt_top.ne⟩)).2 htri
  calc
    C * ENNReal.toReal (eLpNorm
        (SpacetimeMollifier.spacetimeMollification (r m)
            (G.ordinaryRepresentative beta) -
          SpacetimeMollifier.spacetimeMollification (r n)
            (G.ordinaryRepresentative beta)) 2 volume) ≤
      C * (ENNReal.toReal (eLpNorm
          (SpacetimeMollifier.spacetimeMollification (r m)
              (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta) 2 volume) +
        ENNReal.toReal (eLpNorm
          (SpacetimeMollifier.spacetimeMollification (r n)
              (G.ordinaryRepresentative beta) - G.ordinaryRepresentative beta) 2 volume)) := by
        gcongr
        simpa only [ENNReal.toReal_add hmlimMem.eLpNorm_lt_top.ne hnlimMem.eLpNorm_lt_top.ne]
          using htoReal
    _ < ε := by
      rw [mul_add]
      have hm' := hN m hm
      have hn' := hN n hn
      linarith

end

end HypoellipticAleksandrov.Parabolic
