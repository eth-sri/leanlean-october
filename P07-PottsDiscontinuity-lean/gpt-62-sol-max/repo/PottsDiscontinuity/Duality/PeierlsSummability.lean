module

public import PottsDiscontinuity.Duality.ConnectionSymmetry

/-! A summable union bound for long connections from the nonnegative axis to the
negative half-plane. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK MeasureTheory
noncomputable section

abbrev OppositeConnectionIndex := ℕ × LatticeVertex

def oppositeConnectionEvent (t : OppositeConnectionIndex) : Set LatticeConfiguration :=
  {ω | t.2.1 < 0 ∧ ω ∈ connectionEvent ((t.1 : ℤ), 0) t.2}

/-- Only finitely many of these connections occur almost surely. -/
theorem free_ae_finite_oppositeConnections (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    ∀ᵐ ω ∂μ, {t : OppositeConnectionIndex | ω ∈ oppositeConnectionEvent t}.Finite := by
  have := hμ.1
  have hnat : Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
    simpa [mul_comm] using Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hc)
  have hprod := (hnat.mul_of_nonneg (summable_exp_neg_l1 hc) (fun _ => by positivity)
    (fun _ => by positivity)).mul_left C
  apply ae_finite_setOfPred_mem
  refine ne_top_of_le_ne_top hprod.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum ?_)
  rintro ⟨k, w⟩
  by_cases hw : w.1 < 0
  · have he : oppositeConnectionEvent (k, w) = connectionEvent (k, 0) w := by
      ext; simp [oppositeConnectionEvent, hw]
    rw [he, ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    let u : LatticeVertex := (k, 0)
    have ht := free_connection_translate θ μ hμ u 0 (w-u)
    have htr : μ.real (connectionEvent u w) = twoPoint μ (w-u) := by
      simpa [twoPoint, measureReal_def] using congrArg ENNReal.toReal ht
    have hw' : (w.1 : ℝ) ≤ 0 := by exact_mod_cast hw.le
    change μ.real (connectionEvent u w) ≤ _
    rw [htr]
    refine (hdecay (w-u)).trans_eq ?_
    simp only [u, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_natCast, sub_zero,
      abs_of_nonpos (sub_nonpos.2 (hw'.trans (Nat.cast_nonneg k))), abs_of_nonpos hw']
    rw [show -c * (-((w.1 : ℝ) - k) + |(w.2 : ℝ)|) =
      -c * k + -c * (-(w.1 : ℝ) + |(w.2 : ℝ)|) by ring, Real.exp_add]
  · have he : oppositeConnectionEvent (k, w) = ∅ := by
      ext; simp [oppositeConnectionEvent, hw]
    simp [he]

end
end PottsDiscontinuity.Duality
