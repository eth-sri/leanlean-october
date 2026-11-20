module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeak

/-! # Removing the origin from position weak-derivative tests -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set

section
variable {d : ℕ} (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (i : Fin d)
include ht

/-- A C2 test has continuous position derivative components. -/
theorem continuous_dx_test : Continuous (fun q => dx test q i) := by
  exact ((ht.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

/-- A C2 test has continuous velocity derivative components. -/
theorem continuous_dv_test : Continuous (fun q => dv test q i) :=
  (contDiff_dv_test test ht i).continuous

end

/-- A C2 test has continuous second velocity derivative components. -/
theorem continuous_dvv_test {d : ℕ} (test : XV d → ℝ)
    (ht : ContDiff ℝ 2 test) (i k : Fin d) : Continuous (fun q => dvv test q i k) := by
  exact (((contDiff_dv_test test ht k).contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem weak_identity_extend {d : ℕ} {H g test : XV d → ℝ} (hH : Continuous H)
    (hg : LocallyIntegrable g volume) (ht : ContDiff ℝ 2 test) (hs : HasCompactSupport test)
    (D : (XV d → ℝ) → XV d → ℝ) (hDc : Continuous (D test)) (hDs : HasCompactSupport (D test))
    {proj : XV d → PDE.Vec d} (hp : ContDiff ℝ 2 proj) (hp0 : proj 0 = 0)
    (hae : ∀ᵐ q ∂volume, proj q ≠ 0) (sign : ℝ)
    (hweak : ∀ t : XV d → ℝ, ContDiff ℝ 2 t → HasCompactSupport t → 0 ∉ tsupport t →
      (∫ q, H q * D t q) = sign * ∫ q, g q * t q)
    (hcut : ∀ n q, D (fun y => test y * originCutoff n (proj y)) q =
      D test q * originCutoff n (proj q)) :
    (∫ q, H q * D test q) = sign * ∫ q, g q * test q := by
  have hL : Integrable (fun q => H q * D test q) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      hH.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hDc hDs
  have hR : Integrable (fun q => g q * test q) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      hg.integrable_smul_left_of_hasCompactSupport ht.continuous hs
  apply integral_eq_of_originCutoff hL hR sign hp.continuous hae
  intro n
  have hzero : (0 : XV d) ∉ tsupport (fun q => test q * originCutoff n (proj q)) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    have hproj : Tendsto proj (nhds 0) (nhds 0) := hp0 ▸ hp.continuous.tendsto 0
    have h := (originCutoff_eventually_zero d n).comp_tendsto hproj
    filter_upwards [h] with q hq
    change originCutoff n (proj q) = 0 at hq
    simp [hq]
  have hw := hweak _ (ht.mul (((contDiff_originCutoff d n).of_le (by simp)).comp hp)) hs.mul_right hzero
  simpa only [Function.comp_apply, hcut, mul_assoc] using hw

section
variable (d : ℕ) (hd : 1 ≤ d)
include hd

/-- All three punctured distributional identities extend to the entire carrier. -/
theorem profile_weak_identities_extend
    (H : XV d → ℝ) (gx gv : XV d → PDE.Vec d) (hess : XV d → PDE.Mat d)
    (hH : Continuous H)
    (hgx : ∀ i, LocallyIntegrable (fun q => gx q i) volume)
    (hgv : ∀ i, LocallyIntegrable (fun q => gv q i) volume)
    (hhess : ∀ i k, LocallyIntegrable (fun q => hess q i k) volume)
    (hweak : ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (0 : XV d) ∉ tsupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) :
    ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q)) := by
  intro test ht hs
  have hcoord := coordinates_ne_zero_ae d hd
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [neg_one_mul] using weak_identity_extend hH (hgx i) ht hs
      (fun t q => dx t q i) (continuous_dx_test test ht i) (hs.fderiv_apply ℝ (Pi.single i 1, 0))
      contDiff_snd rfl (hcoord.mono fun _ hq => hq.2) (-1)
      (fun t htc hts hto => by simpa only [neg_one_mul] using (hweak t htc hts hto).1 i)
      (fun n q => dx_mul_velocity_cutoff test n q (ht.differentiable (by norm_num) q) i)
  · intro i
    simpa only [neg_one_mul] using weak_identity_extend hH (hgv i) ht hs
      (fun t q => dv t q i) (continuous_dv_test test ht i) (hs.fderiv_apply ℝ (0, Pi.single i 1))
      contDiff_fst rfl (hcoord.mono fun _ hq => hq.1) (-1)
      (fun t htc hts hto => by simpa only [neg_one_mul] using (hweak t htc hts hto).2.1 i)
      (fun n q => dv_mul_position_cutoff test n q (ht.differentiable (by norm_num) q) i)
  · intro i k
    simpa only [one_mul] using weak_identity_extend hH (hhess i k) ht hs
      (fun t q => dvv t q i k) (continuous_dvv_test test ht i k)
      ((hs.fderiv_apply ℝ (0, Pi.single k 1)).fderiv_apply ℝ (0, Pi.single i 1))
      contDiff_fst rfl (hcoord.mono fun _ hq => hq.1) 1
      (fun t htc hts hto => by simpa only [one_mul] using (hweak t htc hts hto).2.2 i k)
      (fun n q => dvv_mul_position_cutoff test n ht q i k)

end

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
