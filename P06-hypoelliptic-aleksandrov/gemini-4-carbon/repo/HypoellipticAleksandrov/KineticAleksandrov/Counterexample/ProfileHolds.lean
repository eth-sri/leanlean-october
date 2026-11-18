module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileOneAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSource
import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set
open scoped MatrixOrder











/-- The literal source formula satisfies the source manuscript's Lp estimate. -/
theorem flat_source_eLpNorm_le_of_profile (d : ℕ) (alpha p : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 1 ≤ p)
    (hprofile : CounterProfileStatement d alpha) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      eLpNorm
        (flatSource (profileMatrix hprofile) (profileFunction hprofile) flatteningPsi alpha r)
        (ENNReal.ofReal p) (volume.restrict {q | profileFunction hprofile q < 1}) ≤
          ENNReal.ofReal (C * Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p))    := by
  have shell_source_bound {d : ℕ} (A : XV d → PDE.Mat d) (H : XV d → ℝ) (gv : XV d → PDE.Vec d) (lam : ℝ) (Lam : ℝ) (C : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hA : ∀ q, lam • 1 ≤ A q ∧ A q ≤ Lam • 1) (hC : 0 < C) (hzero : H 0 = 0) (hcomp : ∀ q, H q ≤ C * Real.rpow (rho q) alpha) (hgrad : ∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) :
      ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ q,
      0 ≤ flatSourceWithJet A H gv alpha r q ∧
      flatSourceWithJet A H gv alpha r q ≤ K * Real.rpow r (alpha - 2) := by
    have source_rpow_identity (r : ℝ) (hr : 0 < r) :
        Real.rpow r (-alpha) * (Real.rpow r (alpha - 1)) ^ 2 =
        Real.rpow r (alpha - 2) := by
      simp
      rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
      congr 1
      ring
    have velocity_gradient_on_shell (hgrad : ∀ q : XV d, q ≠ 0 →
        PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) :
        ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ q ∈ profileShell H alpha r,
        PDE.vecEuclideanNorm (gv q) ≤ K * Real.rpow r (alpha - 1) := by
      let B : ℝ := Real.rpow C alpha⁻¹
      have hB : 0 < B := Real.rpow_pos_of_pos hC _
      have hBa : B ^ alpha = C := Real.rpow_inv_rpow hC.le ha.ne'
      let K : ℝ := C / B ^ (alpha - 1)
      have hK : 0 < K := div_pos hC (Real.rpow_pos_of_pos hB _)
      refine ⟨K, hK, ?_⟩
      intro r hr q hq
      have hlo := hq.1
      have hn : q ≠ 0 := by
        intro he
        rw [he, hzero] at hlo
        exact (not_le_of_gt (Real.rpow_pos_of_pos hr alpha)) hlo
      have hb : r ≤ B * rho q := by
        apply (Real.rpow_le_rpow_iff hr.le (mul_nonneg hB.le (rho_nonneg q)) ha).mp
        rw [Real.mul_rpow hB.le (rho_nonneg q), hBa]
        exact hlo.trans (hcomp q)
      have hlower : r / B ≤ rho q := (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hb)
      have hp := Real.rpow_le_rpow_of_nonpos (div_pos hr hB) hlower (sub_nonpos.mpr ha1.le)
      have ht := (hgrad q hn).trans (mul_le_mul_of_nonneg_left hp hC.le)
      simp at ht ⊢
      rw [Real.div_rpow hr.le hB.le] at ht
      simpa only [K, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using ht
    obtain ⟨G, hG, hgradShell⟩ := velocity_gradient_on_shell hgrad
    obtain ⟨D, hD, hsecond⟩ := flatteningPsi_deriv2_bound
    have hLam := hlam.trans_le hlamLam
    refine ⟨D * Lam * G ^ 2, by positivity, ?_⟩
    intro r hr q
    by_cases hq : q ∈ profileShell H alpha r
    · have hquad0 := quadratic_nonneg_of_loewner lam hlam.le (A q) (hA q).1 (gv q)
      have hnormSq : PDE.vecNormSq (gv q) ≤ (G * Real.rpow r (alpha - 1)) ^ 2 := by
        rw [← PDE.vecEuclideanNorm_sq]
        exact pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) (hgradShell r hr q hq) _
      unfold flatSourceWithJet
      constructor
      · exact mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hr _).le (flatteningPsi_deriv2_nonneg (H q / Real.rpow r alpha))) hquad0
      · calc
          _ ≤ Real.rpow r (-alpha) * D * (Lam * (G * Real.rpow r (alpha - 1)) ^ 2) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left (hsecond (H q / Real.rpow r alpha)) (Real.rpow_pos_of_pos hr _).le)
              ((quadratic_upper_of_loewner Lam (A q) (hA q).2 (gv q)).trans (mul_le_mul_of_nonneg_left hnormSq hLam.le))
              hquad0 (mul_nonneg (Real.rpow_pos_of_pos hr _).le hD.le)
          _ = D * Lam * G ^ 2 *
              (Real.rpow r (-alpha) * (Real.rpow r (alpha - 1)) ^ 2) := by ring
          _ = _ := by rw [source_rpow_identity r hr]
    · rw [flatSourceWithJet_eq_zero_off_shell A H gv alpha r hr q hq]
      exact ⟨le_rfl, mul_nonneg
        (mul_nonneg (mul_nonneg hD.le hLam.le) (sq_nonneg G))
        (Real.rpow_pos_of_pos hr _).le⟩
  have source_norm_rpow_identity (V : ℝ) (K : ℝ) (r : ℝ) (hp : 0 < p) (hV : 0 < V) (hK : 0 ≤ K) (hr : 0 < r) :
      ENNReal.ofReal (K * Real.rpow r (alpha - 2)) *
      ENNReal.ofReal (V * r ^ (4 * d)) ^ (1 / p) =
        ENNReal.ofReal (K * Real.rpow V (1 / p) *
          Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p)) := by
    simp only [Real.rpow_eq_pow]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (show 0 ≤ V * r ^ (4 * d) from mul_nonneg hV.le (pow_nonneg hr.le _))
      (div_nonneg zero_le_one hp.le),
      ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_pos_of_pos hr _).le),
      Real.mul_rpow hV.le (pow_nonneg hr.le _), ← Real.rpow_natCast_mul hr.le]
    have he : (4 * d : ℕ) * (1 / p : ℝ) = 4 * (d : ℝ) / p := by
      push_cast
      ring
    rw [he]
    congr 1
    calc
      _ = (K * V ^ (1 / p)) * (r ^ (alpha - 2) * r ^ (4 * (d : ℝ) / p)) := by ring
      _ = _ := by rw [← Real.rpow_add hr]
  have eLpNorm_le_shell_bound {d : ℕ} (f : XV d → ℝ) (S : Set (XV d)) (B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) (hf : AEStronglyMeasurable f volume) (hS : MeasurableSet S) (hbound : ∀ q, 0 ≤ f q ∧ f q ≤ B) (hsupp : ∀ q, q ∉ S → f q = 0) :
      eLpNorm f (ENNReal.ofReal p) volume ≤ ENNReal.ofReal B * volume S ^ (1 / p) := by
    have hm : ∀ᵐ q ∂volume, ‖f q‖ ≤ ‖S.indicator (fun _ => B) q‖ := by
      filter_upwards [] with q
      by_cases hq : q ∈ S
      · rw [indicator_of_mem hq, Real.norm_eq_abs, abs_of_nonneg (hbound q).1,
          Real.norm_eq_abs, abs_of_nonneg hB]
        exact (hbound q).2
      · rw [hsupp q hq, indicator_of_notMem hq]
    apply (eLpNorm_mono_ae hf hm).trans_eq
    rw [eLpNorm_indicator_const hS.nullMeasurableSet (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hB]
  obtain ⟨hlam, hlamLam, hc, hC, hAm, hA, hH, hzero, hhom, hcomp,
    _, hgv, _, _, _, hgrad, _⟩ := selectedProfile_spec hprofile
  have hp0 := zero_lt_one.trans_le hp
  obtain ⟨V, hV, hvol⟩ := shell_volume_bound (profileFunction hprofile) alpha
    (profileLowerComparison hprofile) ha hc hH (fun q => (hcomp q).1) hhom
  obtain ⟨K, hK, hbound⟩ := shell_source_bound (profileMatrix hprofile)
    (profileFunction hprofile) (profileVelocityJet hprofile)
    (profileLowerEllipticity hprofile) (profileUpperEllipticity hprofile)
    (profileUpperComparison hprofile) hlam hlamLam hA hC hzero
    (fun q => (hcomp q).2) hgrad
  refine ⟨K * Real.rpow V (1 / p), 1, mul_pos hK (Real.rpow_pos_of_pos hV _),
    zero_lt_one, ?_⟩
  intro r hr _
  have hf := (measurable_flatSourceWithJet (profileMatrix hprofile)
    (profileFunction hprofile) (profileVelocityJet hprofile) alpha r
    hAm hH.measurable hgv).aestronglyMeasurable (μ := volume)
  have hS : MeasurableSet (profileShell (profileFunction hprofile) alpha r) :=
    ((isClosed_le continuous_const hH).inter (isClosed_le hH continuous_const)).measurableSet
  have hn := eLpNorm_le_shell_bound _ (profileShell (profileFunction hprofile) alpha r) (K * Real.rpow r (alpha - 2)) hp0
    (mul_nonneg hK.le (Real.rpow_pos_of_pos hr _).le) hf hS (hbound r hr)
    (fun q hq => flatSourceWithJet_eq_zero_off_shell _ _ _ alpha r hr q hq)
  have hn' := hn.trans (mul_le_mul_right (ENNReal.rpow_le_rpow (hvol r hr) (div_nonneg zero_le_one hp0.le)) (ENNReal.ofReal (K * Real.rpow r (alpha - 2))))
  rw [source_norm_rpow_identity V K r hp0 hV hK.le hr] at hn'
  apply (eLpNorm_restrict_le _ _ _ _).trans
  rw [eLpNorm_congr_ae (flatSource_ae_eq_jet_of_profile hprofile r)]
  exact hn'



/-- The scalar and higher-dimensional constructions supply the complete shared profile. -/
theorem counterProfile_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) : CounterProfileStatement d alpha   := by
  have counterProfileGeTwo_holds (hd : 2 ≤ d) :
      CounterProfileGeTwoStatement d alpha := by
    obtain ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
      hsmooth, hhom, hcomp, heq, hgrad⟩ := profile_ge_two d hd alpha ha ha1
    exact ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
      hhom, hcomp, hsmooth, heq, hgrad⟩
  have counterProfile_of_branches (hone : d = 1 → CounterProfileOneStatement alpha) (hge : 2 ≤ d → CounterProfileGeTwoStatement d alpha) :
      CounterProfileStatement d alpha := by
    have counterProfile_ge_two (hd : 2 ≤ d) (h : CounterProfileGeTwoStatement d alpha) :
        CounterProfileStatement d alpha := by
      rcases h with ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
        hhom, hcomp, hs, heq, hgrad⟩
      have hd1 : 1 ≤ d := by omega
      have hH := continuous_profile_of_comparison H alpha c C ha hc.le hzero hcomp hs
      obtain ⟨hx, hv, hh⟩ := profile_classical_jets_locallyIntegrable d hd1 H alpha ha ha1 hhom hs
      have heqae : ∀ᵐ q ∂volume, matrixContraction (A q) (dvv H q) = PDE.vecDot q.2 (dx H q) := by
        filter_upwards [coordinates_ne_zero_ae d hd1] with q hq
        exact heq q (fun hz => hq.1 (congrArg Prod.fst hz))
      refine ⟨lam, Lam, c, C, A, H, dx H, dv H, dvv H,
        hlam, hLam, hc, hC, hmA, hA, hH, hzero, hhom, hcomp,
        measurable_dx H, measurable_dv H, measurable_dvv H,
        Filter.Eventually.of_forall (fun _ => ⟨rfl, rfl, rfl⟩), heqae, hgrad,
        profile_jets_compact_bound H hs, hx, hv, hh,
        profile_weak_identities_extend d hd1 H (dx H) (dv H) (dvv H) hH hx hv hh
          (profile_classical_punctured_weak d hd1 H alpha ha ha1 hH hhom hs), (fun _ => hs), ?_⟩
      filter_upwards [coordinates_ne_zero_ae d hd1] with q hq
      have hq0 : q ≠ 0 := fun hz => hq.1 (congrArg Prod.fst hz)
      exact (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq0))).of_le (by simp)
    by_cases hd1 : d = 1
    · subst d
      exact counterProfile_one alpha ha ha1 (hone rfl)
    · have hd2 : 2 ≤ d := by omega
      exact counterProfile_ge_two hd2 (hge hd2)
  exact counterProfile_of_branches
    (fun _ => counterProfileOne_exists alpha ha ha1)
    (fun hd2 => counterProfileGeTwo_holds hd2)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

