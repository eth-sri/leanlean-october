module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Profile
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileConstruction
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileNormalize
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSolver
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJetHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSpectralJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SpectralMeasurablePunctured
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRadial
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSigns
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsRescaled
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsSeedTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffCompact
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffJets
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Compactness.Compact
import PDEFoundation.Ambient.EuclideanNorm
import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # The proved higher-dimensional profile supplies the shared branch interface -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped MatrixOrder Matrix.Norms.L2Operator
open Filter Topology
open scoped BigOperators

/- The internally constructed profile satisfies the exact higher-dimensional branch statement. -/
theorem counterProfileGeTwo_holds (d : ℕ) (hd : 2 ≤ d) (alpha )
    (ha : 0 < alpha) (ha1 : alpha < 1) : CounterProfileGeTwoStatement d alpha := by
  obtain ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
    hsmooth, hhom, hcomp, heq, hgrad⟩ : ∃ lam Lam c C : ℝ,
      ∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
      ∃ H : (PDE.Vec d × PDE.Vec d) → ℝ,
        0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
        (∀ i k, Measurable (fun q => A q i k)) ∧
        (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧
          A q ≤ Lam • (1 : PDE.Mat d)) ∧
        H 0 = 0 ∧
        ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ) ∧
        (∀ r : ℝ, 0 < r → ∀ q,
          H (r ^ 3 • q.1, r • q.2) = Real.rpow r alpha * H q) ∧
        (∀ q, c * Real.rpow
          (Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6)) alpha
          ≤ H q ∧ H q ≤ C * Real.rpow
          (Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6)) alpha) ∧
        (∀ q, q ≠ 0 →
          matrixContraction (A q)
            (fun i k => fderiv ℝ
              (fun z => fderiv ℝ H z (0, Pi.single k 1)) q (0, Pi.single i 1)) =
            PDE.vecDot q.2 (fun i => fderiv ℝ H q (Pi.single i 1, 0))) ∧
        (∀ q, q ≠ 0 →
          PDE.vecEuclideanNorm (fun i => fderiv ℝ H q (0, Pi.single i 1)) ≤
            C * Real.rpow
              (Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6))
              (alpha - 1)) := by
    obtain ⟨C₀, sigma, R, lam, Lam, A, hC₀, hsigma, hR2, hlam, hlamLam,
      hmeas, helliptic, hsolve⟩ : ∃ C₀ sigma R lam Lam : ℝ, ∃ A : XV d → PDE.Mat d,
        0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ 0 < lam ∧ lam ≤ Lam ∧
        (∀ i k, Measurable (fun q => A q i k)) ∧
        (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
        (∀ q, q ≠ 0 → matrixContraction (A q) (dvv (geometricProfile alpha C₀ sigma R) q) =
          PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q)) := by
      obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :
          ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ ∀ q : XV d, q ≠ 0 →
                let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
                (dvv H q).IsHermitian ∧ 0 < positiveSpectralMass (dvv H q) ∧
                  (negativeSpectralMass (dvv H q) = 0 → 0 < PDE.vecDot q.2 (dx H q)) := by
        obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ : ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧
            ∀ q : XV d, q ≠ 0 →
              (∃ w, 0 < fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w) ∧
              ((∃ w, fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w < 0) ∨
                0 < PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q)) := by
          obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ : ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧
              ∀ y e : PDE.Vec d, PDE.vecNormSq e = 1 →
                (∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w) ∧
                ((∃ w, cutoffHessian alpha C₀ sigma R y e w < 0) ∨
                  1 ≤ ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e) := by
            let sigma := (1 - alpha) / 8
            have hsigma : 0 < sigma := div_pos (sub_pos.mpr ha1) (by norm_num)
            have hsq : sigma ^ 2 < (1 - alpha) / 16 := by
              dsimp [sigma]
              nlinarith [sq_nonneg alpha]
            obtain ⟨C₀, hC₀, htransport⟩ : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ y e : PDE.Vec d,
              PDE.vecNormSq e = 1 → PDE.vecEuclideanNorm (y - e) ≤ 1 / 4 →
              1 ≤ ansatzTransport alpha (seed alpha C₀ sigma) y e := by
              let f : PDE.Vec d × PDE.Vec d → ℝ :=
                fun q => ansatzTransport alpha (seed alpha 0 sigma) q.1 q.2
              have _h_xinl_0 : Continuous (fun q : PDE.Vec d × PDE.Vec d => ansatzTransport alpha (seed alpha 0 sigma) q.1 q.2) := by
                have hb : ContDiff ℝ (⊤ : ℕ∞)
                    (fun q : PDE.Vec d × PDE.Vec d => seedBase sigma q.1 q.2) := by
                  unfold seedBase PDE.vecNormSq PDE.vecDot
                  fun_prop
                have hp : Continuous (fun q : PDE.Vec d × PDE.Vec d =>
                    Real.rpow (seedBase sigma q.1 q.2) (alpha / 2 - 1)) :=
                  (hb.rpow_const_of_ne (p := alpha / 2 - 1) fun q =>
                    (seedBase_pos sigma hsigma q.1 q.2).ne').continuous
                have hs := (contDiff_seed (d := d) alpha 0 sigma hsigma).continuous
                simp_rw [ansatzTransport_seed alpha 0 sigma hsigma]
                unfold PDE.vecDot
                fun_prop
              obtain ⟨B₀, hB₀⟩ := (isCompact_smallSeedBall d).bddAbove_image
                _h_xinl_0.abs.continuousOn
              let B := max 0 B₀
              have hB : 0 ≤ B := le_max_left _ _
              let C₀ := 4 * (B + 1) / alpha
              have hC₀ : 0 < C₀ := div_pos (mul_pos (by norm_num) (by linarith)) ha
              refine ⟨C₀, hC₀, ?_⟩
              intro y e he hy
              have hbound : |f (y, e)| ≤ B :=
                (hB₀ ⟨(y, e), ⟨he, hy⟩, rfl⟩).trans (le_max_right _ _)
              have hlow := (abs_le.mp hbound).1
              have hdot : (3 / 4 : ℝ) ≤ PDE.vecDot y e := by
                have henorm : PDE.vecEuclideanNorm e = 1 := by
                  simp [PDE.vecEuclideanNorm, he]
                have hcs := PDE.abs_vecDot_le_vecEuclideanNorm_mul (y - e) e
                rw [henorm, mul_one] at hcs
                have hdot : PDE.vecDot (y - e) e = PDE.vecDot y e - 1 := by
                  simp only [PDE.vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
                  change PDE.vecDot y e - PDE.vecNormSq e = _
                  rw [he]
                  rfl
                rw [hdot] at hcs
                have hh := (abs_le.mp (hcs.trans hy)).1
                linarith
              have hc : 0 < alpha / 3 * C₀ := mul_pos (div_pos ha (by norm_num)) hC₀
              have hmul := mul_le_mul_of_nonneg_right hdot hc.le
              have heq : (3 / 4 : ℝ) * (alpha / 3 * C₀) = B + 1 := by
                dsimp [C₀]
                field_simp
              rw [heq] at hmul
              rw [ansatzTransport_seed_shift alpha C₀ sigma hsigma]
              change 1 ≤ f (y, e) + PDE.vecDot y e * (alpha / 3 * C₀)
              linarith
            have _h_xinl_0 : ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d, PDE.vecNormSq e = 1 → ∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w := by
              filter_upwards [eventually_cutoff_annulus_signs d hd alpha C₀ sigma ha ha1 hsigma]
                with R hR
              have hR0 : 0 < R := lt_trans (by norm_num) hR.1
              refine ⟨hR.1, ?_⟩
              intro y e he
              by_cases hy : PDE.vecEuclideanNorm y < R
              · obtain ⟨w, hw⟩ := seed_positive_direction d hd alpha C₀ sigma ha hsigma y e
                exact ⟨w, by rwa [cutoffHessian_eq_seed alpha C₀ sigma R hR0 y e w hy]⟩
              · by_cases houter : 2 * R < PDE.vecEuclideanNorm y
                · have hy0 : y ≠ 0 := by
                    intro hzero
                    have hn : PDE.vecEuclideanNorm y = 0 := PDE.vecEuclideanNorm_eq_zero_iff.mpr hzero
                    rw [hn] at houter
                    linarith
                  obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha y hy0
                  refine ⟨w, ?_⟩
                  rw [cutoffHessian_eq_radial alpha C₀ sigma R hR0 y e w houter,
                    radialProfile_hessian alpha y w w hy0]
                  exact hw
                · exact (hR.2 y e he (le_of_not_gt hy) (le_of_not_gt houter)).1
            obtain ⟨R, hp, hn⟩ := (_h_xinl_0.and (eventually_cutoff_negative_direction d hd alpha C₀ sigma ha ha1
              hsigma hsq)).exists
            refine ⟨C₀, sigma, R, hC₀, hsigma, hp.1, ?_⟩
            intro y e he
            refine ⟨hp.2 y e he, ?_⟩
            by_cases hy : 1 / 4 < PDE.vecEuclideanNorm (y - e)
            · exact Or.inl (hn.2 y e he hy)
            · right
              have hsmall := le_of_not_gt hy
              have hen : PDE.vecEuclideanNorm e = 1 := by
                unfold PDE.vecEuclideanNorm
                rw [he]
                norm_num
              have htri := PDE.vecEuclideanNorm_add_le (y - e) e
              have hinner : PDE.vecEuclideanNorm y < R := by
                rw [sub_add_cancel, hen] at htri
                linarith
              have _h_xinl_0 : ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e = ansatzTransport alpha (seed alpha C₀ sigma) y e := by
                have hR : 0 < R := (lt_trans (by norm_num) hp.1)
                have hvel : (fun z => cutoffProfile alpha C₀ sigma R z e) =ᶠ[nhds y]
                    (fun z => seed alpha C₀ sigma z e) := by
                  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_lt_const hinner]
                    with z hz
                  exact cutoffProfile_eq_seed alpha C₀ sigma R hR z e hz.le
                have hsphere : (fun z => cutoffProfile alpha C₀ sigma R y z) =
                    (fun z => seed alpha C₀ sigma y z) := by
                  funext z
                  exact cutoffProfile_eq_seed alpha C₀ sigma R hR y z hinner.le
                unfold ansatzTransport
                rw [cutoffProfile_eq_seed alpha C₀ sigma R hR y e hinner.le, hvel.fderiv_eq, hsphere]
              rw [_h_xinl_0]
              exact htransport y e he hsmall
          have hR : 0 < R := lt_trans (by norm_num) hR2
          refine ⟨C₀, sigma, R, hC₀, hsigma, hR2, ?_⟩
          intro q hq
          by_cases hx : q.1 = 0
          · have hv : q.2 ≠ 0 := fun hv => hq (Prod.ext hx hv)
            obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha q.2 hv
            refine ⟨⟨w, ?_⟩, Or.inl ⟨q.2, ?_⟩⟩
            · rw [show q = (0, q.2) from Prod.ext hx rfl,
                geometricProfile_quadratic_zero_position alpha C₀ sigma R hsigma hR q.2 w hv]
              exact hw
            · rw [show q = (0, q.2) from Prod.ext hx rfl,
                geometricProfile_quadratic_zero_position alpha C₀ sigma R hsigma hR q.2 q.2 hv]
              exact radialHessian_radial_neg alpha ha ha1 q.2 hv
          · have hr : 0 < Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) :=
              Real.rpow_pos_of_pos (PDE.vecEuclideanNorm_pos_iff.mpr hx) _
            obtain ⟨⟨w, hw⟩, hneg⟩ := hsign (normalizedVelocity q.1 q.2) (positionDirection q.1)
              (positionDirection_normSq q.1 hx)
            refine ⟨⟨w, ?_⟩, ?_⟩
            · rw [geometricProfile_quadratic_nonzero_position alpha C₀ sigma R hsigma hR q hx]
              exact mul_pos hr hw
            · rcases hneg with ⟨u, hu⟩ | hb
              · left
                refine ⟨u, ?_⟩
                rw [geometricProfile_quadratic_nonzero_position alpha C₀ sigma R hsigma hR q hx]
                exact mul_neg_of_pos_of_neg hr hu
              · right
                have _h_inl_8 : PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q) =
              Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) *
                ansatzTransport alpha (cutoffProfile alpha C₀ sigma R)
                  (normalizedVelocity q.1 q.2) (positionDirection q.1) := by
                    have hq : q ≠ 0 := fun h => hx (congrArg Prod.fst h)
                    have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
                    have hH := (geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR).contDiffAt
                      (hopen.mem_nhds hq)
                    rw [transport_eq_direction, ← fderiv_position_slice _ q.1 q.2 q.2
                      (hH.differentiableAt (by simp))]
                    have heq : (fun x => geometricProfile alpha C₀ sigma R (x, q.2)) =ᶠ[nhds q.1]
                        (fun x => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x q.2) := by
                      filter_upwards [continuous_id.continuousAt.eventually_ne hx] with x hx'
                      change x ≠ 0 at hx'
                      simp only [geometricProfile, ite_eq_right hx']
                    rw [heq.fderiv_eq (𝕜 := ℝ)]
                    apply homogeneousAnsatz_transport alpha _ q.1 q.2 hx
                    exact (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).differentiable
                      (by simp) (normalizedVelocity q.1 q.2, positionDirection q.1)


                rw [_h_inl_8]
                exact mul_pos hr (lt_of_lt_of_le zero_lt_one hb)
        have hR : 0 < R := lt_trans (by norm_num) hR2
        refine ⟨C₀, sigma, R, hC₀, hsigma, hR2, ?_⟩
        intro q hq
        let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
        have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
        have hH := (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR).contDiffAt
          (hopen.mem_nhds hq)
        have hherm := dvv_isHermitian H q hH
        obtain ⟨⟨w, hw⟩, hneg⟩ := hsign q hq
        have hpos : 0 < positiveSpectralMass (dvv H q) := by
          apply positiveSpectralMass_pos_of_direction _ hherm w
          rwa [dvv_quadratic_eq H q w hH]
        refine ⟨hherm, hpos, ?_⟩
        intro hzero
        rcases hneg with ⟨u, hu⟩ | hb
        · have hmn : 0 < negativeSpectralMass (dvv H q) := by
            apply negativeSpectralMass_pos_of_direction _ hherm u
            rwa [dvv_quadratic_eq H q u hH]
          rw [hzero] at hmn
          exact hmn.false.elim
        · exact hb
      have hR : 0 < R := lt_trans (by norm_num) hR2
      let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
      have hH := geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR
      have hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q :=
        fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
      obtain ⟨cminus, lam, Lam, _, hlam, hlam1, hLam1, hbounds, hsolve⟩ : ∃ cminus lam Lam : ℝ, 1 ≤ cminus ∧ 0 < lam ∧ lam ≤ 1 ∧ 1 ≤ Lam ∧
      (∀ q, lam • (1 : PDE.Mat d) ≤ homogeneousSpectralMatrix H cminus q ∧
        homogeneousSpectralMatrix H cminus q ≤ Lam • (1 : PDE.Mat d)) ∧
      (∀ q, q ≠ 0 → matrixContraction (homogeneousSpectralMatrix H cminus q) (dvv H q) =
        PDE.vecDot q.2 (dx H q)) := by
        have hpos := (fun q hq => (hsign q hq).2.1)
        have hzero := (fun q hq => (hsign q hq).2.2)
        let K : Set (XV d) := {q | rho q = 1}
        let M := dvv H
        let b := fun q : XV d => PDE.vecDot q.2 (dx H q)
        have hKnz : ∀ q ∈ K, q ≠ 0 := by
          intro q hq hz
          have hh : rho q = 1 := hq
          simp [hz] at hh
        have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
        have hherm : ∀ q, q ≠ 0 → (M q).IsHermitian :=
          fun q hq => dvv_isHermitian H q (hH.contDiffAt (hopen.mem_nhds hq))
        have hMc : ContinuousOn M K := (continuousOn_dvv_off_origin H hH).mono
          (fun q hq => hKnz q hq)
        have hbc : ContinuousOn b K := (continuousOn_transport_off_origin H hH).mono
          (fun q hq => hKnz q hq)
        have hmp : ContinuousOn (fun q => positiveSpectralMass (M q)) K :=
          continuousOn_positiveSpectralMass M K hMc (fun q hq => hherm q (hKnz q hq))
        have hmn : ContinuousOn (fun q => negativeSpectralMass (M q)) K :=
          continuousOn_positiveSpectralMass (fun q => -M q) K hMc.neg
            (fun q hq => (hherm q (hKnz q hq)).neg)
        have hm0 : ∀ q ∈ K, 0 ≤ negativeSpectralMass (M q) :=
          fun q hq => positiveSpectralMass_nonneg (-M q) (hherm q (hKnz q hq)).neg
        obtain ⟨cminus, hcminus, hnum⟩ : ∃ cminus : ℝ, 1 ≤ cminus ∧ ∀ x ∈ K, 0 < b x + cminus * (fun q => negativeSpectralMass (M q)) x := by
          have hK := (isCompact_unitGaugeShell d)
          let m := (fun q => negativeSpectralMass (M q))
          have hzero := (fun q hq => hzero q (hKnz q hq))
          by_cases hne : K.Nonempty
          · let g := fun x => m x + max 0 (b x)
            have hg : ContinuousOn g K := hmn.add (continuousOn_const.sup hbc)
            have hgpos : ∀ x ∈ K, 0 < g x := by
              intro x hx
              by_cases hmx : m x = 0
              · have hbx := hzero x hx hmx
                simpa [g, hmx, max_eq_right hbx.le] using hbx
              · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hm0 x hx) (Ne.symm hmx))
                  (le_max_left _ _)
            obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hg
            have hd := hgpos x₀ hx₀
            obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image hbc.abs
            let B := max 0 B₀
            have hB : 0 ≤ B := le_max_left _ _
            have hbound : ∀ x ∈ K, |b x| ≤ B := by
              intro x hx
              exact (hB₀ ⟨x, hx, rfl⟩).trans (le_max_right _ _)
            let cminus := 1 + B / g x₀
            have hc : 1 ≤ cminus := by
              dsimp [cminus]
              exact le_add_of_nonneg_right (div_nonneg hB hd.le)
            have hc0 := lt_of_lt_of_le zero_lt_one hc
            have heq : cminus * g x₀ = g x₀ + B := by
              dsimp [cminus]
              field_simp
            refine ⟨cminus, hc, ?_⟩
            intro x hx
            by_cases hbx : 0 < b x
            · exact add_pos_of_pos_of_nonneg hbx (mul_nonneg hc0.le (hm0 x hx))
            · have hmx : g x₀ ≤ m x := by
                have hh := hmin hx
                simpa [g, max_eq_left (le_of_not_gt hbx)] using hh
              have hh : g x₀ + B ≤ cminus * m x := by
                rw [← heq]
                exact mul_le_mul_of_nonneg_left hmx hc0.le
              have hlow : -B ≤ b x := (abs_le.mp (hbound x hx)).1
              linarith
          · refine ⟨1, le_rfl, ?_⟩
            intro x hx
            exact (hne ⟨x, hx⟩).elim
        let w := fun q => (b q + cminus * negativeSpectralMass (M q)) / positiveSpectralMass (M q)
        have hwc : ContinuousOn w K :=
          (hbc.add (continuousOn_const.mul hmn)).div hmp
            (fun q hq => (hpos q (hKnz q hq)).ne')
        obtain ⟨lower, upper, hlo, _, hweights⟩ := exists_positive_bounds_on_compact K
          (isCompact_unitGaugeShell d) w hwc
          (fun q hq => div_pos (hnum q hq) (hpos q (hKnz q hq)))
        let lam := min 1 (min lower cminus)
        let Lam := max 1 (max upper cminus)
        have hlam : 0 < lam := lt_min zero_lt_one
          (lt_min hlo (lt_of_lt_of_le zero_lt_one hcminus))
        have hlam1 : lam ≤ 1 := min_le_left _ _
        have hLam1 : 1 ≤ Lam := le_max_left _ _
        have hbound : ∀ q ∈ K, lam • (1 : PDE.Mat d) ≤ spectralTraceMatrix (M q) (b q) cminus ∧
            spectralTraceMatrix (M q) (b q) cminus ≤ Lam • (1 : PDE.Mat d) := by
          intro q hq
          exact spectralTraceMatrix_uniform_bounds (M q) (hherm q (hKnz q hq)) (b q) cminus
            lower upper (hweights q hq).1 (hweights q hq).2
        refine ⟨cminus, lam, Lam, hcminus, hlam, hlam1, hLam1, ?_, ?_⟩
        · intro q
          by_cases hq : q = 0
          · rw [homogeneousSpectralMatrix, ite_eq_left hq]
            simpa only [one_smul] using
              And.intro (scalar_identity_le (d := d) lam 1 hlam1)
                (scalar_identity_le (d := d) 1 Lam hLam1)
          · have hp : normalizeGauge q ∈ K := rho_normalizeGauge q hq
            rw [homogeneousSpectralMatrix, ite_eq_right hq, normalizedProfileMatrix,
              ite_eq_right hq, normalizedProfileTransport, ite_eq_right hq]
            exact hbound (normalizeGauge q) hp
        · intro q hq
          have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
          let p := normalizeGauge q
          have hpnz : p ≠ 0 := normalizeGauge_ne_zero q hq
          have hMscale : dvv H (dilate (rho q) p) = Real.rpow (rho q) (alpha - 2) • dvv H p := by
            let r := (rho q)
            have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
            ext i k
            let F := fun z => fderiv ℝ H z (0, Pi.single k 1)
            have hF :=
              (hH.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply
                (contDiffOn_const (c := ((0, Pi.single k 1) : XV d)))
            have hhomF : ∀ s : ℝ, 0 < s → ∀ z, z ≠ 0 →
                F (dilate s z) = Real.rpow s (alpha - 1) * F z :=
              fun s hs z hz => homogeneous_velocity_jet alpha H hH hhom s hs z hz _
            have hh := punctured_homogeneous_velocity_jet (alpha - 1) F hF hhomF r hr p hpnz
              (Pi.single i 1)
            have hexp : alpha - 1 - 1 = alpha - 2 := by ring
            simpa only [dvv, dv, Matrix.smul_apply, smul_eq_mul, hexp] using hh
          have hbscale : PDE.vecDot (dilate (rho q) p).2 (dx H (dilate (rho q) p)) =
            Real.rpow (rho q) (alpha - 2) * PDE.vecDot p.2 (dx H p) := by
            let r := (rho q)
            rw [transport_eq_direction, transport_eq_direction]
            have hdir : ((dilate r p).2, (0 : PDE.Vec d)) = r • ((p.2, 0) : XV d) := by
              simp only [dilate, Prod.smul_mk, smul_zero]
            rw [hdir, map_smul, smul_eq_mul, homogeneous_position_jet alpha H hH hhom r hr p hpnz]
            have hp : r * Real.rpow r (alpha - 3) = Real.rpow r (alpha - 2) := by
              simp only [Real.rpow_eq_pow]
              conv_lhs => lhs; rw [← Real.rpow_one r]
              rw [← Real.rpow_add hr]
              congr 1
              ring
            rw [← mul_assoc, hp]
          have _h_xinl_0 : dilate (rho q) (normalizeGauge q) = q := by
              have hr : rho q ≠ 0 := (rho_eq_zero_iff q).not.mpr hq
              rw [normalizeGauge, dilate_mul, mul_inv_cancel₀ hr, dilate_one]


          rw [_h_xinl_0] at hMscale hbscale
          rw [homogeneousSpectralMatrix, ite_eq_right hq, normalizedProfileMatrix,
            ite_eq_right hq, normalizedProfileTransport, ite_eq_right hq, hMscale,
            matrixContraction_smul_right,
            spectral_trace_solver _ (hherm p hpnz) _ _ (hpos p hpnz).ne']
          exact hbscale.symm
      refine ⟨C₀, sigma, R, lam, Lam, homogeneousSpectralMatrix H cminus,
        hC₀, hsigma, hR2, hlam, hlam1.trans hLam1, ?_, hbounds, hsolve⟩
      exact fun i k => measurable_homogeneousSpectralMatrix H hH cminus i k
    have hR : 0 < R := lt_trans (by norm_num) hR2
    let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
    obtain ⟨c, C₁, hc, _, hcompare⟩ : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV (d),
        c * Real.rpow (rho q) alpha ≤ geometricProfile alpha C₀ sigma R q ∧
        geometricProfile alpha C₀ sigma R q ≤ C * Real.rpow (rho q) alpha := by
      let d := (d)
      have hC₀ := hC₀.le
      apply homogeneous_profile_comparison alpha ha (geometricProfile alpha C₀ sigma R)
        (geometricProfile_zero d alpha C₀ sigma R ha)
        (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
        (geometricProfile_pos alpha C₀ sigma R hC₀ hsigma hR)
      exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
    obtain ⟨C₂, hC₂, hgrad⟩ : ∃ C : ℝ, 0 < C ∧ ∀ q : XV (d), q ≠ 0 →
        PDE.vecEuclideanNorm (dv (geometricProfile alpha C₀ sigma R) q) ≤
          C * Real.rpow (rho q) (alpha - 1) := by
      let d := (d)
      apply homogeneous_velocity_gradient_bound alpha (geometricProfile alpha C₀ sigma R)
        (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
      exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
    let C := max C₁ C₂
    have hC : 0 < C := lt_of_lt_of_le hC₂ (le_max_right _ _)
    refine ⟨lam, Lam, c, C, A, H, hlam, hlamLam, hc, hC, hmeas, helliptic,
      geometricProfile_zero d alpha C₀ sigma R ha,
      geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR, ?_, ?_, ?_, ?_⟩
    · exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
    · intro q
      change c * Real.rpow (rho q) alpha ≤ H q ∧ H q ≤ C * Real.rpow (rho q) alpha
      refine ⟨(hcompare q).1, (hcompare q).2.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (rho_nonneg q) _)
    · exact hsolve
    · intro q hq
      change PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1)
      exact (hgrad q hq).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (rho_nonneg q) _))
  exact ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
    hhom, hcomp, hsmooth, heq, hgrad⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
