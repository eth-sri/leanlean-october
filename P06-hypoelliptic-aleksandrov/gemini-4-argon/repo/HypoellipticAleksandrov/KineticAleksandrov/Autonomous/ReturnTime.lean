module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIteration
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTimeScaling
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatch
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIterationAbsorption
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIterationCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryBoxes
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryDistance
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatchModulus
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatchPoint
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatchRadius
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IsLUB
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPower
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus

/-! # The canonical full-space return-time comparison

The only conditional analytic input beyond the classical inputs is the preliminary p-six
admissibility statement. The constant is chosen before coefficients, data, times and points.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory
open Holder
open Filter
open scoped Topology
open Finset
open SectionTwo Evolution TheoremA HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/- Smooth terminal data satisfy the return comparison at every kinetic scale. -/
theorem return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v) := by
  obtain ⟨C, hC, hsmooth⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ t s X v : ℝ, 0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v) := by
      obtain ⟨C, hC, hunit⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ v : ℝ, |v| ≤ 1 →
      ∀ zStar ∈ returnFutureRegion, u (point 1 0 v) ≤ C * u zStar := by
        obtain ⟨alpha, beta, c₀, ha, _ha1, hb, hc, hheight⟩ : ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
      ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
      1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
      ∀ zStar ∈ returnFutureRegion,
      0 < sSup (u '' returnBox v b) →
      c₀ * (b - a) ^ beta * sSup (u '' returnBox v a) ^ (1 + beta / alpha) *
        sSup (u '' returnBox v b) ^ (-beta / alpha) ≤ u zStar := by
          obtain ⟨alpha, beta, c₀, ha, ha1, hb, hc, hpoint⟩ : ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
              ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
              IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
              1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
              ∀ z zStar : Point, z ∈ returnBox v a → zStar ∈ returnFutureRegion →
              0 < sSup (u '' returnBox v b) →
              c₀ * (b - a) ^ beta * (u z) ^ (1 + beta / alpha) *
                sSup (u '' returnBox v b) ^ (-beta / alpha) ≤ u zStar := by
            obtain ⟨alpha, D, ha, ha1, hD, hmod⟩ : ∃ alpha D : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < D ∧
              ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
              IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
              1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
              ∀ (z p : Point) (ell : ℝ), z ∈ returnBox v a →
              0 < ell → ell ≤ (b - a) / 8192 →
              p ∈ closure (backwardCylinder z ell) →
              |u z - u p| ≤ D * sSup (u '' returnBox v b) *
                (ell / ((b - a) / 8192)) ^ alpha := by
              obtain ⟨C_A, _hCA, hadm⟩ := hp6
              obtain ⟨alpha, C, halpha, halpha1, hholder⟩ :=
                kinetic_holder_of_aleksandrov_aux 1 (by omega) lam Lam 6 C_A
                  hlam hLam (by norm_num)
              let D := max C 1 * (4 : ℝ) ^ alpha
              have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
              refine ⟨alpha, D, halpha, halpha1, mul_pos hCpos (by positivity), ?_⟩
              intro A u hu a b v ha hab hb hv z p ell hz hell hellh hp
              let h := (b - a) / 8192
              let mid := (a + b) / 2
              let O := returnBox v b
              let K : Set Point := {z, p}
              let E := holderNeighbourhood h K
              have hh : 0 < h := by dsimp [h]; positivity
              have hamid : a < mid := by dsimp [mid]; linarith
              have hmidb : mid < b := by dsimp [mid]; linarith
              have hpcl : p ∈ closure (backwardCylinder z (2 * h)) :=
                closure_mono (backwardCylinder_radius_mono z hell (by dsimp [h]; linarith)) hp
              have hinner : closure (backwardCylinder z (2 * h)) ⊆ returnBox v mid := by
                have he : 2 * h = 2 * ((mid - a) / 4096) := by dsimp [h, mid]; ring
                rw [he]
                exact returnBox_cylinder_subset v a mid hv ha hamid (by dsimp [mid]; linarith) z hz
              have hzmid : z ∈ returnBox v mid := returnBox_mono v hamid.le hz
              have hpmid : p ∈ returnBox v mid := hinner hpcl
              have hKmid : K ⊆ returnBox v mid := by
                intro q hq
                rcases hq with hq | hq <;> subst q
                · exact hzmid
                · exact hpmid
              have hQ : ∀ q ∈ K, closure (backwardCylinder q (2 * h)) ⊆ O := by
                intro q hq
                have he : 2 * h = 2 * ((b - mid) / 4096) := by dsimp [h, mid]; ring
                rw [he]
                exact returnBox_cylinder_subset v mid b hv (by dsimp [mid]; linarith)
                  hmidb hb q (hKmid hq)
              have hKO : K ⊆ O := hKmid.trans (returnBox_mono v hmidb.le)
              have hOpos : O ⊆ {q | 0 < q.time} := by
                intro q hq
                have hr := returnBox_subset_reference v b hv hb hq
                change 0 < q.time
                linarith [hr.1.1]
              have hO : IsOpen (returnBox v b) := by
                  exact (
                (isOpen_lt ((continuous_time.sub continuous_const).abs) continuous_const).inter
                    ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
                      continuous_const).inter (isOpen_lt
                        (PDE.continuous_vecEuclideanNorm.comp (continuous_velocity.sub continuous_const))
                        continuous_const))
                )
              have hreg : IsKineticC112On u O := by
                rcases hu.2.2.1 with ⟨hc, ht, hx, hv, hct, hcx, hcv, hcvv⟩
                exact ⟨hc.mono hOpos, fun q hq => ht q (hOpos hq), fun q hq => hx q (hOpos hq),
                  fun q hq => hv q (hOpos hq), hct.mono hOpos, hcx.mono hOpos,
                  hcv.mono hOpos, hcvv.mono hOpos⟩
              have hadmiss : IsAdmissibleSolution (autonomousCoefficient A.a) O 6 C_A u :=
                hadm A O hO u hreg
                  (ae_restrict_of_forall_mem hO.measurableSet (fun q hq => hu.2.2.2 q (hOpos hq)))
              obtain ⟨M, hM⟩ := hu.1
              have hbounded : ∀ q ∈ O, |u q| ≤ M := fun q hq => hM q (hOpos hq)
              have hEll := autonomous_fullElliptic A
              have hmod := hholder _ hEll.1 hEll.2.1 hEll.2.2.1 hEll.2.2.2 O hO u
                ⟨M, hbounded⟩ hadmiss K hKO (isCompact_singleton.insert z) h hh hQ
                z (by simp [K]) p (by simp [K])
              have hEO : E ⊆ O := by
                intro q hq
                simp only [E, holderNeighbourhood, mem_iUnion] at hq
                obtain ⟨w, hw, hq⟩ := hq
                exact hQ w hw (subset_closure hq)
              have hEne : E.Nonempty := by
                obtain ⟨q, hq⟩ := backwardCylinder_nonempty z (by positivity : 0 < 2 * h)
                exact ⟨q, mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨by simp [K], hq⟩⟩⟩
              have habO : BddAbove (u '' O) := ⟨M, by
                rintro _ ⟨q, hq, rfl⟩
                exact (le_abs_self _).trans (hbounded q hq)⟩
              have habE : BddAbove (u '' E) := habO.mono (image_mono hEO)
              have hbbE : BddBelow (u '' E) := ⟨0, by
                rintro _ ⟨q, hq, rfl⟩
                exact hu.2.1 q (hOpos (hEO hq))⟩
              have hosc0 : 0 ≤ oscillationOn u E := oscillationOn_nonneg hEne habE hbbE
              have hosc : oscillationOn u E ≤ sSup (u '' O) := by
                have hs : sSup (u '' E) ≤ sSup (u '' O) :=
                  csSup_le (hEne.image u) (fun _ hx => le_csSup habO (image_mono hEO hx))
                have hi : 0 ≤ sInf (u '' E) := le_csInf (hEne.image u) (by
                  rintro _ ⟨q, hq, rfl⟩
                  exact hu.2.1 q (hOpos (hEO hq)))
                unfold oscillationOn
                linarith
              have hdist : quasiDistance z p ≤ 4 * ell := by
                obtain ⟨ht, hv, hx⟩ := returnCylinder_bounds z p ell hell hp
                have hinv : relativePosition p z = -relativePosition z p +
                    (p.time - z.time) • (p.velocity - z.velocity) := by
                  unfold relativePosition
                  module
                have hxi := PDE.vecEuclideanNorm_add_le (-relativePosition z p)
                  ((p.time - z.time) • (p.velocity - z.velocity))
                rw [PDE.vecEuclideanNorm_neg, PDE.vecEuclideanNorm_smul, ← hinv] at hxi
                have hmul := mul_le_mul ht hv (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg ell)
                have hxinv : PDE.vecEuclideanNorm (relativePosition p z) ≤ 2 * ell ^ 3 := by
                  nlinarith
                have hmax : max (PDE.vecEuclideanNorm (relativePosition z p))
                    (PDE.vecEuclideanNorm (relativePosition p z)) ≤ (2 * ell) ^ 3 := by
                  apply max_le <;> nlinarith [pow_pos hell 3]
                have hmax0 : 0 ≤ max (PDE.vecEuclideanNorm (relativePosition z p))
                    (PDE.vecEuclideanNorm (relativePosition p z)) :=
                  le_max_of_le_left (PDE.vecEuclideanNorm_nonneg _)
                have hroot := Real.rpow_le_rpow hmax0 hmax (by norm_num : (0 : ℝ) ≤ 1 / 3)
                have hcube : ((2 * ell) ^ 3) ^ (1 / 3 : ℝ) = 2 * ell := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * ell)]
                  norm_num
                rw [hcube] at hroot
                have htime : Real.sqrt |z.time - p.time| ≤ ell := by
                  rw [abs_sub_comm]
                  exact (Real.sqrt_le_iff).mpr ⟨hell.le, ht⟩
                unfold quasiDistance
                rw [PDE.vecEuclideanNorm_sub_comm z.velocity p.velocity]
                dsimp only [relativePosition] at hroot
                exact (add_le_add (add_le_add htime hv) hroot).trans_eq (by ring)
              have hd0 := quasiDistance_nonneg z p
              have hratio : quasiDistance z p / h ≤ 4 * (ell / h) := by
                exact (div_le_div_of_nonneg_right hdist hh.le).trans_eq (by ring)
              have hrpow := Real.rpow_le_rpow (div_nonneg hd0 hh.le) hratio halpha.le
              rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (div_nonneg hell.le hh.le)] at hrpow
              have h₁ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left C 1) hosc0)
                (Real.rpow_nonneg (div_nonneg hd0 hh.le) alpha)
              have h₂ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hosc hCpos.le)
                (Real.rpow_nonneg (div_nonneg hd0 hh.le) alpha)
              have hMb0 : 0 ≤ sSup (u '' O) := hosc0.trans hosc
              have h₃ := mul_le_mul_of_nonneg_left hrpow (mul_nonneg hCpos.le hMb0)
              exact (hmod.trans (h₁.trans (h₂.trans h₃))).trans_eq (by dsimp [D, h, O]; ring)
            obtain ⟨beta, cp, hb, hcp, hpatch⟩ := return_patch_power lam Lam hlam hLam hp6
            let δ := returnHolderRadiusFactor alpha D
            let c₀ := (cp * δ ^ beta / 2) / (8192 : ℝ) ^ beta
            have hδ := returnHolderRadiusFactor_bounds alpha D ha hD
            have hδpos := hδ.1
            have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
            refine ⟨alpha, beta, c₀, ha, ha1, hb, hc₀, ?_⟩
            intro A u hu a b v habase hab hb1 hv z zStar hz hstar hMb
            have hzref := returnBox_subset_reference v a hv (by linarith) hz
            have huz0 := hu.2.1 z (by linarith [hzref.1.1])
            by_cases huz : u z = 0
            · rw [huz, Real.zero_rpow (by positivity : (1 + beta / alpha) ≠ 0), mul_zero, zero_mul]
              exact hu.2.1 zStar (by linarith [hstar.1.1])
            have huzpos : 0 < u z := lt_of_le_of_ne huz0 (Ne.symm huz)
            let M := sSup (u '' returnBox v b)
            let h := (b - a) / 8192
            let ell := δ * h * (u z / M) ^ (1 / alpha)
            have hh : 0 < h := by dsimp [h]; positivity
            have hh1 : h ≤ 1 := by dsimp [h]; linarith
            have hOpos : returnBox v b ⊆ {q | 0 < q.time} := by
              intro q hq
              have hqref := returnBox_subset_reference v b hv hb1 hq
              change 0 < q.time
              linarith [hqref.1.1]
            obtain ⟨B, hB⟩ := hu.1
            have hbounded : BddAbove (u '' returnBox v b) := ⟨B, by
              rintro _ ⟨q, hq, rfl⟩
              exact (le_abs_self _).trans (hB q (hOpos hq))⟩
            have huzM := le_csSup hbounded
              (mem_image_of_mem u (returnBox_mono v hab.le hz))
            have hradius := return_holder_radius alpha D h (u z) M ha hD hh huzpos hMb huzM
            change 0 < ell ∧ ell ≤ h ∧ D * M * (ell / h) ^ alpha ≤ u z / 2 at hradius
            have hlower : ∀ q ∈ backwardCylinder z ell, u z / 2 ≤ u q := by
              intro q hq
              have hc := hmod A u hu a b v habase hab hb1 hv z q ell hz
                hradius.1 hradius.2.1 (subset_closure hq)
              have hdiff := hc.trans hradius.2.2
              linarith [(abs_le.mp hdiff).2]
            have hheight := hpatch A u hu ell (u z / 2) z zStar hradius.1
              (hradius.2.1.trans hh1) (by positivity) hzref hstar hlower
            have he : cp * (δ * h * ((u z) / M) ^ (1 / alpha)) ^ beta * ((u z) / 2) =
              (cp * δ ^ beta / 2) * h ^ beta * (u z) ^ (1 + beta / alpha) * M ^ (-beta / alpha) := by
              let value := (u z)
              have hδ := hδ.1.le
              have hh := hh.le
              rw [Real.mul_rpow (mul_nonneg hδ hh) (Real.rpow_nonneg (div_nonneg huzpos.le hMb.le) _),
                Real.mul_rpow hδ hh, ← Real.rpow_mul (div_nonneg huzpos.le hMb.le)]
              have he : 1 / alpha * beta = beta / alpha := by ring
              rw [he, Real.div_rpow huzpos.le hMb.le, Real.rpow_add huzpos,
                Real.rpow_one, neg_div, Real.rpow_neg hMb.le]
              ring
            have hhpower : h ^ beta = (b - a) ^ beta / (8192 : ℝ) ^ beta :=
              Real.div_rpow (by linarith) (by norm_num) beta
            change cp * (δ * h * (u z / M) ^ (1 / alpha)) ^ beta * (u z / 2) ≤ u zStar at hheight
            rw [he, hhpower] at hheight
            convert hheight using 1; dsimp [c₀, M]; ring
          refine ⟨alpha, beta, c₀, ha, ha1, hb, hc, ?_⟩
          intro A u hu a b v habase hab hb1 hv zStar hstar hMb
          have hne : (u '' returnBox v a).Nonempty :=
            ⟨u (point 1 0 v), mem_image_of_mem u (returnBox_center v a (by linarith))⟩
          obtain ⟨M, hM⟩ := hu.1
          have hbounded : BddAbove (u '' returnBox v a) := ⟨M, by
            rintro _ ⟨q, hq, rfl⟩
            have hqref := returnBox_subset_reference v a hv (by linarith) hq
            exact (le_abs_self _).trans (hM q (by linarith [hqref.1.1]))⟩
          obtain ⟨f, _hmono, hlim, hf⟩ := exists_seq_tendsto_sSup hne hbounded
          let g : ℝ → ℝ := fun x => c₀ * (b - a) ^ beta * x ^ (1 + beta / alpha) *
            sSup (u '' returnBox v b) ^ (-beta / alpha)
          have hg : Continuous g :=
            ((Real.continuous_rpow_const (by positivity : 0 ≤ 1 + beta / alpha)).const_mul
              (c₀ * (b - a) ^ beta)).mul_const _
          have hseq : ∀ n, g (f n) ≤ u zStar := by
            intro n
            obtain ⟨z, hz, hzf⟩ := hf n
            rw [← hzf]
            exact hpoint A u hu a b v habase hab hb1 hv z zStar hz hstar hMb
          exact le_of_tendsto (hg.continuousAt.tendsto.comp hlim) (Eventually.of_forall hseq)
        let r := (2 : ℝ) ^ beta
        let eps := 1 / (2 * r)
        let K := (c₀ * eps ^ (beta / alpha))⁻¹
        let C := 2 * K * (4 : ℝ) ^ beta
        have hr : 0 < r := by dsimp [r]; positivity
        have hr1 : 1 ≤ r := Real.one_le_rpow (by norm_num) hb.le
        have heps : 0 < eps := by dsimp [eps]; positivity
        have heps1 : eps < 1 := by
          apply (div_lt_one (by positivity : 0 < 2 * r)).mpr
          linarith
        have her : eps * r = 1 / 2 := by dsimp [eps]; field_simp
        have hK : 0 < K := by dsimp [K]; positivity
        have hC : 0 < C := by dsimp [C]; positivity
        refine ⟨C, hC, ?_⟩
        intro A u hu v hv zStar hstar
        obtain ⟨M, hM⟩ := hu.1
        have hprops (R : ℝ) (hRlo : 1 / 2 ≤ R) (hRhi : R ≤ 1) :
            BddAbove (u '' returnBox v R) ∧ 0 ≤ sSup (u '' returnBox v R) ∧
              sSup (u '' returnBox v R) ≤ M := by
          have hpos : returnBox v R ⊆ {q | 0 < q.time} := by
            intro q hq
            have href := returnBox_subset_reference v R hv hRhi hq
            change 0 < q.time
            linarith [href.1.1]
          have hbd : BddAbove (u '' returnBox v R) := ⟨M, by
            rintro _ ⟨q, hq, rfl⟩
            exact (le_abs_self _).trans (hM q (hpos hq))⟩
          have hcenter := returnBox_center v R (by linarith)
          have hne := (show (returnBox v R).Nonempty from ⟨point 1 0 v, hcenter⟩).image u
          exact ⟨hbd, (hu.2.1 _ (by norm_num [point])).trans
            (le_csSup hbd (mem_image_of_mem u hcenter)), csSup_le hne (by
              rintro _ ⟨q, hq, rfl⟩
              exact (le_abs_self _).trans (hM q (hpos hq)))⟩
        let f : ℕ → ℝ := fun n => sSup (u '' returnBox v (returnIterationRadius n))
        have hf0 (n : ℕ) : 0 ≤ f n :=
          (hprops _ (returnIterationRadius_bounds n).1 (returnIterationRadius_bounds n).2.le).2.1
        have hfM (n : ℕ) : f n ≤ M :=
          (hprops _ (returnIterationRadius_bounds n).1 (returnIterationRadius_bounds n).2.le).2.2
        have hU := hu.2.1 zStar (by linarith [hstar.1.1])
        have hstep (n : ℕ) : f n ≤ eps * f (n + 1) +
            (K * (4 : ℝ) ^ beta * u zStar) * r ^ n := by
          have hgap : 0 < returnIterationRadius (n + 1) - returnIterationRadius n := by
            rw [returnIterationRadius_gap]
            positivity
          have hfmono : f n ≤ f (n + 1) := by
            apply csSup_le
            · exact ⟨u (point 1 0 v), mem_image_of_mem u (returnBox_center v _
                (by linarith [(returnIterationRadius_bounds n).1]))⟩
            · intro x hx
              exact le_csSup (hprops _ (returnIterationRadius_bounds (n + 1)).1
                (returnIterationRadius_bounds (n + 1)).2.le).1
                (image_mono (returnBox_mono v (by linarith)) hx)
          have hh := return_height_absorption beta (beta / alpha) c₀ eps
            (returnIterationRadius (n + 1) - returnIterationRadius n) (f n) (f (n + 1))
            (u zStar) (by positivity) hc heps hgap (hf0 n) hfmono hU
            (fun hMb => by
              simpa only [f, neg_div] using hheight A u hu _ _ v (returnIterationRadius_bounds n).1
                (by linarith) (returnIterationRadius_bounds (n + 1)).2.le hv zStar hstar hMb)
          rw [returnIterationRadius_gap_power] at hh
          convert hh using 1; dsimp [K, r]; ring
        have hbound : f 0 ≤ (K * (4 : ℝ) ^ beta * u zStar) / (1 - eps * r) := by
          let B := (K * (4 : ℝ) ^ beta * u zStar)
          have hq := heps.le
          have hr := hr.le
          have hqr : eps * r < 1 := by
            rw [her]; norm_num
          have hB : 0 ≤ (K * (4 : ℝ) ^ beta * u zStar) := by
            positivity
          have hsum (N : ℕ) : (∑ j ∈ range N, (eps * r) ^ j) ≤ 1 / (1 - eps * r) := by
            simpa only [Nat.Ico_zero_eq_range, pow_zero] using
              (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (mul_nonneg hq hr) hqr)
          have hN (N : ℕ) : f 0 ≤ eps ^ N * M + B / (1 - eps * r) := by
            have h := return_recurrence_substitution f eps r B hq hstep 0 N
            simp only [zero_add, pow_zero, mul_one] at h
            apply h.trans
            exact (add_le_add
              (mul_le_mul_of_nonneg_left (hfM N) (pow_nonneg hq N))
              (mul_le_mul_of_nonneg_left (hsum N) hB)).trans_eq (by ring)
          have ht : Tendsto (fun N : ℕ => eps ^ N * M + B / (1 - eps * r)) atTop
              (𝓝 (B / (1 - eps * r))) := by
            simpa only [zero_mul, zero_add] using
              ((tendsto_pow_atTop_nhds_zero_of_lt_one hq heps1).mul_const M).add_const
                (B / (1 - eps * r))
          exact ge_of_tendsto ht (Eventually.of_forall hN)
        rw [her] at hbound
        have hcenter : u (point 1 0 v) ≤ f 0 :=
          le_csSup (hprops _ (returnIterationRadius_bounds 0).1
            (returnIterationRadius_bounds 0).2.le).1
            (mem_image_of_mem u (returnBox_center v _ (by norm_num [returnIterationRadius])))
        exact (hcenter.trans hbound).trans_eq (by dsimp [C]; ring)
      refine ⟨C, hC, ?_⟩
      intro A F hF0 hF t s X v ht hs hs1 hv
      let r := Real.sqrt t
      have hr : 0 < r := Real.sqrt_pos.mpr ht
      have hr2 : r ^ 2 = t := Real.sq_sqrt ht.le
      have hvn : |v / r| ≤ 1 := by
        rw [abs_div, abs_of_pos hr]
        exact (div_le_one hr).mpr hv
      have hslo : 2 ≤ s / t := (le_div_iff₀ ht).mpr (by linarith)
      have hshi : s / t ≤ 3 := (div_le_iff₀ ht).mpr hs1
      have hspos : 0 < s / t := by linarith
      obtain ⟨U, hu, hrep⟩ : ∃ U : Point → ℝ, IsNonnegativeHomogeneousSolution (returnReflectedCoefficient (returnScaledCoefficient A r X)) U ∧ ∀ p : Point, 0 < p.time → U p = S hH hLE hlam hLam A (r ^ 2 * p.time) F (X - r ^ 3 * p.position 0, r * p.velocity 0) := by
        let E := fullSpaceEvolution hH hLE hlam hLam A
        let G := physicalTerminalDatum (scalarTerminalDatum F)
        have hG :=
          (scalarTerminalDatum_smooth F hF).comp (contDiff_snd.prodMk contDiff_fst)
        obtain ⟨w, hw, hrep⟩ := fullspace_bounded_smooth_solution hH hlam hLam A E
          (fullSpaceEvolution_spec hH hLE hlam hLam A) 0 G hG
        let Φ := returnScaling r hr X
        let W := w ∘ Φ.point
        let U := W ∘ autonomousReversal ∘ autonomousPositionReflection
        have heq (p : Point) (hp : 0 < p.time) :
            U p = S hH hLE hlam hLam A (r ^ 2 * p.time) F
              (X - r ^ 3 * p.position 0, r * p.velocity 0) := by
          have ht : 0 ≤ r ^ 2 * p.time := by positivity
          have hpoint : Φ.point (autonomousReversal (autonomousPositionReflection p)) =
              ⟨-(r ^ 2 * p.time), fun _ => r * p.velocity 0,
                fun _ => X - r ^ 3 * p.position 0⟩ := by
            apply KineticPoint.ext
            · simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
                Scaling.KineticAffineScaling.time, autonomousReversal, autonomousPositionReflection]
            · funext i
              rw [Fin.eq_zero i]
              simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
                Scaling.KineticAffineScaling.position, autonomousReversal, autonomousPositionReflection]
            · funext i
              rw [Fin.eq_zero i]
              simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
                Scaling.KineticAffineScaling.transport, autonomousReversal,
                autonomousPositionReflection, sub_eq_add_neg]
          dsimp only [U, W, Function.comp_apply]
          rw [hpoint]
          unfold S fullSpaceAction
          split
          · exact hrep (wholeSpaceQuery (-(r ^ 2 * p.time)) 0 (neg_nonpos.mpr ht)
            (fun _ => r * p.velocity 0) (fun _ => X - r ^ 3 * p.position 0)) rfl
          · rename_i h
            exact False.elim (h ht)
        let O : Set Point := {p | 0 < p.time}
        let T : EvolutionVec 1 → ℝ × (PDE.Vec 1 × PDE.Vec 1) := fun q =>
          (-(r ^ 2 * timeCoord 1 q), r • transportedCoord 1 q,
            (fun _ => X) - r ^ 3 • diffusedCoord 1 q)
        have hT : ContDiff ℝ (⊤ : ℕ∞) T := by unfold T; fun_prop
        have hmaps : MapsTo T (evolutionHomeomorph 1 ⁻¹' O)
            (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
          intro q hq
          refine ⟨?_, ?_⟩
          · change -(r ^ 2 * timeCoord 1 q) < 0
            change 0 < timeCoord 1 q at hq
            nlinarith [sq_pos_of_pos hr]
          · change r • transportedCoord 1 q ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
            rw [movingDomain_wholeSpace]
            trivial
        have hraw := hw.2.2.1.comp hT.contDiffOn hmaps
        have hreg : IsKineticC112On U O := by
          apply isKineticC112On_of_contDiffOn (isOpen_lt continuous_const continuous_time)
          convert hraw using 1
          funext q
          dsimp [U, W, Φ, returnScaling, Scaling.KineticAffineScaling.point,
            Scaling.KineticAffineScaling.time, Scaling.KineticAffineScaling.position,
            Scaling.KineticAffineScaling.transport, autonomousReversal,
            autonomousPositionReflection, T]
          congr 1
          apply KineticPoint.ext
          · change 0 + r ^ 2 * (-q 0) = -(r ^ 2 * q 0)
            ring
          · funext i
            change 0 + r * transportedCoord 1 q i = r * transportedCoord 1 q i
            ring
          · funext i
            change X + (r ^ 2 * -q 0) * 0 + r ^ 3 * -(diffusedCoord 1 q i) =
              X - r ^ 3 * diffusedCoord 1 q i
            ring
        obtain ⟨M, hM, hbound⟩ := F.exists_bound
        refine ⟨U, ⟨⟨M, ?_⟩, ?_, hreg, ?_⟩, heq⟩
        · intro p hp
          rw [heq p hp, S_eq_integral hH hLE hlam hLam A _ (by positivity)]
          exact abs_integral_boundedBorel_le F _
            (Kphysical_mass_one hH hLE hlam hLam A _ (by positivity) _).le hM hbound
        · intro p hp
          rw [heq p hp, S_eq_integral hH hLE hlam hLam A _ (by positivity)]
          exact integral_nonneg hF0
        · intro p hp
          change autonomousScalarOperator (reflectedAutonomous (returnScaledCoefficient A r X).a)
            ((W ∘ autonomousReversal) ∘ autonomousPositionReflection) p = 0
          have _h_xinl_0 (a : ℝ → ℝ → ℝ) (u p) : autonomousGeneratorResidual a (u ∘ autonomousReversal) p = -transportedForwardOperator (evolutionCoefficient a) (identityDrift 1) u (autonomousReversal p) := by
            rw [autonomousGeneratorResidual, transportedForwardOperator_apply]
            have ht : kineticTimeDerivative (u ∘ autonomousReversal) p =
                -kineticTimeDerivative u (autonomousReversal p) :=
              deriv_comp_neg (fun r => u ⟨r, p.velocity, p.position⟩) p.time
            rw [ht]
            simp only [matrixContraction, Fin.sum_univ_one, fullKineticCoefficientAt,
              evolutionCoefficient, PDE.vecDot, identityDrift]
            change -kineticTimeDerivative u (autonomousReversal p) -
                p.velocity 0 * kineticVelocityGradient u (autonomousReversal p) 0 -
                a (p.position 0) (p.velocity 0) * diffusedHessian u (autonomousReversal p) 0 0 = _
            dsimp only [autonomousReversal, id_eq]
            ring
          rw [autonomous_generator_positionReflection, _h_xinl_0]
          let q := autonomousReversal (autonomousPositionReflection p)
          have hq : Φ.point q ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) 0 := by
            refine ⟨?_, ?_⟩
            · change 0 + r ^ 2 * (-p.time) < 0
              nlinarith [sq_pos_of_pos hr]
            · change (Φ.point q).position ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
              rw [movingDomain_wholeSpace]
              trivial
          have hrawmem : Scaling.rawPoint (Φ.point q) ∈
              evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0 := hq
          have hopen : IsOpen (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
            have he : evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0 =
                {x : ℝ × (PDE.Vec 1 × PDE.Vec 1) | x.1 < 0} := by
              ext x
              simp [evolutionPastInteriorRaw, autonomousWholeDomain, movingDomain]
            rw [he]
            exact isOpen_lt continuous_fst continuous_const
          have hw2 := (hw.2.2.1.contDiffAt (hopen.mem_nhds hrawmem)).of_le
            (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
          have hscaled := Scaling.KineticAffineScaling.transportedForwardOperator_comp_point (Φ := Φ)
            (u := w) (p := q) (evolutionCoefficient A.a) (identityDrift 1) hw2
          have _h_xinl_0 : (returnScaling r hr X).coefficient (evolutionCoefficient A.a) = evolutionCoefficient (returnScaledCoefficient A r X).a := by
            ext s y z i j
            simp [Scaling.KineticAffineScaling.coefficient, Scaling.KineticAffineScaling.time,
              Scaling.KineticAffineScaling.position, Scaling.KineticAffineScaling.transport,
              returnScaling, evolutionCoefficient, returnScaledCoefficient, hr.ne']
          rw [_h_xinl_0, returnScaling_drift r hr X] at hscaled
          rw [show transportedForwardOperator (evolutionCoefficient (returnScaledCoefficient A r X).a)
              (identityDrift 1) W q = r ^ 2 *
                transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) w
                  (Φ.point q) from hscaled,
            hw.2.2.2.1 _ hq, mul_zero, neg_zero]
      have hstar : point (s / t) 0 (v / r) ∈ returnFutureRegion :=
        ⟨⟨hslo, hshi⟩, by simp [point, return_norm_one],
          by simpa only [point, return_norm_one] using hvn.trans (by norm_num : (1 : ℝ) ≤ 2)⟩
      have h := hunit _ U hu (v / r) hvn _ hstar
      rw [hrep _ (by norm_num [point]), hrep _ hspos] at h
      have hrv : r * (v / r) = v := by field_simp
      have hst : t * (s / t) = s := by field_simp
      simpa only [point, hr2, mul_one, mul_zero, sub_zero, hrv, hst] using h

    /- Bounded nonnegative Borel data satisfy the same full-space return comparison. -/
  refine ⟨C, hC, ?_⟩
  intro A F hF0 t s X v ht hs hs1 hv
  apply return_time_borel_of_smooth_tests hH hLE hlam hLam C hC.le A t s ht.le
    (by linarith) (X, v) ?_ F hF0
  intro G hG0 hG
  exact hsmooth A G hG0 hG t s X v ht hs hs1 hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
