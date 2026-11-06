module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryDistance
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic

/-! # The local Holder modulus relative to the larger return-box supremum -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder

/-- The concrete return boxes increase with their radius parameter. -/
theorem returnBox_mono (v : ℝ) {a b : ℝ} (hab : a ≤ b) :
    returnBox v a ⊆ returnBox v b := by
  intro p hp
  exact ⟨hp.1.trans_le (by linarith), hp.2.1.trans_le (by linarith),
    hp.2.2.trans_le (by linarith)⟩

/-- The generic Holder theorem gives a modulus measured against the larger supremum. -/
theorem return_holder_modulus (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ alpha D : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < D ∧
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
  let D := max C 1 * (4) ^ alpha
  have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨alpha, D, halpha, halpha1, mul_pos hCpos (by positivity), ?_⟩
  intro A u hu a b v ha hab hb hv z p ell hz hell hellh hp
  let h := (b - a) / 8192
  let mid := (a + b) / 2
  let O := returnBox v b
  let K : Set Point := {z, p}
  let E := holderNeighbourhood h K
  have hh : 0 < h := by positivity
  have hamid : a < mid := by grind
  have hmidb : mid < b := by grind
  have hpcl : p ∈ closure (backwardCylinder z (2 * h)) :=
    closure_mono (backwardCylinder_radius_mono z hell (by grind)) hp
  have hinner : closure (backwardCylinder z (2 * h)) ⊆ returnBox v mid := by
    have he : 2 * h = 2 * ((mid - a) / 4096) := by ring
    rw [he]
    exact returnBox_cylinder_subset v a mid hv ha hamid (by linarith) z hz
  have hzmid  := returnBox_mono v hamid.le hz
  have hpmid : p ∈ returnBox v mid := hinner hpcl
  have hKmid : K ⊆ returnBox v mid := by
    grind
  have hQ : ∀ q ∈ K, closure (backwardCylinder q (2 * h)) ⊆ O := by
    intro q hq
    have he : 2 * h = 2 * ((b - mid) / 4096) := by ring
    rw [he]
    exact returnBox_cylinder_subset v mid b hv (by linarith)
      hmidb hb q (hKmid hq)
  have hKO : K ⊆ O := hKmid.trans (returnBox_mono v hmidb.le)
  have hOpos : O ⊆ {q | 0 < q.time} := by
    intro q hq
    have hr := returnBox_subset_reference v b hv hb hq
    change 0 < q.time
    linarith [hr.1.1]
  have hO := returnBox_isOpen v b
  have hreg : IsKineticC112On u O := by
    rcases hu.2.2.1 with ⟨hc, ht, hx, hv, hct, hcx, hcv, hcvv⟩
    exact ⟨hc.mono hOpos, fun q hq => ht q (hOpos hq), fun q hq => hx q (hOpos hq),
      fun q hq => hv q (hOpos hq), hct.mono hOpos, hcx.mono hOpos,
      hcv.mono hOpos, hcvv.mono hOpos⟩
  have hadmiss : IsAdmissibleSolution _ O 6 C_A u :=
    hadm A O hO u hreg
      (ae_restrict_of_forall_mem hO.measurableSet (fun q hq => hu.2.2.2 q (hOpos hq)))
  obtain ⟨M, hM⟩ := hu.1
  have hbounded  := fun q hq => hM q (hOpos hq)
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
  have hosc0  := oscillationOn_nonneg hEne habE hbbE
  have hosc : oscillationOn u E ≤ sSup (u '' O) := by
    have hs : sSup _ ≤ sSup (u '' O) :=
      csSup_le (hEne.image u) (fun _ hx => le_csSup habO (image_mono hEO hx))
    have hi : 0 ≤ sInf (u '' E) := le_csInf (hEne.image u) (by
      rintro _ ⟨q, hq, rfl⟩
      exact hu.2.1 q (hOpos (hEO hq)))
    unfold oscillationOn
    linarith
  have hdist := returnCylinder_distance z p ell hell hp
  have hd0 := quasiDistance_nonneg z p
  have hratio : quasiDistance z p / h ≤ 4 * (ell / h) := (div_le_div_of_nonneg_right hdist hh.le).trans_eq (by ring)
  have hrpow := Real.rpow_le_rpow (div_nonneg hd0 hh.le) hratio halpha.le
  rw [Real.mul_rpow (by norm_num) (div_nonneg hell.le hh.le)] at hrpow
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C 1) hosc0)
    (Real.rpow_nonneg (div_nonneg hd0 hh.le) alpha)
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hosc hCpos.le)
    (Real.rpow_nonneg (div_nonneg hd0 hh.le) alpha)
  have hMb0 : 0 ≤ sSup (u '' O) := hosc0.trans hosc
  have h₃ := mul_le_mul_of_nonneg_left hrpow (mul_nonneg hCpos.le hMb0)
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
