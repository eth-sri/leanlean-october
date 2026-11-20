module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
import Mathlib.Tactic.Positivity

/-! # From an ordered nearby-pair estimate to a compact-set Hölder estimate -/

@[expose] public section

noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set

theorem cylinder_subset_holderNeighbourhood {d : ℕ} {K : Set (KineticPoint d)}
    {P : KineticPoint d} (hP : P ∈ K) (R : ℝ) :
    backwardCylinder P (2 * R) ⊆ holderNeighbourhood R K :=
  fun _ hz => mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hz⟩⟩

/-- For far pairs, the oscillation alone suffices; only positive-distance nearby
pairs in time order need a local estimate. -/
theorem neighbourhood_estimate {d : ℕ} {K Ω : Set (KineticPoint d)} {u : KineticPoint d → ℝ}
    {R a C q : ℝ} (hK : IsCompact K) (hR : 0 < R) (ha : 0 < a) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hfar : 1 ≤ C * q ^ a) (hu : ContinuousOn u Ω)
    (hΩ : ∀ P ∈ K, closure (backwardCylinder P (2 * R)) ⊆ Ω)
    (hnear : let E := holderNeighbourhood R K
      BddAbove (u '' E) → BddBelow (u '' E) →
        ∀ P ∈ K, ∀ Q ∈ K, P.time ≤ Q.time →
          0 < quasiDistance P Q → quasiDistance P Q / R < q →
          |u P - u Q| ≤ C * oscillationOn u E * (quasiDistance P Q / R) ^ a) :
    ∀ P ∈ K, ∀ Q ∈ K,
      |u P - u Q| ≤ C * oscillationOn u (holderNeighbourhood R K) *
        (quasiDistance P Q / R) ^ a := by
  let E := holderNeighbourhood R K
  obtain ⟨hclosed, hcompact⟩ := holder_neighbourhood_compact K hK R hR
  have hEO : closure E ⊆ Ω := by
    rw [hclosed]
    simpa only [iUnion_subset_iff] using hΩ
  have hcont := hu.mono hEO
  have hac := hcompact.bddAbove_image hcont
  have hbc := hcompact.bddBelow_image hcont
  have hab : BddAbove (u '' E) := hac.mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := hbc.mono (image_mono subset_closure)
  have hR' : 0 < 2 * R := by positivity
  have hcenter (P : KineticPoint d) (hP : P ∈ K) : P ∈ closure E :=
    closure_mono (cylinder_subset_holderNeighbourhood hP R)
      (Covering.top_mem_closure_cylinder P hR' (PDE.center_mem_euclideanBall _ hR'))
  have ordered (P : KineticPoint d) (hP : P ∈ K) (Q : KineticPoint d) (hQ : Q ∈ K)
      (ht : P.time ≤ Q.time) :
      |u P - u Q| ≤ C * oscillationOn u E * (quasiDistance P Q / R) ^ a := by
    have hne := (backwardCylinder_nonempty P hR').mono (cylinder_subset_holderNeighbourhood hP R)
    have hosc := oscillationOn_nonneg hne hab hbb
    have hδ := quasiDistance_nonneg P Q
    by_cases hz : quasiDistance P Q = 0
    · rw [congrArg u ((quasiDistance_eq_zero_iff P Q).mp hz), sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC hosc) (Real.rpow_nonneg (div_nonneg hδ hR.le) _)
    by_cases h : quasiDistance P Q / R < q
    · exact hnear hab hbb P hP Q hQ ht (lt_of_le_of_ne hδ (Ne.symm hz)) h
    have hb := abs_sub_le_oscillationOn hac hbc (hcenter P hP) (hcenter Q hQ)
    rw [oscillationOn_closure hne hcompact hcont] at hb
    have hpow := Real.rpow_le_rpow hq (le_of_not_gt h) ha.le
    have hcoef := hfar.trans (mul_le_mul_of_nonneg_left hpow hC)
    rw [mul_comm C, mul_assoc]
    exact hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcoef hosc)
  intro P hP Q hQ
  rcases le_total P.time Q.time with ht | ht
  · exact ordered P hP Q hQ ht
  · simpa only [abs_sub_comm, quasiDistance_symm Q P] using ordered Q hQ P hP ht

end HypoellipticAleksandrov.KineticAleksandrov.Holder
