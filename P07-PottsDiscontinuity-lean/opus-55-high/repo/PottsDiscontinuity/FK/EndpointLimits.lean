/- The box-exhaustion argument is adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The endpoint weight and measure proofs are original proofs for the frozen definitions. -/
module

public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit
public import PottsDiscontinuity.Infra.RCWeightBasic

/-!
# The random-cluster limits at the two edge-parameter endpoints

For every positive cluster weight and either boundary condition, the frozen finite-volume
laws at `p = 0` and `p = 1` concentrate on the constant configurations. Their cylinder limits
are the corresponding Dirac probability measures.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

/-- The edge parameter corresponding to a deterministic Boolean edge state. -/
def endpointParameter (b : Bool) : Set.Icc (0 : ℝ) 1 :=
  if b then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

theorem endpoint_weight_eq_zero (V : Finset (ℤ × ℤ))
    (q : Set.Ioi (0 : ℝ)) (i : Fin 2) (b : Bool)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : ω ≠ fun _ => b) : rcWeight V (endpointParameter b) q i ω = 0 := by
  classical
  have hex : ∃ e, ω e ≠ b := by
    grind
  obtain ⟨e, he⟩ := hex
  cases b with
  | false =>
      have htrue : ω e = true := by simp_all
      have : Nonempty {f // ω f = true} := by tauto
      simp [rcWeight, endpointParameter]
  | true =>
      have hfalse : ω e = false := by simp_all
      have : Nonempty {f // ω f = false} := by tauto
      simp [rcWeight, endpointParameter]

open Classical in
/-- The frozen finite-volume law at an endpoint is a point mass. -/
theorem rcProb_endpoint (V : Finset (ℤ × ℤ)) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (b : Bool)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    rcProb V (endpointParameter b) q i ω = if ω = (fun _ => b) then 1 else 0 := by
  have hsum : (∑ ω', rcWeight V (endpointParameter b) q i ω') =
      rcWeight V (endpointParameter b) q i (fun _ => b) := by
    apply Finset.sum_eq_single (fun _ => b)
    · simp_all [endpoint_weight_eq_zero]
    simp
  have hpos : 0 < rcWeight V (endpointParameter b) q i (fun _ => b) := by
    rw [← hsum]
    exact rcWeight_denominator_pos V (endpointParameter b) q i
  by_cases hω : ω = (fun _ => b)
  · grind [rcProb]
  · simp_all [rcProb, endpoint_weight_eq_zero]

/-- Every fixed lattice vertex lies in all sufficiently large frozen boxes. -/
theorem eventually_mem_box (x : ℤ × ℤ) : ∀ᶠ n : ℕ in atTop, x ∈ box n := by
  filter_upwards [eventually_ge_atTop (max x.1.natAbs x.2.natAbs)] with n hn
  grind [box]

/-- Every fixed lattice edge has a lift to the induced graph on every sufficiently large box. -/
theorem eventually_edge_lift_box (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop,
      ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
      refine ⟨⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩, rfl⟩
      simp_all

section
variable (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
/-- At either endpoint, the frozen box laws converge to the deterministic infinite configuration. -/
theorem isRCInfiniteVolumeLimit_endpoint (b : Bool) :
    IsRCInfiniteVolumeLimit (endpointParameter b) q i (Measure.dirac (fun _ => b)) := by
  constructor
  · infer_instance
  · intro A ξ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [((eventually_all_finset A).2 fun e _ => eventually_edge_lift_box e)] with n hn
    rw [Finset.sum_eq_single (fun _ => b)]
    · rw [rcProb_endpoint, Measure.dirac_real_apply]
      have hiff :
          (∀ e ∈ A, ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
            Sym2.map Subtype.val f.1 = e.1 ∧ b = ξ e) ↔ ∀ e ∈ A, b = ξ e := by
        grind
      simp only [hiff, ite_true, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    · grind [rcProb_endpoint]
    grind

/-- The frozen random-cluster infinite-volume measure exists at `p = 0`, for every `q > 0`. -/
theorem exists_isRCInfiniteVolumeLimit_zero  :
    ∃ μ, IsRCInfiniteVolumeLimit ⟨0, by norm_num⟩ q i μ :=
  ⟨Measure.dirac (fun _ => false), isRCInfiniteVolumeLimit_endpoint q i false⟩

/-- The frozen random-cluster infinite-volume measure exists at `p = 1`, for every `q > 0`. -/
theorem exists_isRCInfiniteVolumeLimit_one  :
    ∃ μ, IsRCInfiniteVolumeLimit ⟨1, by norm_num⟩ q i μ :=
  ⟨Measure.dirac (fun _ => true), isRCInfiniteVolumeLimit_endpoint q i true⟩
end

end PottsDiscontinuity.FK
