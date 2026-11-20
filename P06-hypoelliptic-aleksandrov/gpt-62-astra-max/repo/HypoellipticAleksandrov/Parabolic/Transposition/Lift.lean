module
public import HypoellipticAleksandrov.Parabolic.Transposition.BarrierSolve
import Mathlib

/-! # Lifting smooth boundary data -/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity Set Filter
open scoped ContDiff Topology
variable {d k : ℕ} {U : Domain d} {X : Fin (k+1) → Vector d}

private theorem along_congr (v : Vector d) {f g : TimeVelocity d → ℝ} {x} (e : f =ᶠ[𝓝 x] g) : along v f x = along v g x := by
  simp only [along,pd,e.fderiv_eq]

theorem generator_congr {f g : TimeVelocity d → ℝ} {x} (e : f =ᶠ[𝓝 x] g) : generator X f x = generator X g x := by
  simp only [generator,along_congr _ e]; congr 1; apply Finset.sum_congr rfl; intro i _
  apply along_congr; exact e.eventuallyEq_nhds.mono fun y hy => along_congr _ hy

theorem source_of_lift (X : Fin (k+1) → Vector d) (H : Field d) (hs : HasCompactSupport H.val) : HasCompactSupport (generator X H.val) := by
  apply hs.of_isClosed_subset (isClosed_tsupport _); apply closure_minimal _ (isClosed_tsupport _)
  intro z hz; by_contra h
  have eq : H.val =ᶠ[𝓝 z] fun _ => 0 := Filter.mem_of_superset ((isClosed_tsupport _).isOpen_compl.mem_nhds h) (fun _ hy => image_eq_zero_of_notMem_tsupport hy)
  have az (v : Vector d) : along v (fun _ => 0) = (fun _ => 0) := funext fun _ => by simp [along,pd]
  exact hz (by rw [generator_congr eq]; simp only [generator,az, Finset.sum_const_zero,add_zero])

private theorem along_add_at (v : Vector d) {f g : TimeVelocity d → ℝ} {x} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    along v (f+g) x = along v f x + along v g x := by simp [along,pd,fderiv_add hf hg,mul_add,Finset.sum_add_distrib]

private theorem generator_add (f g : Local U) {z} (hz : z ∈ U) :
    generator X (f.val+g.val) z = generator X f.val z + generator X g.val z := by
  have sq i : along (X i) (along (X i) (f.val+g.val)) z = along (X i) (along (X i) f.val) z + along (X i) (along (X i) g.val) z := by
    apply (along_congr (g := along (X i) f.val + along (X i) g.val) _ (Filter.mem_of_superset (U.isOpen.mem_nhds hz) (fun x hx => along_add_at _ (difAt f hx) (difAt g hx)))).trans
    apply along_add_at
    all_goals rw [← action_val]; exact difAt _ hz
  simp only [generator,along_add_at _ (difAt f hz) (difAt g hz),sq,Finset.sum_add_distrib]; ring

theorem harmonic_lift (H : Field d) (X : Fin (k+1) → Vector d)
    (span : KineticAleksandrov.LieAlgebraSpansOn ((unpack d) ⁻¹' (U : Set _)) (fun i => liftField (X i)))
    (f : Field d) (g : TimeVelocity d → ℝ) (hc : Continuous g) {M : TimeVelocity d → ℝ} {C : ℝ} (cm : Continuous M) (hM : ∀ z ∈ U, 0 ≤ M z)
    (hL : ∀ z ∈ U, |generator X H.val z| ≤ M z)
    (hf : ∀ z ∈ U, 0 ≤ f.val z ∧ f.val z ≤ C ∧ generator X f.val z ≤ -M z)
    (hg : ∀ z ∈ U, 0 ≤ g z)
    (ha : ∀ ε > (0 : ℝ), ∃ G : Field d, ∀ z ∈ U, 0 ≤ G.val z ∧ generator X G.val z ≤ -M z ∧ G.val z ≤ g z + ε) :
    ∃ J : Local U, (∀ z ∈ U, generator X J.val z = 0) ∧ EqOn J.val H.val (U : Set _)ᶜ ∧
      ∀ z ∈ U, |J.val z-H.val z| ≤ min (f.val z) (g z) := by
  classical
  obtain ⟨w,eq,bnd⟩ := solve_with_barriers X span ⟨-generator X H.val,(generator_sm X H.prop).neg⟩ f g hc cm hM (fun z hz => by simpa using hL z hz) hf hg ha
  let J := (U : Set _).piecewise (H.val+w.val) H.val
  have hJ : EqOn J (H.val+w.val) U := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  refine ⟨⟨J, ((H.prop.contDiffOn).add (smooth_local w)).congr hJ⟩, fun z hz => ?_,fun z hz => piecewise_eq_of_notMem _ _ _ hz,fun z hz => ?_⟩
  · rw [generator_congr (hJ.eventuallyEq_of_mem (U.isOpen.mem_nhds hz))]
    exact (generator_add (onDomain U H) w hz).trans (by rw [eq hz]; exact add_neg_cancel _)
  · simpa only [hJ hz, Pi.add_apply,add_sub_cancel_left] using bnd z hz

theorem continuousAt_boundary {E : Type*} [TopologicalSpace E] {s : Set E} {J H m : E → ℝ} {x}
    (hH : Continuous H) (hm : Continuous m) (hx : m x = 0) (he : EqOn J H sᶜ)
    (hb : ∀ y ∈ s, |J y - H y| ≤ m y) : ContinuousAt J x := by
  have h (y) : |J y-H y| ≤ |m y| := by
    by_cases hy : y ∈ s
    · exact (hb y hy).trans (le_abs_self _)
    · simp [he hy]
  have h0 : Tendsto (fun y => J y-H y) (𝓝 x) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => abs_nonneg _) h (by simpa [hx] using (hm.abs.continuousAt (x := x)).tendsto))
  have hh := h x; simp [hx] at hh
  change Tendsto J (𝓝 x) (𝓝 (J x)); rw [sub_eq_zero.mp hh]; simpa using h0.add hH.continuousAt.tendsto

end HypoellipticAleksandrov.Parabolic.Transposition
