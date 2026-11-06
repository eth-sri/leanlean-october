module

public import DedekindZetaZeroFree.Analysis.Sobolev.Embedding.FiniteOrderRepresentatives

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalCubeEmbedding

open MeasureTheory
open scoped ContDiff
open KPContLocalNorm

def euclideanSobolevNorm {n : ℕ} (k : ℕ) (w : Space n → ℂ) : ℝ :=
  Real.sqrt (∑ α : MultiIndex n k, ∫ x, ‖coordinateDerivative α w x‖ ^ 2)

def closedCarrier {n : ℕ} (B : LocalBall n) : Set (Space n) :=
  Metric.closedBall B.center B.radius

theorem ball_sobolev_embedding {n : ℕ} (A B : LocalBall n)
    (hAB : closedCarrier A ⊆ B.carrier) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : IntegerSobolev B (m + n),
      ∃ (f : Space n → ℂ) (j : CompactJets (closedCarrier A) m),
        ContDiffOn ℝ m f B.carrier ∧
        (f =ᵐ[volume.restrict B.carrier]
          (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) ∧
        (∀ α : MultiIndex n m, ∀ x : closedCarrier A,
          j α x = coordinateDerivative α f x) ∧
        jetMaxNorm (isCompact_closedBall A.center A.radius) j ≤ C * u.sobolevNorm ∧
        (∀ g : Space n → ℂ, ContDiffOn ℝ m g B.carrier →
          (g =ᵐ[volume.restrict B.carrier]
            (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) →
          Set.EqOn g f B.carrier) := by
  obtain ⟨C, hC, hbound⟩ :=
    KPLocalCubeSobolevJets.finite_order_representative_interior_jet_bound A B hAB m
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨f, hf, hfu⟩ :=
    KPLocalCubeSobolevJets.weak_sobolev_has_finite_order_representative B m u
  obtain ⟨j, hj, hjbound⟩ := hbound u f hf hfu
  refine ⟨f, j, hf, hfu, hj, hjbound, ?_⟩
  intro g hg hgu
  exact Measure.eqOn_open_of_ae_eq (hgu.trans hfu.symm) Metric.isOpen_ball
    hg.continuousOn hf.continuousOn

def LocallyAllIntegerSobolev {n : ℕ} (U : Set (Space n)) (u : Space n → ℂ) : Prop :=
  ∀ B : LocalBall n, closedCarrier B ⊆ U → ∀ k : ℕ,
    ∃ v : IntegerSobolev B k,
      u =ᵐ[volume.restrict B.carrier]
        (fun x => v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)

theorem smooth_on_local_ball {n : ℕ} (B : LocalBall n)
    (u : Space n → ℂ)
    (hu : ∀ k : ℕ, ∃ v : IntegerSobolev B k,
      u =ᵐ[volume.restrict B.carrier]
        (fun x => v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)) :
    ∃ f : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier ∧
      f =ᵐ[volume.restrict B.carrier] u := by
  classical
  let A : LocalBall n := ⟨B.dimension_pos, B.center, B.radius / 2, by linarith [B.radius_pos]⟩
  have hAB : closedCarrier A ⊆ B.carrier :=
    Metric.closedBall_subset_ball (by dsimp [A]; linarith [B.radius_pos])
  have hreps : ∀ m : ℕ, ∃ f : Space n → ℂ,
      ContDiffOn ℝ m f B.carrier ∧ f =ᵐ[volume.restrict B.carrier] u := by
    intro m
    obtain ⟨v, hv⟩ := hu (m + n)
    obtain ⟨C, hC, h⟩ := ball_sobolev_embedding A B hAB m
    obtain ⟨f, j, hf, hfv, hj, hbound, hunique⟩ := h v
    exact ⟨f, hf, hfv.trans hv.symm⟩
  choose f hf hfu using hreps
  refine ⟨f 0, contDiffOn_infty.mpr ?_, hfu 0⟩
  intro m
  apply (hf m).congr
  exact Measure.eqOn_open_of_ae_eq ((hfu 0).trans (hfu m).symm)
    Metric.isOpen_ball (hf 0).continuousOn (hf m).continuousOn

theorem locally_all_orders_smooth_representative {n : ℕ} (hn : 0 < n)
    (U : Set (Space n)) (hU : IsOpen U) (u : Space n → ℂ)
    (hu : LocallyAllIntegerSobolev U u) :
    ∃ f : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      (f =ᵐ[volume.restrict U] u) ∧
      (∀ g : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) g U →
        (g =ᵐ[volume.restrict U] u) → Set.EqOn g f U) := by
  classical
  have hballs : ∀ p : U, ∃ B : LocalBall n,
      B.center = p.val ∧ closedCarrier B ⊆ U := by
    intro p
    obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds p.property)
    exact ⟨⟨hn, p.val, r, hr⟩, rfl, hrU⟩
  choose B hBcenter hBU using hballs
  have hBopen : ∀ p : U, IsOpen (B p).carrier := fun p => Metric.isOpen_ball
  have hBsub : ∀ p : U, (B p).carrier ⊆ U := fun p =>
    (Metric.ball_subset_closedBall).trans (hBU p)
  have hBmem : ∀ p : U, p.val ∈ (B p).carrier := by
    intro p
    rw [LocalBall.carrier, hBcenter p]
    exact Metric.mem_ball_self (B p).radius_pos
  have hreps : ∀ p : U, ∃ f : Space n → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (B p).carrier ∧
      f =ᵐ[volume.restrict (B p).carrier] u := by
    intro p
    exact smooth_on_local_ball (B p) u (hu (B p) (hBU p))
  choose v hv hvu using hreps
  have hcompat : ∀ p q : U, Set.EqOn (v p) (v q) ((B p).carrier ∩ (B q).carrier) := by
    intro p q
    have hp : v p =ᵐ[volume.restrict ((B p).carrier ∩ (B q).carrier)] u :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hvu p)
    have hq : v q =ᵐ[volume.restrict ((B p).carrier ∩ (B q).carrier)] u :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hvu q)
    exact Measure.eqOn_open_of_ae_eq (hp.trans hq.symm)
      ((hBopen p).inter (hBopen q))
      ((hv p).continuousOn.mono Set.inter_subset_left)
      ((hv q).continuousOn.mono Set.inter_subset_right)
  let f : Space n → ℂ := fun x => if hx : x ∈ U then v ⟨x, hx⟩ x else 0
  have hfB : ∀ p : U, Set.EqOn f (v p) (B p).carrier := by
    intro p x hx
    have hxU : x ∈ U := hBsub p hx
    dsimp [f]
    rw [dif_pos hxU]
    exact hcompat ⟨x, hxU⟩ p ⟨hBmem ⟨x, hxU⟩, hx⟩
  have hfsmooth : ContDiffOn ℝ (⊤ : ℕ∞) f U := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    let p : U := ⟨x, hx⟩
    refine ⟨(B p).carrier, hBopen p, hBmem p, ?_⟩
    exact ((hv p).congr (hfB p)).mono Set.inter_subset_right
  have hfaeB : ∀ p : U, f =ᵐ[volume.restrict (B p).carrier] u := by
    intro p
    have hfv : f =ᵐ[volume.restrict (B p).carrier] v p :=
      ae_restrict_of_forall_mem (hBopen p).measurableSet (hfB p)
    exact hfv.trans (hvu p)
  have hcover : U ⊆ ⋃ p : U, (B p).carrier := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hBmem ⟨x, hx⟩⟩
  obtain ⟨t, htcount, htcover⟩ := (IsLindelof.of_coe (s := U)).elim_countable_subcover
    (fun p : U => (B p).carrier) hBopen hcover
  have hfae : f =ᵐ[volume.restrict U] u := by
    apply ae_restrict_of_ae_restrict_of_subset htcover
    exact (ae_restrict_biUnion_iff (fun p : U => (B p).carrier) htcount
      (fun x => f x = u x)).mpr (fun p _ => hfaeB p)
  refine ⟨f, hfsmooth, hfae, ?_⟩
  intro g hg hgu
  exact Measure.eqOn_open_of_ae_eq (hgu.trans hfae.symm) hU hg.continuousOn
    hfsmooth.continuousOn
