module

public import PottsDiscontinuity.TorusLoops.LoopClusterProjection
public import PottsDiscontinuity.TorusLoops.DualTranslation

/-!
# Incidence of loops with their primal and dual clusters

Each medial loop has one incident cluster of each colour. The joint incidence
relation is connected: at every indexed edge its two ends are connected either
through the open primal edge or through the open dual edge.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
/-- The actual dual cluster incident to a loop, in translated primal coordinates. -/
def loopDualCluster (q : Loop hN hM (rcSmoothing A)) :
    (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent :=
  loopPrimalCluster hN hM (translatedDual A) (translatedDualLoopEquiv hN hM A q)

@[simp] theorem loopDualCluster_loopOf (d : DirectedDart (checkerArrows N M)) :
    loopDualCluster hN hM A (directedLoopOf _ _
        (checkerArrows_compatible hN hM (rcSmoothing A)) d) =
      (diamondOpenGraph hN hM true (translatedDual A)).connectedComponentMk
        (ribbonFace hN hM (dualDartEquiv hN hM d)) := by
  rfl

theorem loopDualCluster_ends_of_closed (v : Fin N × Fin M) (hv : A v = false) :
    loopDualCluster hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) (ribbonEndEquiv hN hM (v, false))) =
    loopDualCluster hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) (ribbonEndEquiv hN hM (v, true))) := by
  rw [loopDualCluster_loopOf, loopDualCluster_loopOf,
    ribbonFace_dualDart_end, ribbonFace_dualDart_end]
  have hr := diamond_endpoints_reachable hN hM (translatedDual A) (columnShift v) (by simp_all)
  apply SimpleGraph.ConnectedComponent.sound
  cases hc : checker v
  · simp_all
  tauto
end

section
variable {β : Type*} (hN : Even N) (hM : Even M) (A : RCConfig N M) (f : (diamondOpenGraph hN hM true A).ConnectedComponent → β) (g : (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent → β) (hfg : ∀ q, f (loopPrimalCluster hN hM A q) = g (loopDualCluster hN hM A q))
include g hfg
/-- Any labels agreeing across each loop agree between the two ends of every
indexed ribbon, using the primal edge when open and the dual edge when closed. -/
theorem compatible_cluster_labels_ends (v : Fin N × Fin M) :
    f ((diamondOpenGraph hN hM true A).connectedComponentMk
      (faceEndpoint hN hM true v false)) =
    f ((diamondOpenGraph hN hM true A).connectedComponentMk
      (faceEndpoint hN hM true v true)) := by
  cases hv : A v
  · let q₀ := directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (v, false))
    let q₁ := directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (v, true))
    have h₀ := hfg q₀
    have h₁ := hfg q₁
    rw [← (loopDualCluster_ends_of_closed hN hM A v hv)] at h₁
    aesop
  · exact congrArg f (SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A v hv))

/-- The loop–cluster incidence relation is connected, expressed without
choosing representatives of either cluster quotient. -/
theorem compatible_cluster_labels_constant (c c' : (diamondOpenGraph hN hM true A).ConnectedComponent) : f c = f c' := by
  induction c using Quot.inductionOn with
  | h u =>
    induction c' using Quot.inductionOn with
    | h v =>
      have hr := diamondOpenGraph_open_preconnected hN hM u v
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => rfl
      | @tail w z hr hadj ih =>
        apply ih.trans
        obtain ⟨⟨e, _, he⟩, _⟩ := hadj
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact compatible_cluster_labels_ends hN hM A f g hfg e
        · exact (compatible_cluster_labels_ends hN hM A f g hfg e).symm
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
theorem loopPrimalCluster_surjective  :
    Function.Surjective (loopPrimalCluster hN hM A) := by
  intro c
  induction c using Quot.inductionOn with
  | h v =>
    refine ⟨directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonVertexDart hN hM v), ?_⟩
    rfl

theorem loopDualCluster_surjective  :
    Function.Surjective (loopDualCluster hN hM A) :=
  (loopPrimalCluster_surjective hN hM (translatedDual A)).comp
    (translatedDualLoopEquiv hN hM A).surjective
end

noncomputable section

local instance primalClusterFintype (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Fintype (diamondOpenGraph hN hM true A).ConnectedComponent := Fintype.ofFinite _

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
abbrev LoopIncidenceVertex  :=
  (diamondOpenGraph hN hM true A).ConnectedComponent ⊕
    (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent

/-- The actual signed incidence matrix; loops remain distinct indexed edges. -/
def loopIncidenceMatrix  :
    Matrix (LoopIncidenceVertex hN hM A) (Loop hN hM (rcSmoothing A)) ℚ := by
  classical
  exact fun v q => (if v = Sum.inl (loopPrimalCluster hN hM A q) then 1 else 0) -
    (if v = Sum.inr (loopDualCluster hN hM A q) then 1 else 0)

def loopIncidenceBoundary  :
    (Loop hN hM (rcSmoothing A) → ℚ) →ₗ[ℚ] (LoopIncidenceVertex hN hM A → ℚ) := by
  classical
  exact Matrix.toLin' (loopIncidenceMatrix hN hM A)

def loopIncidenceCoboundary  :
    (LoopIncidenceVertex hN hM A → ℚ) →ₗ[ℚ] (Loop hN hM (rcSmoothing A) → ℚ) where
  toFun f q := f (.inl (loopPrimalCluster hN hM A q)) - f (.inr (loopDualCluster hN hM A q))
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem incidenceKernel_constant (f : LinearMap.ker (loopIncidenceCoboundary hN hM A))
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (v : LoopIncidenceVertex hN hM A) : f.val v = f.val (.inl c) := by
  have hfg (q : Loop hN hM (rcSmoothing A)) :=
    sub_eq_zero.mp (congrFun f.property q)
  cases v with
  | inl c' =>
      exact compatible_cluster_labels_constant hN hM A
        (fun c => f.val (.inl c)) (fun c => f.val (.inr c)) hfg c' c
  | inr d =>
      obtain ⟨q, rfl⟩ := loopDualCluster_surjective hN hM A d
      exact (hfg q).symm.trans (compatible_cluster_labels_constant hN hM A
        (fun c => f.val (.inl c)) (fun c => f.val (.inr c)) hfg _ c)
end

/-- The only potentials with zero incidence coboundary are constant potentials. -/
def incidenceKernelConstantEquiv (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    LinearMap.ker (loopIncidenceCoboundary hN hM A) ≃ₗ[ℚ] ℚ where
  toFun f := f.val (.inl ((diamondOpenGraph hN hM true A).connectedComponentMk
    (originFace hNp hMp)))
  invFun a := ⟨fun _ => a, by ext; exact sub_self a⟩
  left_inv f := by
    apply Subtype.ext
    grind [incidenceKernel_constant]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
theorem loopIncidenceCoboundary_eq_transpose (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    loopIncidenceCoboundary hN hM A = Matrix.toLin' (loopIncidenceMatrix hN hM A).transpose := by
  apply LinearMap.ext
  intro f
  funext q
  change f (.inl (loopPrimalCluster hN hM A q)) - f (.inr (loopDualCluster hN hM A q)) =
    ∑ v, loopIncidenceMatrix hN hM A v q * f v
  simp only [loopIncidenceMatrix, sub_mul, Finset.sum_sub_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The incidence circulation space has dimension at most one. This is the
algebraic form of the torus incidence graph being a tree or a unicyclic graph. -/
theorem finrank_loopIncidenceCycleSpace_le_one (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    Module.finrank ℚ (LinearMap.ker (loopIncidenceBoundary hN hM A)) ≤ 1 := by
  have hk : Module.finrank ℚ (LinearMap.ker (loopIncidenceCoboundary hN hM A)) = 1 := by
    rw [(incidenceKernelConstantEquiv hN hM hNp hMp A).finrank_eq, Module.finrank_self]
  have hr : Module.finrank ℚ (LinearMap.range (loopIncidenceBoundary hN hM A)) =
      Module.finrank ℚ (LinearMap.range (loopIncidenceCoboundary hN hM A)) := by
    rw [loopIncidenceCoboundary_eq_transpose]
    change (loopIncidenceMatrix hN hM A).rank = (loopIncidenceMatrix hN hM A).transpose.rank
    simp
  have hb := LinearMap.finrank_range_add_finrank_ker (loopIncidenceBoundary hN hM A)
  have hc := LinearMap.finrank_range_add_finrank_ker (loopIncidenceCoboundary hN hM A)
  have hv : Fintype.card (LoopIncidenceVertex hN hM A) =
      clusterCount hN hM true A + clusterCount hN hM true (translatedDual A) := by
    simp [clusterCount]
  simp_all
  have hl := rcLoopCount_le_primal_dual_clusters hN hM A
  change Fintype.card (Loop hN hM (rcSmoothing A)) ≤ _ at hl
  omega

end

end PottsDiscontinuity.TorusLoops
