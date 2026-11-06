import RequestProject.OrderNerveSmallChainMapLow
import RequestProject.Tac
noncomputable section


namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- The data needed to extend a carried approximation by one degree. -/
structure OrderSmallNerveStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 1) (map c) = map c
  closed_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    Nerve.bdry (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) = 0

def orderSmallNerveStageZero : OrderSmallNerveStage P 0 where
  map := orderSmallToNerve0
  carrier := orderSmallToNerve0_single_carrier
  homogeneous := orderSmallToNerve0_length
  closed_boundary c := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 c.val) • _ = 0
    rw [augmentation_boundary, zero_smul]

theorem orderSmallNerveBoundary_carrier
    (f : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ τ : OrderSmallSimplex P n,
      f (orderSmallSingle τ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier τ.val))
    σ :
    f (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallSingle_boundary, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  rw [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
    (by aesop)

/-- Every new simplex can be filled in its own acyclic order carrier. -/
theorem orderSmallNerveStage_fill (s : OrderSmallNerveStage P n)
    σ :
    ∃ b, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b =
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property _
    (orderSmallNerveBoundary_carrier s.map s.carrier σ) (s.closed_boundary _)
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact s.homogeneous _

def orderSmallNerveStageNextMap (s : OrderSmallNerveStage P n) :
    smallChains (orderNerveRealizationOpenStar P) (n + 1) →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallNerveStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P _).toLinearMap

theorem orderSmallNerveStageNextMap_single s
    (σ : OrderSmallSimplex P (n + 1)) :
    orderSmallNerveStageNextMap s (orderSmallSingle σ 1) =
      (orderSmallNerveStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P _).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P (n + 1) =>
    (orderSmallNerveStage_fill s τ).choose))
      ((orderSmallChainEquiv P _) (orderSmallSingle σ 1)) = _
  simp_all

theorem orderSmallNerveStageNextMap_boundary s
    c :
    Nerve.bdry (orderSmallNerveStageNextMap s c) =
      s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : Nerve.bdry.toIntLinearMap.comp (orderSmallNerveStageNextMap s) =
      s.map.comp (smallBoundary _ n) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallNerveStageNextMap s (orderSmallSingle σ 1)) = _
    rw [orderSmallNerveStageNextMap_single]
    exact (orderSmallNerveStage_fill s σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

def orderSmallNerveStageNext (s : OrderSmallNerveStage P n) :
    OrderSmallNerveStage P (n + 1) where
  map := orderSmallNerveStageNextMap s
  carrier σ := by
    rw [orderSmallNerveStageNextMap_single]
    grind
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 2)).toIntLinearMap.comp
        (orderSmallNerveStageNextMap s) = orderSmallNerveStageNextMap s := by
      apply orderSmallSingle_spans
      intro σ
      change Nerve.lengthProjection (n + 2)
        (orderSmallNerveStageNextMap s (orderSmallSingle σ 1)) = _
      rw [orderSmallNerveStageNextMap_single]
      grind
    exact DFunLike.congr_fun he c
  closed_boundary c := by
    rw [orderSmallNerveStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared _ n) c
    simp_all

/-- A carried approximation exists simultaneously in all dimensions. -/
def orderSmallNerveStage P [PartialOrder P] :
    (n : ℕ) → OrderSmallNerveStage P n
  | 0 => orderSmallNerveStageZero
  | n + 1 => orderSmallNerveStageNext (orderSmallNerveStage P n)

def orderSmallToNerve P [PartialOrder P] n :=
  (orderSmallNerveStage P n).map

theorem orderSmallToNerve_carrier n σ :
    orderSmallToNerve P n (orderSmallSingle σ 1) ∈
      Nerve.IncOn (orderNerveSingularCarrier σ.val) :=
  (orderSmallNerveStage P n).carrier σ

theorem orderSmallToNerve_length n
    c :
    Nerve.lengthProjection (n + 1) (orderSmallToNerve P n c) = orderSmallToNerve P n c :=
  (orderSmallNerveStage P n).homogeneous c

theorem orderSmallToNerve_boundary n
    c :
    Nerve.bdry (orderSmallToNerve P (n + 1) c) =
      orderSmallToNerve P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  orderSmallNerveStageNextMap_boundary _ c

theorem orderSmallToNerve_mem_inc n
    c :
    orderSmallToNerve P n c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  lin_ind d σ r using aesop =>
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul, orderSmallChainEquiv_symm_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallToNerve_carrier n σ)) r
