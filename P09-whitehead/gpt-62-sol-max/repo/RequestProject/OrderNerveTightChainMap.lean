module

public import RequestProject.OrderNerveTightCarriers
public import RequestProject.TopologicalSingular.SubdivisionSupport

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- The data needed to extend a carried approximation by one degree. -/
structure OrderTightNerveStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveTightCarrier σ.val)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 1) (map c) = map c
  closed_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    Nerve.bdry (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) = 0

noncomputable def orderTightNerveStageZero : OrderTightNerveStage P 0 where
  map := orderSmallToNerve0
  carrier := orderSmallToNerve0_tight
  homogeneous := orderSmallToNerve0_length
  closed_boundary c := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 c.val) • _ = 0
    rw [augmentation_boundary, zero_smul]

theorem orderTightNerveBoundary_carrier {n : ℕ}
    (f : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ τ : OrderSmallSimplex P n,
      f (orderSmallSingle τ 1) ∈ Nerve.IncOn (orderNerveTightCarrier τ.val))
    (σ : OrderSmallSimplex P (n + 1)) :
    f (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      Nerve.IncOn (orderNerveTightCarrier σ.val) := by
  rw [orderSmallSingle_boundary, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  rw [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderNerveTightCarrier_face σ.val i hp)
    (hf (orderSmallSimplexFace i σ))

/-- Every new simplex can be filled in its own acyclic order carrier. -/
theorem orderTightNerveStage_fill {n : ℕ} (s : OrderTightNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveTightCarrier σ.val) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b =
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  obtain ⟨b, hb, he⟩ := orderNerveTightCarrier_acyclic σ _
    (orderTightNerveBoundary_carrier s.map s.carrier σ) (s.closed_boundary _)
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact s.homogeneous _

noncomputable def orderTightNerveStageLift {n : ℕ} (s : OrderTightNerveStage P n) :
    CarriedLift (orderSmallBasis P (n + 1))
      (fun σ b => b ∈ Nerve.IncOn (orderNerveTightCarrier σ.val) ∧
        Nerve.lengthProjection (n + 2) b = b)
      Nerve.bdry.toIntLinearMap (s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n)) :=
  .ofExists fun σ => by
    simpa only [orderSmallBasis_apply, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, and_assoc]
      using orderTightNerveStage_fill s σ

noncomputable def orderTightNerveStageNext {n : ℕ} (s : OrderTightNerveStage P n) :
    OrderTightNerveStage P (n + 1) where
  map := (orderTightNerveStageLift s).map
  carrier σ := by simpa only [orderSmallBasis_apply] using ((orderTightNerveStageLift s).carried σ).1
  homogeneous := (orderTightNerveStageLift s).fixed (Nerve.lengthProjection (n + 2)).toIntLinearMap fun _ _ h => h.2
  closed_boundary c := by
    rw [show Nerve.bdry _ = s.map (smallBoundary (orderNerveRealizationOpenStar P) n
        (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c)) from
      (orderTightNerveStageLift s).boundary _]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    simp_all

/-- A carried approximation exists simultaneously in all dimensions. -/
noncomputable def orderTightNerveStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderTightNerveStage P n
  | 0 => orderTightNerveStageZero
  | n + 1 => orderTightNerveStageNext (orderTightNerveStage P n)

noncomputable def orderTightToNerve (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P :=
  (orderTightNerveStage P n).map

theorem orderTightToNerve_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderTightToNerve P n (orderSmallSingle σ 1) ∈
      Nerve.IncOn (orderNerveTightCarrier σ.val) :=
  (orderTightNerveStage P n).carrier σ

theorem orderTightToNerve_length (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    Nerve.lengthProjection (n + 1) (orderTightToNerve P n c) = orderTightToNerve P n c :=
  (orderTightNerveStage P n).homogeneous c

theorem orderTightToNerve_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderTightToNerve P (n + 1) c) =
      orderTightToNerve P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  (orderTightNerveStageLift (orderTightNerveStage P n)).boundary c

theorem orderTightToNerve_mem_inc (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    orderTightToNerve P n c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  apply Finsupp.map_mem_of_basis (Nerve.Inc P).toIntSubmodule
    ((orderTightToNerve P n).comp (orderSmallChainEquiv P n).symm.toLinearMap) _ d
  intro σ
  change (orderTightToNerve P n) ((orderSmallChainEquiv P n).symm (Finsupp.single σ 1)) ∈ Nerve.Inc P
  simpa only [orderSmallChainEquiv_symm_single] using
    Nerve.incOn_le_inc _ (orderTightToNerve_carrier n σ)

/-- The tightened approximation respects every induced vertex subcomplex. -/
theorem orderTightToNerve_supported (n : ℕ) (A : Set P)
    (c : smallChains (orderNerveRealizationOpenStar P) n)
    (hc : c.val ∈ subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) n) :
    orderTightToNerve P n c ∈ Nerve.IncOn A := by
  classical
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  have hd : d ∈ Finsupp.supported ℤ ℤ {σ : OrderSmallSimplex P n |
      ∀ z, σ.val z ∈ orderNerveRealizationSubcomplex P A} := by
    rw [subChains_eq_supported, Finsupp.mem_supported] at hc
    rw [Finsupp.mem_supported]
    intro σ hσ
    apply hc
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hσ ⊢
    have he := congrArg (fun e  => e σ)
      ((orderSmallChainEquiv P n).apply_symm_apply d)
    change ((orderSmallChainEquiv P n).symm d).val σ.val = d σ at he
    rwa [he]
  exact Finsupp.map_mem_of_supported _ (Nerve.IncOn A).toIntSubmodule
    ((orderTightToNerve P n).comp (orderSmallChainEquiv P n).symm.toLinearMap)
    (by
      intro σ hσ
      change orderTightToNerve P n ((orderSmallChainEquiv P n).symm (Finsupp.single σ 1)) ∈ _
      rw [orderSmallChainEquiv_symm_single]
      exact Nerve.incOn_mono (fun _ hp => orderNerveTightCarrier_subset σ.val A hσ hp)
        (orderTightToNerve_carrier n σ)) hd

end FiniteChains.Comb
