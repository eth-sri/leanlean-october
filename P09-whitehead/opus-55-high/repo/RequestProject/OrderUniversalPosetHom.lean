import RequestProject.OrderUniversalPosetCells
import RequestProject.UnivCoverIncl
import RequestProject.Tac


/-! The cellular identification of the genuine universal-cover order complex. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem uOrderEdge_target (e : OrdEdge (UOrder P a)) :
    uTgt (uOrderEdge e) = e.1.2 := e.2.2

theorem uOrderFace_att t :
    uAtt (uOrderFace t) = ((orderCx (UOrder P a)).att t).map
      (fun eb => (uOrderEdge eb.1, eb.2)) := by
  obtain ⟨⟨v, w, z⟩, hvw, hwz⟩ := t
  have hvw' : extend (ordPos (uOrderEnd_monotone hvw)) v = w := hvw.2
  have hwz' : extend (ordPos (uOrderEnd_monotone hwz)) w = z := hwz.2
  have hvz' : extend (ordPos (uOrderEnd_monotone (hvw.trans hwz))) v = z :=
    (hvw.trans hwz).2
  have hback : extend (ordNeg (uOrderEnd_monotone (hvw.trans hwz))) z = v := by
    have h := extend_revGerm (c := v)
      (eb := ordPos (uOrderEnd_monotone (hvw.trans hwz))) rfl
    simp_all
  change uLiftPath [ordPos (uOrderEnd_monotone hvw), ordPos (uOrderEnd_monotone hwz),
    ordNeg (by grind)] v =
      [(uOrderEdge ⟨(v, w), hvw⟩, true), (uOrderEdge ⟨(w, z), hwz⟩, true),
        (uOrderEdge ⟨(v, z), hvw.trans hwz⟩, false)]
  rw [uLiftPath_cons rfl, hvw', uLiftPath_cons rfl, hwz', uLiftPath_cons rfl,
    uLiftPath_nil]
  simp only [ordPos, ordNeg, liftGerm_true, liftGerm_false]
  congr 1
  congr 1
  congr 1
  congr 1
  apply Subtype.ext
  aesop

/-- The constructed cellular map identifies the lifted-order cells with the existing
path-class universal-cover cells, and preserves their actual attaching paths. -/
noncomputable def uOrderHom : Hom (orderCx (UOrder P a)) (uCover (orderCx P) a) where
  onV := id
  onE := uOrderEdge
  onF := uOrderFace
  src_onE _ := rfl
  tgt_onE := uOrderEdge_target
  base_onF _ := rfl
  att_onF := uOrderFace_att

theorem uOrderHom_chain2_injective :
    Function.Injective (chain2 (uOrderHom (P := P) (a := a))) :=
  Finsupp.mapDomain_injective uOrderFace_injective

theorem uOrderHom_chain2_surjective :
    Function.Surjective (chain2 (uOrderHom (P := P) (a := a))) :=
  Finsupp.mapDomain_surjective uOrderFace_surjective

theorem uOrderHom_cycle_iff (c : OrdTri (UOrder P a) →₀ ℤ) :
    bdry2 (uCover (orderCx P) a) (chain2 uOrderHom c) = 0 ↔
      bdry2 (orderCx (UOrder P a)) c = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective uOrderEdge_injective
    tauto
  simp_all

/-- Every actual universal-cover two-cycle has a unique finite cycle in the
constructed lifted-order complex as its preimage. -/
theorem exists_unique_uOrder_cycle (c : UF (orderCx P) a →₀ ℤ)
    (hc : bdry2 (uCover (orderCx P) a) c = 0) :
    ∃! d : OrdTri (UOrder P a) →₀ ℤ,
      chain2 uOrderHom d = c ∧ bdry2 (orderCx (UOrder P a)) d = 0 := by
  cases' uOrderHom_chain2_surjective c with d hd
  refine ⟨d, ⟨hd, (uOrderHom_cycle_iff d).mp (hd.symm ▸ hc)⟩, ?_⟩
  intro e he
  exact uOrderHom_chain2_injective (he.1.trans hd.symm)
