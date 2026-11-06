import RequestProject.OrderUniversalPosetConnected
import RequestProject.OrderNerveOneDictionary
import RequestProject.ChamberQuotientAttachingRelativeChains
noncomputable section


/-! Convert genuine universal-cover cellular chains into lifted-order nerve chains.
The conversion preserves coefficients, boundaries, projection, and subposet support.

-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P] {a : P}

/-- The actual cover edges, expressed in lifted-order nerve coordinates. -/
def universalNerveChain1 :
    (UE (orderCx P) a →₀ ℤ) →ₗ[ℤ] Nerve.Ch (UOrder P a) :=
  ordNerveChain1.comp (chain1 uOrderHomInv)

/-- The actual cover faces, expressed in lifted-order nerve coordinates. -/
def universalNerveChain2 :
    (UF (orderCx P) a →₀ ℤ) →ₗ[ℤ] Nerve.Ch (UOrder P a) :=
  ordNerveChain2.comp (chain2 uOrderHomInv)

theorem uOrderHomInv_edge_projection (e : UE (orderCx P) a) :
    (orderCxMap uOrderEnd uOrderEnd_monotone).onE (uOrderHomInv.onE e) = e.1.2 := congrArg (·.1.2)
    (homInv_onE_apply uOrderHom Function.bijective_id
      _
      _ e)

theorem uOrderHomInv_face_projection (t : UF (orderCx P) a) :
    (orderCxMap uOrderEnd uOrderEnd_monotone).onF (uOrderHomInv.onF t) = t.1.2 := congrArg (·.1.2)
    (homInv_onF_apply uOrderHom Function.bijective_id
      _
      _ t)

/-- This is an equality for arbitrary chains, including relative chains. -/
theorem universalNerveChain2_bdry c :
    Nerve.bdry (universalNerveChain2 c) =
      universalNerveChain1 (Comb.bdry2 (uCover (orderCx P) a) c) := by
  change Nerve.bdry (ordNerveChain2 (chain2 uOrderHomInv c)) =
    ordNerveChain1 (chain1 uOrderHomInv (Comb.bdry2 _ c))
  rw [← ordNerveChain1_bdry2, bdry2_chain2]

theorem universalNerveChain2_lengthProjection (c : UF (orderCx P) a →₀ ℤ) :
    Nerve.lengthProjection 3 (universalNerveChain2 c) = universalNerveChain2 c :=
  ordNerveChain2_lengthProjection _

theorem universalNerveChain2_mem_inc c :
    universalNerveChain2 c ∈ Nerve.Inc (UOrder P a) :=
  ordNerveChain2_mem_inc _

theorem universalNerveChain2_single (t : UF (orderCx P) a) n :
    universalNerveChain2 (Finsupp.single t n) =
      n • FreeAbelianGroup.of [(uOrderHomInv.onF t).1.1,
        (uOrderHomInv.onF t).1.2.1, (uOrderHomInv.onF t).1.2.2] := by
  change ordNerveChain2 (Finsupp.mapDomain uOrderHomInv.onF (Finsupp.single t n)) = _
  simp [Finsupp.mapDomain_single, ordNerveChain2, Finsupp.linearCombination_single]

/-- A face whose projection lies in a subposet has all lifted vertices over that subposet. -/
theorem universalNerveChain2_single_mem_incOn S
    (t : UF (orderCx P) a) n (ht : t.1.2 ∈ ordTriOn S) :
    universalNerveChain2 (Finsupp.single t n) ∈
      Nerve.IncOn (fun v => S (uOrderEnd v)) := by
  rw [universalNerveChain2_single]
  apply AddSubgroup.zsmul_mem
  apply Nerve.of_mem_incOn
  · grind
  · rw [← uOrderHomInv_face_projection t] at ht
    change S (uOrderEnd (uOrderHomInv.onF t).1.1) ∧
      S (uOrderEnd (uOrderHomInv.onF t).1.2.1) ∧
      S (uOrderEnd (uOrderHomInv.onF t).1.2.2) at ht
    simp_all

/-- Finite cellular support over a subposet becomes nerve support over that same subposet.
No cycle or connectedness hypothesis is required. -/
theorem universalNerveChain2_mem_incOn S
    (c : UF (orderCx P) a →₀ ℤ)
    (hc : ∀ t ∈ c.support, t.1.2 ∈ ordTriOn S) :
    universalNerveChain2 c ∈ Nerve.IncOn (fun v => S (uOrderEnd v)) := by
  classical
  have he : c = ∑ t ∈ c.support, Finsupp.single t (c t) :=
    c.sum_single.symm
  rw [he, map_sum]
  apply AddSubgroup.sum_mem
  intro t ht
  exact universalNerveChain2_single_mem_incOn S t _ (hc t ht)

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Comb Nerve
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- The relative attaching-chain theorem applied to the actual supported cellular chain
in the quotient's universal cover. Its boundary is prescribed through the exact
degree-one conversion; the original chain need not be a cycle. -/
theorem qUniversal_old_cellular_relative_chain_from_attaching x
    (hx : IsConnected (orderCx X)) (σ : NeSpx A)
    (z : UF (orderCx (Qpos A X att)) (qNew x) →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2 ∈ ordTriOn InQOld)
    (b : Ch (QLiftedAttaching (qNew (A := A) (att := att) x))) (hb : b ∈ Inc _)
    (hbz : universalNerveChain1 (Comb.bdry2 (uCover (orderCx (Qpos A X att)) (qNew x)) z) =
      cmap Subtype.val b) :
    ∃ c,
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧ Nerve.bdry c = b ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧
          universalNerveChain2 z = cmap Subtype.val c + Nerve.bdry y := by
  apply qUniversal_old_relative_chain_from_attaching x hx σ _
    (universalNerveChain2_mem_incOn InQOld z hz)
    (universalNerveChain2_lengthProjection z) b hb
  rw [universalNerveChain2_bdry, hbz]
