import RequestProject.OrderComponentLabels
import RequestProject.CellularHomotopyChain
import RequestProject.OrderNervePositiveFillings
import RequestProject.Tac


/-! Finite one-cycle fillings when every component has trivial edge-path pi1. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- A componentwise path contraction gives actual finite cellular fillings.
Connectedness or finiteness of the whole poset is not required. -/
theorem order_oneCycle_filling_of_simplyConnected (hsc : SimplyConnected (orderCx P))
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ y : OrdTri P →₀ ℤ, bdry2 (orderCx P) y = c := by
  classical
  let r := fun v => Quotient.out (orderComponentLabel P v)
  have hr (e : OrdEdge P) : r e.1.1 = r e.1.2 :=
    congrArg Quotient.out (orderComponentLabel_eq_of_le e.2)
  have hreach (v : P) : Reach (orderCx P) (r v) v :=
    (orderComponentLabel_eq_iff _ _).mp (Quotient.out_eq _)
  choose p hp using hreach
  have hface (e : (orderCx P).E) : ∃ y : OrdTri P →₀ ℤ,
      bdry2 _ y = Finsupp.single e (1) + pathChain (p e.1.1) -
        pathChain (p e.1.2) := by
    let l := p e.1.1 ++ [(e, true)] ++ revPath (p e.1.2)
    have hrev : IsPathX (orderCx P) (revPath (p e.1.2))
        e.1.2 (r e.1.1) := by
      rw [hr e]
      exact isPath_revPath (hp e.1.2)
    have hl : IsPathX (orderCx P) l (r e.1.1) (r e.1.1) :=
      ((hp e.1.1).append (by aesop)).append hrev
    cases' (hsc _ l hl).exists_boundary with y hy
    refine ⟨y, ?_⟩
    simpa [l, pathChain_append, pathChain_cons, pathChain_revPath,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy
  choose f hf using hface
  let s : (P →₀ ℤ) →ₗ[ℤ] (OrdEdge P →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  let t :=
    Finsupp.linearCombination ℤ f
  have hs (v : P) : s (Finsupp.single v 1) = pathChain (p v) := by
    aesop
  have ht (z : OrdEdge P →₀ ℤ) : bdry2 (orderCx P) (t z) =
      z - s (bdry1 (orderCx P) z) := by
    lin_ind z with z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]; abel
    | e n =>
      rw [Finsupp.linearCombination_single, map_smul, hf, bdry1_single,
        map_smul, map_sub, hs, hs, smul_sub, smul_add, smul_sub]
      simp [Finsupp.smul_single, smul_eq_mul, mul_one]
      simp [orderCx]
      abel
  exact ⟨t c, by simp_all⟩

theorem nerve_oneCycle_filling_of_simplyConnected (hsc : SimplyConnected (orderCx P))
    c (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 2 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain1 (decodeOrdNerve1 c) = c := by
    rw [ordNerveChain1_decode hi, hd]
  have hcyc : bdry1 _ (decodeOrdNerve1 c) = 0 :=
    (ordNerveChain1_cycle_iff _).mp (by simp_all)
  cases' order_oneCycle_filling_of_simplyConnected hsc _ hcyc with y hy
  refine ⟨ordNerveChain2 y, ordNerveChain2_mem_inc y, ?_⟩
  rw [← ordNerveChain1_bdry2, hy, he]
