module

public import RequestProject.OrderComplexExt
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Finite chains and cycles on an actual induced subposet. -/
namespace FiniteChains.Comb
universe u
section Induced
variable {P : Type u} {r : P → P → Prop} (hr : IsTrans P r) (S : Set P)

abbrev subChainCx : Complex2.{u} :=
  chainCx (fun a b : S => r a.1 b.1) ⟨fun _ _ _ => hr.trans _ _ _⟩

abbrev chainSubposetIncl : Hom (subChainCx hr S) (chainCx r hr) :=
  chainCxMap Subtype.val id

/-- Restriction to an induced subcomplex, for either the weak or strict relation. -/
theorem exists_chainSubposet_chain (c : ChainTri r →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S) :
    ∃ d, chain2 (chainSubposetIncl hr S) d = c := by
  have hi := @Hom.injective_chainCx_onF S (fun a b => r a.1 b.1)
    ⟨fun _ _ _ => hr.trans _ _ _⟩ (chainCx r hr) (chainSubposetIncl hr S) Subtype.val_injective
  refine ⟨_, Finsupp.mapDomain_comapDomain _ hi c ?_⟩
  intro t ht
  obtain ⟨ha, hb, hc⟩ := hs t ht
  exact ⟨⟨(⟨t.1.1, ha⟩, ⟨t.1.2.1, hb⟩, ⟨t.1.2.2, hc⟩), t.2⟩, rfl⟩

theorem exists_chainSubposet_cycle (c : ChainTri r →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (chainCx r hr) c = 0) :
    ∃ d, chain2 (chainSubposetIncl hr S) d = c ∧ bdry2 (subChainCx hr S) d = 0 := by
  obtain ⟨d, hd⟩ := exists_chainSubposet_chain hr S c hs
  refine ⟨d, hd, ?_⟩
  let p := chainSubposetIncl hr S
  have hi := @Hom.injective_chainCx_onE S (fun a b => r a.1 b.1)
    ⟨fun _ _ _ => hr.trans _ _ _⟩ (chainCx r hr) p Subtype.val_injective
  apply Finsupp.mapDomain_injective hi
  change chain1 p (bdry2 _ d) = Finsupp.mapDomain _ 0
  rw [Finsupp.mapDomain_zero, ← bdry2_chain2, hd, hc]

end Induced

variable {P : Type u} [PartialOrder P] (S : Set P)

abbrev ordSubposetIncl : Hom (orderCx S) (orderCx P) := subposetHom (· ∈ S)

theorem exists_ordSubposet_cycle (c : OrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (orderCx P) c = 0) :
    ∃ d : OrdTri S →₀ ℤ,
      chain2 (ordSubposetIncl S) d = c ∧ bdry2 (orderCx S) d = 0 :=
  @exists_chainSubposet_cycle P (· ≤ ·) ⟨fun _ _ _ => le_trans⟩ S c hs hc

end FiniteChains.Comb
