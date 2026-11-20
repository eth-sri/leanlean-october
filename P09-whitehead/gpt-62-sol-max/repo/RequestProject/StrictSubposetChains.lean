module

public import RequestProject.StrictOrderChains
public import RequestProject.OrderSubposetChains

@[expose] public section

/-! Finite chains and cycles on an actual induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (S : Set P)

def strictSubposetIncl : Hom (strictOrderCx S) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

theorem strictSubposetIncl_onE_injective :
    Function.Injective (strictSubposetIncl S).onE :=
  @Hom.injective_chainCx_onE S (· < ·) ⟨fun _ _ _ => lt_trans⟩ (strictOrderCx P)
    (strictSubposetIncl S) Subtype.val_injective

theorem exists_strictSubposet_chain (c : StrictOrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S) :
    ∃ d : StrictOrdTri S →₀ ℤ, chain2 (strictSubposetIncl S) d = c :=
  @exists_chainSubposet_chain P (· < ·) ⟨fun _ _ _ => lt_trans⟩ S c hs

theorem exists_strictSubposet_cycle (c : StrictOrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri S →₀ ℤ,
      chain2 (strictSubposetIncl S) d = c ∧ bdry2 (strictOrderCx S) d = 0 :=
  @exists_chainSubposet_cycle P (· < ·) ⟨fun _ _ _ => lt_trans⟩ S c hs hc

end FiniteChains.Comb
