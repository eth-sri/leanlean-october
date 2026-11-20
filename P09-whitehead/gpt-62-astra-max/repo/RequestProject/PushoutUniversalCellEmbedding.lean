module

public import RequestProject.PushoutUniversalEmbedding


@[expose] public section

/-! The actual L-copy in the universal pushout is injective on all cells.
The base map itself identifies old cells; source/base vertices and the
covering lifting uniqueness recover them. Unverified source. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.PushoutSheets
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

include hp hiV hiE in
theorem pushE_injective_at_source {e f : L.E}
    (hs : L.src e = L.src f) (hf : pushE p i e = pushE p i f) : e = f := by
  by_cases heD : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := heD
    rw [pushE_of_mem p hiE] at hf
    by_cases hfD : ∃ e, i.onE e = f
    · obtain ⟨e, rfl⟩ := hfD
      rw [pushE_of_mem p hiE] at hf
      have hh := liftGerm_unique hp.lifts (x := (d, true)) (y := (e, true)) rfl (hiV (by simp_all [i.src_onE])).symm
        (congrArg (fun z => (z, true)) (Sum.inl.inj hf))
      simp_all
    · rw [pushE_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf <;> simp_all
  · rw [pushE_of_off p i ⟨e, fun d hd => heD ⟨d, hd⟩⟩] at hf
    by_cases hfD : ∃ d, i.onE d = f
    · grind [pushE_of_mem]
    · rw [pushE_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf <;> grind

include hp hiV hiF in
theorem pushF_injective_at_base {e f : L.F}
    (hs : L.base e = L.base f) (hf : pushF p i e = pushF p i f) : e = f := by
  by_cases heD : ∃ d, i.onF d = e
  · obtain ⟨d, rfl⟩ := heD
    rw [pushF_of_mem p hiF] at hf
    by_cases hfD : ∃ e, i.onF e = f
    · obtain ⟨e, rfl⟩ := hfD
      rw [pushF_of_mem p hiF] at hf
      have hbase : D.base d = D.base e := hiV (by simp_all [i.base_onF])
      have hh := hp.lifts.cell.1 (Subtype.ext (Prod.ext (Sum.inl.inj hf) hbase))
      exact congrArg i.onF hh
    · rw [pushF_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf <;> simp_all
  · rw [pushF_of_off p i ⟨e, fun d hd => heD ⟨d, hd⟩⟩] at hf
    by_cases hfD : ∃ d, i.onF d = f
    · grind [pushF_of_mem]
    · rw [pushF_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf <;> grind

variable (hD : IsConnected D) (hL : IsConnected L) (d₀ : D.V) (ht : Pi1Trivial i)
include hD hL ht

include hp hr he in
theorem univLift_edges_injective :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onE := by
  intro e f h
  have hv :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE)
        ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => e.val.1) h)
  have hb := pushE_injective_at_source p hp i hiV hiE (e.property.symm.trans ((congrArg endV hv).trans f.property))
    (congrArg (fun e : UE (pushoutComplex p i hiV hiE)
      ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => e.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

include hp hr he in
theorem univLift_faces_injective :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onF := by
  intro e f h
  have hv :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (fun f : UF (pushoutComplex p i hiV hiE)
        ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => f.val.1) h)
  have hb := pushF_injective_at_base p hp i hiV hiF (e.property.symm.trans ((congrArg endV hv).trans f.property))
    (congrArg (fun f : UF (pushoutComplex p i hiV hiE)
      ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => f.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

end FiniteChains.Comb.PushoutSheets
