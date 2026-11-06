import RequestProject.PushoutUniversalEmbedding
import RequestProject.CombCoveringLift


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
      have hsrc : D.src d = D.src e := hiV (by simp_all [i.src_onE])
      have hproj := Sum.inl.inj hf
      have hh := liftGerm_unique hp (x := (d, true)) (y := (e, true)) rfl hsrc.symm
        (by simp_all)
      simp_all
    · simp_all [pushE_of_off p i ⟨f, by simp_all⟩]
  · rw [pushE_of_off p i ⟨e, by simp_all⟩] at hf
    by_cases hfD : ∃ d, i.onE d = f
    · grind [pushE_of_mem p hiE]
    · grind [pushE_of_off p i ⟨f, by simp_all⟩]

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
      have hproj := Sum.inl.inj hf
      have hh : d = e := hp.cell.1 (by aesop)
      simp_all
    · simp_all [pushF_of_off p i ⟨f, by simp_all⟩]
  · rw [pushF_of_off p i ⟨e, by simp_all⟩] at hf
    by_cases hfD : ∃ d, i.onF d = f
    · grind [pushF_of_mem p hiF]
    · grind [pushF_of_off p i ⟨f, by simp_all⟩]

include hp hr he in
theorem univLift_edges_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onE := by
  intro e f h
  have hv :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (·.val.1) h)
  have hs : L.src e.val.2 = L.src f.val.2 :=
    by grind
  have hb := pushE_injective_at_source p hp i hiV hiE hs
    (congrArg (·.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

include hp hr he in
theorem univLift_faces_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onF := by
  intro e f h
  have hv :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (·.val.1) h)
  have hs : L.base e.val.2 = L.base f.val.2 :=
    by grind
  have hb := pushF_injective_at_base p hp i hiV hiF hs
    (congrArg (·.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)
