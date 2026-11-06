module

public import RequestProject.PushoutUniversalEmbedding
public import RequestProject.ZeroPi2Descent
public import RequestProject.CellularChainMapZero
public import RequestProject.DeckChainTransport

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u v

section
variable {D X : Complex2.{u}} (f : Hom D X)
  (hV : Function.Injective f.onV) (hE : Function.Injective f.onE)
  (hF : Function.Injective f.onF) (hD : IsAcyclic D)

include hV hE hD in
theorem embedded_one_cycle_filling (z : X.E →₀ ℤ)
    (hs : ∀ e ∉ Set.range f.onE, z e = 0) (hz : bdry1 X z = 0) :
    ∃ y : X.F →₀ ℤ, (∀ g ∉ Set.range f.onF, y g = 0) ∧ bdry2 X y = z := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_range_mapDomain_iff f.onE hE z).mpr hs
  obtain ⟨d, hd⟩ := hD.h1 c (Finsupp.mapDomain_injective hV
    (show chain0 f (bdry1 D c) = Finsupp.mapDomain f.onV 0 by erw [← bdry1_chain1, hz]; rfl))
  exact ⟨chain2 f d, fun g hg => Finsupp.mapDomain_notin_range d g hg, by rw [bdry2_chain2, hd]; rfl⟩

include hE hF hD in
theorem embedded_two_cycle_zero (z : X.F →₀ ℤ)
    (hs : ∀ e ∉ Set.range f.onF, z e = 0) (hz : bdry2 X z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_range_mapDomain_iff f.onF hF z).mpr hs
  have hc0 : c = 0 := hD.h2 ((Finsupp.mapDomain_injective hE
    (show chain1 f (bdry2 D c) = Finsupp.mapDomain f.onE 0 by erw [← bdry2_chain2, hz]; rfl)).trans
    (map_zero _).symm)
  rw [hc0, Finsupp.mapDomain_zero]
end

namespace PushoutOldCover
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

def oldMap : Hom D (pushoutComplex p i hiV hiE) := (pushoutInl p i hiV hiE).comp p

def oldLift : Hom D (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :=
  liftHom (f := oldMap p i hiV hiE) (d₀ := d₀) hconn (by
    change Pi1Trivial ((pushoutInl p i hiV hiE).comp p)
    rw [← pushout_comm p i hiV hiE hiF]
    exact Pi1Trivial.comp_left _ ht)

include hp hr he in
theorem oldLift_injective_V : Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onV := by
  have hread (d : D.V) :
      EdgeLabels.vertexRead (PushoutSheets.labels p hp a hr i hiV hiE)
        (PushoutSheets.labels_rel p hp a hr he i hiV hiE hiF) (Sum.inl (p.onV d₀))
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) =
        (RegularCoverLabels.sheet p hp a hr d₀)⁻¹ * RegularCoverLabels.sheet p hp a hr d := by
    change EdgeLabels.read (PushoutSheets.labels p hp a hr i hiV hiE)
      (mapPath (oldMap p i hiV hiE) (cPath hconn d₀ d)) = _
    rw [oldMap, ← mapPath_comp, EdgeLabels.read_mapPath]
    exact RegularCoverLabels.read_projected_path p hp a hr he (cPath_isPath hconn d₀ d)
  intro d e h
  have h' : endV (liftV (oldMap p i hiV hiE) hconn d₀ d) =
      endV (liftV (oldMap p i hiV hiE) hconn d₀ e) := congrArg endV h
  rw [endV_liftV, endV_liftV] at h'
  have hs := congrArg (EdgeLabels.vertexRead (PushoutSheets.labels p hp a hr i hiV hiE)
    (PushoutSheets.labels_rel p hp a hr he i hiV hiE hiF) (Sum.inl (p.onV d₀))) h
  rw [hread d, hread e] at hs
  exact RegularCoverLabels.sheet_fibre_injective p hp a hr (Sum.inl.inj h') (mul_left_cancel hs)

def translatedOldLift (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Hom D (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :=
  ((univDeck _ _).cellHom g).comp (oldLift p i hiV hiE hiF hconn d₀ ht)

include hp hr he in
theorem translatedOldLift_injective_E (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE := by
  intro x y h
  have h' := congrArg ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹) h
  change (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onE x)) =
    (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onE y)) at h'
  simp only [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE] at h'
  exact congrArg Prod.fst (liftGerm_unique hp (x := (x, true)) (y := (y, true)) rfl
    (oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.1) h')).symm
    (congrArg (·, true) (Sum.inl.inj
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.2) h'))))

include hp hr he in
theorem translatedOldLift_injective_F (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF := by
  intro x y h
  have h' := congrArg ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹) h
  change (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onF x)) =
    (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onF y)) at h'
  simp only [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF] at h'
  exact hp.cell.1 (Subtype.ext (Prod.ext
    (Sum.inl.inj (congrArg (fun e : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.2) h'))
    (oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
      (congrArg (fun e : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.1) h'))))

end PushoutOldCover
end FiniteChains.Comb
