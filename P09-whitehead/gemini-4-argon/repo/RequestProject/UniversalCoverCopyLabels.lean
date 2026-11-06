module

public import RequestProject.UnivCoverCopies
public import RequestProject.DeckChainTransport

@[expose] public section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.UniversalCopy
universe u
variable {L E : Complex2.{u}} (f : Hom L E) (a : L.V)

def map (g : Pi1 E (f.onV a)) : Hom (uCover L a) (uCover E (f.onV a)) :=
  ((univDeck E (f.onV a)).cellHom g).comp (univLift L f a)

theorem projection_V (g : Pi1 E (f.onV a)) (v : UV L a) :
    endV ((map f a g).onV v) = f.onV (endV v) := by
  change endV (deckV g (univLiftV a f v)) = _
  rw [endV_deckV, endV_univLiftV]

def vertexPair (g : Pi1 E (f.onV a)) (v : UV L a) : UV E (f.onV a) × L.V :=
  ((map f a g).onV v, endV v)

def vertices (g : Pi1 E (f.onV a)) : Set (UV E (f.onV a) × L.V) :=
  Set.range (vertexPair f a g)

def label (v : UV E (f.onV a) × L.V) : Set (UV E (f.onV a) × L.V) :=
  {w | ∃ g, v ∈ vertices f a g ∧ w ∈ vertices f a g}

theorem identified_of_meet (hE : IsConnected E)
    (g h : Pi1 E (f.onV a)) (v w : UV L a)
    (hm : vertexPair f a g v = vertexPair f a h w) :
    ∃ k : Pi1 L a,
      (∀ x, (map f a g).onV x = (map f a h).onV (deckV k x)) ∧
      (∀ e, (map f a g).onE e = (map f a h).onE (deckE k e)) ∧
      (∀ t, (map f a g).onF t = (map f a h).onF (deckF k t)) := by
  obtain ⟨k, hk, _⟩ := (isRegular_univProj (X := L) (x₀ := a)).simply_transitive v w (congrArg Prod.snd hm)
  let F := map f a g; let H := (map f a h).comp ((univDeck L a).cellHom k)
  have hV := lift_onV_eq (A := F) (B := H) (isCovering_univProj hE) isConnected_univCover (fun _ => rfl)
    (by change (map f a g).onV v = (map f a h).onV (deckV k v)
        change deckV k v = w at hk; rw [hk]; exact congrArg Prod.fst hm)
  exact ⟨k, hV, lift_onE_eq (A := F) (B := H) (isCovering_univProj hE) (fun _ => rfl) hV,
    lift_onF_eq (A := F) (B := H) (isCovering_univProj hE) (fun _ => rfl) hV⟩

theorem label_on_pair (hE : IsConnected E) (g : Pi1 E (f.onV a)) (v : UV L a) :
    label f a (vertexPair f a g v) = vertices f a g := by
  ext z
  refine ⟨?_, fun hz => ⟨g, ⟨v, rfl⟩, hz⟩⟩
  rintro ⟨h, ⟨w, hw⟩, hz⟩
  obtain ⟨k, hV, _, _⟩ := identified_of_meet f a hE g h v w hw.symm
  obtain ⟨x, rfl⟩ := hz
  refine ⟨deckV k⁻¹ x, Prod.ext ?_ (endV_deckV k⁻¹ x)⟩
  simpa only [← deckV_mul, mul_inv_cancel, deckV_one, vertexPair, map] using hV (deckV k⁻¹ x)

theorem vertices_nonempty (g : Pi1 E (f.onV a)) : (vertices f a g).Nonempty :=
  ⟨vertexPair f a g (UV.base L a), ⟨UV.base L a, rfl⟩⟩

theorem vertices_covered (hL : IsConnected L) (v : UV E (f.onV a)) (l : L.V)
    (hv : endV v = f.onV l) : ∃ g x, vertexPair f a g x = (v, l) := by
  obtain ⟨x, hx⟩ := endV_surjective (x₀ := a) hL l
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := E) (x₀ := f.onV a)).simply_transitive
    (univLiftV a f x) v (by show endV (univLiftV a f x) = endV v; rw [endV_univLiftV, hx, hv])
  exact ⟨g, x, Prod.ext hg hx⟩

theorem faces_covered (hL : IsConnected L) (t : UF E (f.onV a)) (l : L.F)
    (ht : t.val.2 = f.onF l) :
    ∃ (g : Pi1 E (f.onV a)) (x : UF L a), (map f a g).onF x = t ∧ x.val.2 = l := by
  obtain ⟨g, x, hx⟩ := vertices_covered f a hL t.val.1 (L.base l) (by rw [t.property, ht, f.base_onF])
  exact ⟨g, ⟨(x, l), congrArg Prod.snd hx⟩,
    Subtype.ext (Prod.ext (congrArg Prod.fst hx : (map f a g).onV x = t.val.1) ht.symm), rfl⟩

theorem face_range_of_label (hE : IsConnected E) (hL : IsConnected L)
    (g : Pi1 E (f.onV a)) (t : UF E (f.onV a)) (l : L.F)
    (ht : t.val.2 = f.onF l)
    (hl : label f a (t.val.1, L.base l) = vertices f a g) :
    t ∈ Set.range (map f a g).onF := by
  obtain ⟨h, x, hx, hxl⟩ := faces_covered f a hL t l ht
  have hp : vertexPair f a h x.val.1 = (t.val.1, L.base l) :=
    Prod.ext (congrArg (fun t : UF E (f.onV a) => t.val.1) hx) (x.property.trans (congrArg L.base hxl))
  have hvg : vertices f a h = vertices f a g := (label_on_pair f a hE h x.val.1).symm.trans (hp ▸ hl)
  obtain ⟨y, hy⟩ : vertexPair f a h x.val.1 ∈ vertices f a g := hvg ▸ ⟨x.val.1, rfl⟩
  obtain ⟨k, _, _, hkF⟩ := identified_of_meet f a hE h g x.val.1 y hy.symm
  exact ⟨deckF k x, (hkF x).symm.trans hx⟩

theorem map_injective_E (hE : Function.Injective (univLift L f a).onE)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onE :=
  fun e t h => hE <| by
    have hh := congrArg ((univDeck E (f.onV a)).smulE g⁻¹) h
    change (univDeck E (f.onV a)).smulE g⁻¹ ((univDeck E (f.onV a)).smulE g ((univLift L f a).onE e)) =
      (univDeck E (f.onV a)).smulE g⁻¹ ((univDeck E (f.onV a)).smulE g ((univLift L f a).onE t)) at hh
    simpa only [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE] using hh

theorem map_injective_F (hF : Function.Injective (univLift L f a).onF)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onF :=
  fun e t h => hF <| by
    have hh := congrArg ((univDeck E (f.onV a)).smulF g⁻¹) h
    change (univDeck E (f.onV a)).smulF g⁻¹ ((univDeck E (f.onV a)).smulF g ((univLift L f a).onF e)) =
      (univDeck E (f.onV a)).smulF g⁻¹ ((univDeck E (f.onV a)).smulF g ((univLift L f a).onF t)) at hh
    simpa only [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF] using hh

theorem cycle_image_mem (g : Pi1 E (f.onV a)) (c : UF L a →₀ ℤ)
    (hc : bdry2 (uCover L a) c = 0) : chain2 (map f a g) c ∈ Pi2FromSub f (f.onV a) :=
  ⟨a, map f a g, projection_V f a g, fun _ => rfl, fun _ => rfl, c, hc, rfl⟩
