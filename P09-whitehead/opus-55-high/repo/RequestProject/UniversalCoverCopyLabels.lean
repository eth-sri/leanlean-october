import RequestProject.UnivCoverCopies
import RequestProject.DeckChainTransport
import RequestProject.Tac


/-! Actual components of the pullback of a universal cover to L, described
without choosing coset representatives.  The label keeps the L-vertex as
well as its universal-cover image, which matters when a pushout identifies
distinct old vertices. Unverified source. -/

noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Comb.UniversalCopy
universe u
variable {L E : Complex2.{u}} (f : Hom L E) (a : L.V)

def map (g : Pi1 E (f.onV a)) :=
  ((univDeck E _).cellHom g).comp (univLift L f a)

theorem projection_V g (v : UV L a) :
    endV ((map f a g).onV v) = f.onV (endV v) := by
  change endV (deckV g (univLiftV a f v)) = _
  simp

theorem projection_E g (e : UE L a) :
    ((map f a g).onE e).val.2 = f.onE e.val.2 := rfl

theorem projection_F g (e : UF L a) :
    ((map f a g).onF e).val.2 = f.onF e.val.2 := rfl

def vertexPair (g : Pi1 E (f.onV a)) (v : UV L a) : UV E (f.onV a) × L.V :=
  ((map f a g).onV v, endV v)

def vertices (g : Pi1 E (f.onV a)) :=
  Set.range (vertexPair f a g)

def label (v : UV E (f.onV a) × L.V) :=
  {w | ∃ g, v ∈ vertices f a g ∧ w ∈ vertices f a g}

theorem identified_of_meet (hE : IsConnected E)
    g h v w
    (hm : vertexPair f a g v = vertexPair f a h w) :
    ∃ k,
      (∀ x, (map f a g).onV x = (map f a h).onV (deckV k x)) ∧
      (∀ e, (map f a g).onE e = (map f a h).onE (deckE k e)) ∧
      (∀ t, (map f a g).onF t = (map f a h).onF (deckF k t)) := by
  have hend := congrArg Prod.snd hm
  obtain ⟨k, hk, _⟩ := (isRegular_univProj (X := L) (x₀ := a)).simply_transitive v w hend
  let F := map f a g
  let H := (map f a h).comp ((univDeck L a).cellHom k)
  have hprojE : ∀ e, (univProj E _).onE (F.onE e) =
      (univProj E _).onE (H.onE e) := by tauto
  have hprojF : ∀ t, (univProj E _).onF (F.onF t) =
      (univProj E _).onF (H.onF t) := by tauto
  have hb : F.onV v = H.onV v := by
    change (map f a g).onV v = (map f a h).onV (deckV k v)
    change deckV k v = w at hk
    rw [hk]
    exact congrArg Prod.fst hm
  have hV := lift_onV_eq (isCovering_univProj hE) isConnected_univCover hprojE hb
  exact ⟨k, hV, lift_onE_eq (isCovering_univProj hE) hprojE hV,
    lift_onF_eq (isCovering_univProj hE) hprojF hV⟩

theorem vertices_eq_of_meet (hE : IsConnected E)
    g h v w
    (hm : vertexPair f a g v = vertexPair f a h w) : vertices f a g = vertices f a h := by
  obtain ⟨k, hV, _, _⟩ := identified_of_meet f a hE g h v w hm
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨deckV k x, Prod.ext (hV x).symm (endV_deckV k x)⟩
  · rintro ⟨x, rfl⟩
    refine ⟨deckV k⁻¹ x, Prod.ext ?_ (endV_deckV _ x)⟩
    simp_all [← deckV_mul, mul_inv_cancel, deckV_one, vertexPair, map]

theorem label_on_pair (hE : IsConnected E) g v :
    label f a (vertexPair f a g v) = vertices f a g := by
  ext z
  constructor
  · rintro ⟨h, ⟨w, hw⟩, hz⟩
    grind [vertices_eq_of_meet f a hE g h v w hw.symm]
  · intro hz
    exact ⟨g, ⟨v, rfl⟩, hz⟩

theorem vertices_nonempty g : (vertices f a g).Nonempty :=
  ⟨vertexPair f a g (UV.base L a), ⟨UV.base L a, rfl⟩⟩

theorem vertices_covered (hL : IsConnected L) v l
    (hv : endV v = f.onV l) : ∃ g x, vertexPair f a g x = (v, l) := by
  cases' endV_surjective (x₀ := a) hL l with x hx
  have hproj : endV (univLiftV a f x) = endV v := by
    simp_all
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := E) (x₀ := f.onV a)).simply_transitive _ _ hproj
  aesop

theorem faces_covered (hL : IsConnected L) (t : UF E (f.onV a)) l
    (ht : t.val.2 = f.onF l) :
    ∃ (g : Pi1 E (f.onV a)) (x : UF L a), (map f a g).onF x = t ∧ x.val.2 = l := by
  have hv : endV t.val.1 = f.onV (L.base l) := by
    rw [t.property, ht, f.base_onF]
  obtain ⟨g, x, hx⟩ := vertices_covered f a hL t.val.1 _ hv
  let t' : UF L a := ⟨(x, l), congrArg Prod.snd hx⟩
  refine ⟨g, t', ?_, rfl⟩
  apply Subtype.ext
  have hv' : (map f a g).onV x = t.val.1 :=
    congrArg (·.1) hx
  aesop

theorem face_range_of_label (hE : IsConnected E) (hL : IsConnected L)
    g (t : UF E (f.onV a)) l
    (ht : t.val.2 = f.onF l)
    (hl : label f a (t.val.1, L.base l) = vertices f a g) :
    t ∈ Set.range (map f a g).onF := by
  obtain ⟨h, x, hx, hxl⟩ := faces_covered f a hL t l ht
  have hp : vertexPair f a h x.val.1 = (t.val.1, L.base l) := by
    apply Prod.ext
    · aesop
    · exact x.property.trans (congrArg L.base hxl)
  have hvg : vertices f a h = vertices f a g := by
    rw [← label_on_pair f a hE h x.val.1, hp]
    exact hl
  have hmem : vertexPair f a h x.val.1 ∈ vertices f a g := by
    rw [← hvg]
    exact ⟨x.val.1, rfl⟩
  cases' hmem with y hy
  obtain ⟨k, _, _, hkF⟩ := identified_of_meet f a hE h g x.val.1 y hy.symm
  aesop

theorem map_injective_E (hE : Function.Injective (univLift L f a).onE)
    g : Function.Injective (map f a g).onE := by
  intro e t h
  apply hE
  have hh := congrArg ((univDeck E (f.onV a)).smulE g⁻¹) h
  change (univDeck E _).smulE g⁻¹
      ((univDeck E _).smulE g ((univLift L f a).onE e)) =
    (univDeck E _).smulE g⁻¹
      ((univDeck E _).smulE g ((univLift L f a).onE t)) at hh
  simp_all [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE]

theorem map_injective_F (hF : Function.Injective (univLift L f a).onF)
    g : Function.Injective (map f a g).onF := by
  intro e t h
  apply hF
  have hh := congrArg ((univDeck E (f.onV a)).smulF g⁻¹) h
  change (univDeck E _).smulF g⁻¹
      ((univDeck E _).smulF g ((univLift L f a).onF e)) =
    (univDeck E _).smulF g⁻¹
      ((univDeck E _).smulF g ((univLift L f a).onF t)) at hh
  simp_all [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF]

theorem cycle_image_mem g (c : UF L a →₀ ℤ)
    (hc : bdry2 (uCover L a) c = 0) : chain2 (map f a g) c ∈ Pi2FromSub f (f.onV a) :=
  ⟨a, map f a g, projection_V f a g, projection_E f a g,
    projection_F f a g, c, hc, rfl⟩
