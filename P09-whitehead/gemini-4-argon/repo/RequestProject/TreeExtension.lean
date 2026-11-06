module

public import RequestProject.TreePresentation

@[expose] public section

noncomputable section
namespace FiniteChains.Comb.SpanningTree

universe u

variable {X Y : Complex2.{u}}

section

def imReach (h : Hom X Y) (a : Y.V) : Set ℕ :=
  {n | ∃ p : List (Y.E × Bool), p.length = n ∧ ∃ x : X.V, IsPath Y.src Y.tgt p a (h.onV x)}

def imDist (h : Hom X Y) (a : Y.V) : ℕ := sInf (imReach h a)

variable (h : Hom X Y) (hconn : IsConnected Y) (x₀ : X.V)

include hconn x₀ in
theorem imDist_mem (a : Y.V) : imDist h a ∈ imReach h a :=
  let ⟨p, hp⟩ := hconn a (h.onV x₀)
  Nat.sInf_mem ⟨p.length, p, rfl, x₀, hp⟩

theorem imDist_le {a : Y.V} {p : List (Y.E × Bool)} {x : X.V}
    (hp : IsPath Y.src Y.tgt p a (h.onV x)) : imDist h a ≤ p.length :=
  Nat.sInf_le ⟨p, rfl, x, hp⟩

theorem imDist_image (x : X.V) : imDist h (h.onV x) = 0 :=
  Nat.le_zero.1 (imDist_le h (p := []) (x := x) rfl)

include hconn x₀ in
theorem exists_pre {a : Y.V} (hz : imDist h a = 0) : ∃ x : X.V, a = h.onV x := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  rw [hz, List.length_eq_zero_iff] at hlen; subst hlen; exact ⟨x, hp⟩

def imPre {a : Y.V} (hz : imDist h a = 0) : X.V :=
  (exists_pre h hconn x₀ hz).choose

theorem imPre_spec {a : Y.V} (hz : imDist h a = 0) :
    a = h.onV (imPre h hconn x₀ hz) :=
  (exists_pre h hconn x₀ hz).choose_spec

include hconn x₀ in
theorem imDist_step {a : Y.V} (ha : imDist h a ≠ 0) :
    ∃ g : Y.E × Bool, germSrc Y.src Y.tgt g = a ∧
      imDist h (germTgt Y.src Y.tgt g) + 1 = imDist h a := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  rcases p with _ | ⟨g, q⟩
  · exact absurd hlen.symm ha
  · obtain ⟨hgs, hq⟩ := hp
    obtain ⟨q', hlen', x', hq'⟩ := imDist_mem h hconn x₀ (germTgt Y.src Y.tgt g)
    have h1 := imDist_le h hq
    have h2 := imDist_le h (p := g :: q') ⟨hgs, hq'⟩
    exact ⟨g, hgs.symm, by simp [hlen'] at hlen h2; omega⟩

def upChoice {a : Y.V} (ha : imDist h a ≠ 0) : Y.E × Bool :=
  (imDist_step h hconn x₀ ha).choose

theorem upChoice_src {a : Y.V} (ha : imDist h a ≠ 0) :
    germSrc Y.src Y.tgt (upChoice h hconn x₀ ha) = a :=
  (imDist_step h hconn x₀ ha).choose_spec.1

theorem upChoice_dist {a : Y.V} (ha : imDist h a ≠ 0) :
    imDist h (germTgt Y.src Y.tgt (upChoice h hconn x₀ ha)) + 1 = imDist h a :=
  (imDist_step h hconn x₀ ha).choose_spec.2

variable (T : SpanningTree X)

def extHt (a : Y.V) : ℕ :=
  if hz : imDist h a = 0 then T.ht (imPre h hconn x₀ hz)
  else extHt (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1
  termination_by imDist h a
  decreasing_by have := upChoice_dist h hconn x₀ hz; omega

include hconn x₀ in
theorem extHt_image (hV : Function.Injective h.onV) (x : X.V) :
    extHt h hconn x₀ T (h.onV x) = T.ht x := by
  have hz := imDist_image h x
  rw [extHt, dif_pos hz, hV (imPre_spec h hconn x₀ hz).symm]

theorem imPre_ne_root {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a = 0) :
    imPre h hconn x₀ hz ≠ T.root := fun hr =>
  ha ((imPre_spec h hconn x₀ hz).trans (congrArg h.onV hr))

def extUp (a : Y.V) (ha : a ≠ h.onV T.root) : Y.E × Bool :=
  if hz : imDist h a = 0 then
    (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
      (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).2)
  else upChoice h hconn x₀ hz

def extend (hV : Function.Injective h.onV) : SpanningTree Y where
  root := h.onV T.root
  ht := extHt h hconn x₀ T
  isTree e := ∃ (a : Y.V) (ha : a ≠ h.onV T.root), (extUp h hconn x₀ T a ha).1 = e
  up := extUp h hconn x₀ T
  ht_root := by rw [extHt_image h hconn x₀ T hV, T.ht_root]
  ht_eq_zero a ha := by
    rw [extHt] at ha
    split_ifs at ha with hz
    exact (imPre_spec h hconn x₀ hz).trans (congrArg h.onV (T.ht_eq_zero _ ha))
  up_src a ha := by
    rw [extUp]; split_ifs with hz
    · rw [germSrc_onE h, T.up_src]; exact (imPre_spec h hconn x₀ hz).symm
    · exact upChoice_src h hconn x₀ hz
  up_ht a ha := by
    rw [extUp]; conv_rhs => rw [extHt]
    split_ifs with hz
    · rw [germTgt_onE h, extHt_image h hconn x₀ T hV]; exact T.up_ht _ _
    · rfl
  isTree_iff _ := Iff.rfl

include hconn x₀ in
theorem exists_extension (hV : Function.Injective h.onV) (hE : Function.Injective h.onE) :
    ∃ T' : SpanningTree Y, T'.root = h.onV T.root ∧
      ∀ e : X.E, (T'.isTree (h.onE e) ↔ T.isTree e) := by
  refine ⟨extend h hconn x₀ T hV, rfl, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, hae⟩
    rw [extUp] at hae; split_ifs at hae with hz
    · exact (T.isTree_iff e).2 ⟨_, imPre_ne_root h hconn x₀ T ha hz, hE hae⟩
    · exfalso; apply hz
      have hsrc := upChoice_src h hconn x₀ hz
      rcases hup : upChoice h hconn x₀ hz with ⟨_, b⟩
      rw [hup] at hae hsrc; subst hae
      rw [← hsrc, germSrc_onE h (e, b)]
      exact imDist_image h _
  · intro he
    obtain ⟨x, hx, hxe⟩ := (T.isTree_iff e).1 he
    have hne : h.onV x ≠ h.onV T.root := fun hc => hx (hV hc)
    have hz := imDist_image h x
    refine ⟨h.onV x, hne, ?_⟩
    rw [extUp, dif_pos hz]
    have key : ∀ (y : X.V) (hy : y ≠ T.root), y = x → (T.up y hy).1 = e := by rintro _ _ rfl; exact hxe
    exact congrArg h.onE (key _ _ (hV (imPre_spec h hconn x₀ hz)).symm)

end

variable {h : Hom X Y} {T : SpanningTree X} {T' : SpanningTree Y}
  (hiff : ∀ e : X.E, T'.isTree (h.onE e) ↔ T.isTree e)

def nonTreeIncl (e : NonTree T) : NonTree T' :=
  ⟨h.onE e.1, fun hc => e.2 ((hiff e.1).1 hc)⟩

theorem nonTreeIncl_injective (hE : Function.Injective h.onE) :
    Function.Injective (nonTreeIncl hiff) :=
  fun _ _ hab => Subtype.ext (hE (congrArg Subtype.val hab))

theorem pathWord_mapPath (l : List (X.E × Bool)) :
    pathWord T' (mapPath h l) = FreeGroup.map (nonTreeIncl hiff) (pathWord T l) := by
  have hg (g : X.E × Bool) :
      germWord T' (h.onE g.1, g.2) = FreeGroup.map (nonTreeIncl hiff) (germWord T g) := by
    classical
    rcases g with ⟨e, _ | _⟩ <;> by_cases hT : T.isTree e <;>
      simp [germWord, hT, (hiff e).trans ⟨id, id⟩, nonTreeIncl]
  induction l with
  | nil => simp [mapPath]
  | cons g l ih =>
      change pathWord T' ((h.onE g.1, g.2) :: mapPath h l) = _
      rw [pathWord_cons, ih, hg g, pathWord_cons, map_mul]

theorem treeRel_onF (f : X.F) :
    treeRel T' (h.onF f) = FreeGroup.map (nonTreeIncl hiff) (treeRel T f) := by
  rw [treeRel, h.att_onF f]
  exact pathWord_mapPath hiff (X.att f)
