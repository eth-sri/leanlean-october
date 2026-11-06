module

public import RequestProject.CombData

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb

universe u

variable {A X Y Z : Complex2.{u}}

def Reach (X : Complex2.{u}) (x₀ v : X.V) : Prop := ∃ p, IsPath X.src X.tgt p x₀ v

theorem reach_self (X : Complex2.{u}) (x₀ : X.V) : Reach X x₀ x₀ := ⟨[], rfl⟩

theorem Reach.trans_path {x₀ a b : X.V} (h : Reach X x₀ a) {p : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) : Reach X x₀ b :=
  let ⟨q, hq⟩ := h; ⟨q ++ p, hq.append hp⟩

theorem Reach.src_of_germSrc {x₀ : X.V} {eb : X.E × Bool}
    (h : Reach X x₀ (germSrc X.src X.tgt eb)) : Reach X x₀ (X.src eb.1) := by
  rcases eb with ⟨e, false | true⟩
  · exact h.trans_path (p := [(e, false)]) ⟨rfl, rfl⟩
  · exact h

theorem Reach.germSrc_of_src {x₀ : X.V} {eb : X.E × Bool}
    (h : Reach X x₀ (X.src eb.1)) : Reach X x₀ (germSrc X.src X.tgt eb) := by
  rcases eb with ⟨e, false | true⟩
  · exact h.trans_path (p := [(e, true)]) ⟨rfl, rfl⟩
  · exact h

theorem reach_of_mem_path {x₀ : X.V} :
    ∀ {l : List (X.E × Bool)} {a b : X.V}, IsPath X.src X.tgt l a b → Reach X x₀ a →
      ∀ eb ∈ l, Reach X x₀ (X.src eb.1)
  | [], _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | eb :: _, _, _, hl, ha, eb', hm => by
      have ha' : Reach X x₀ (germSrc X.src X.tgt eb) := hl.1 ▸ ha
      rcases List.mem_cons.mp hm with rfl | h
      · exact ha'.src_of_germSrc
      · exact reach_of_mem_path hl.2 (ha'.trans_path (p := [eb]) ⟨rfl, rfl⟩) eb' h

variable (X) in
def CV (x₀ : X.V) : Type u := {v : X.V // Reach X x₀ v}
variable (X) in
def CE (x₀ : X.V) : Type u := {e : X.E // Reach X x₀ (X.src e)}
variable (X) in
def CF (x₀ : X.V) : Type u := {f : X.F // Reach X x₀ (X.base f)}

variable {x₀ : X.V}

def cSrc (e : CE X x₀) : CV X x₀ := ⟨X.src e.1, e.2⟩
def cTgt (e : CE X x₀) : CV X x₀ := ⟨X.tgt e.1, e.2.trans_path (p := [(e.1, true)]) ⟨rfl, rfl⟩⟩

open Classical in
def liftGerms (X : Complex2.{u}) (x₀ : X.V) (l : List (X.E × Bool)) : List (CE X x₀ × Bool) :=
  l.filterMap fun eb => if h : Reach X x₀ (X.src eb.1) then some (⟨eb.1, h⟩, eb.2) else none

@[simp] theorem liftGerms_append (X : Complex2.{u}) (x₀ : X.V) (l l' : List (X.E × Bool)) :
    liftGerms X x₀ (l ++ l') = liftGerms X x₀ l ++ liftGerms X x₀ l' := by
  simp [liftGerms, List.filterMap_append]

theorem liftGerms_cons {eb : X.E × Bool} (h : Reach X x₀ (X.src eb.1)) (l : List (X.E × Bool)) :
    liftGerms X x₀ (eb :: l) = ((⟨eb.1, h⟩ : CE X x₀), eb.2) :: liftGerms X x₀ l := by
  classical simp [liftGerms, h]

def cForget (eb : CE X x₀ × Bool) : X.E × Bool := (eb.1.1, eb.2)

@[simp] theorem liftGerms_map_cForget : ∀ L : List (CE X x₀ × Bool),
    liftGerms X x₀ (L.map cForget) = L
  | [] => rfl
  | eb :: L => by rw [List.map_cons, liftGerms_cons eb.1.2, liftGerms_map_cForget L]; rfl

theorem map_cForget_liftGerms : ∀ {l : List (X.E × Bool)},
    (∀ eb ∈ l, Reach X x₀ (X.src eb.1)) → (liftGerms X x₀ l).map cForget = l
  | [], _ => rfl
  | eb :: l, h => by
      rw [liftGerms_cons (h eb List.mem_cons_self), List.map_cons,
        map_cForget_liftGerms fun e he => h e (List.mem_cons_of_mem _ he)]; rfl

theorem isPath_liftGerms :
    ∀ {l : List (X.E × Bool)} {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b),
      IsPath X.src X.tgt l a b →
        IsPath (cSrc (X := X) (x₀ := x₀)) cTgt (liftGerms X x₀ l) ⟨a, ha⟩ ⟨b, hb⟩
  | [], _, _, _, _, hl => Subtype.ext hl
  | ⟨e, b⟩ :: _, _, _, ha, hb, hl => by
      have hsrc : Reach X x₀ (X.src e) := (hl.1 ▸ ha).src_of_germSrc
      have htgt : Reach X x₀ (germTgt X.src X.tgt (e, b)) :=
        (hl.1 ▸ ha).trans_path (p := [(e, b)]) ⟨rfl, rfl⟩
      rw [liftGerms_cons hsrc]
      refine ⟨by cases b <;> exact Subtype.ext hl.1, ?_⟩
      simpa [show germTgt cSrc cTgt (⟨e, hsrc⟩, b) = ⟨germTgt X.src X.tgt (e, b), htgt⟩ by
        cases b <;> rfl] using isPath_liftGerms htgt hb hl.2

variable (X) in
def component (x₀ : X.V) : Complex2.{u} where
  V := CV X x₀
  E := CE X x₀
  F := CF X x₀
  src := cSrc
  tgt := cTgt
  base f := ⟨X.base f.1, f.2⟩
  att f := liftGerms X x₀ (X.att f.1)
  att_isLoop f := isPath_liftGerms f.2 f.2 (X.att_isLoop f.1)

instance (x₀ : X.V) [Finite X.E] : Finite (component X x₀).E := by
  show Finite (CE X x₀); unfold CE; infer_instance

instance (x₀ : X.V) [Finite X.F] : Finite (component X x₀).F := by
  show Finite (CF X x₀); unfold CF; infer_instance

theorem component_isConnected (x₀ : X.V) : IsConnected (component X x₀) :=
  fun ⟨_, p, hp⟩ ⟨_, q, hq⟩ =>
    ⟨liftGerms X x₀ (revPath p ++ q), isPath_liftGerms _ _ ((isPath_revPath hp).append hq)⟩

variable (X) in
def componentIncl (x₀ : X.V) : Hom (component X x₀) X where
  onV := Subtype.val
  onE := Subtype.val
  onF := Subtype.val
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (map_cForget_liftGerms (reach_of_mem_path (X.att_isLoop f.1) f.2)).symm

theorem componentIncl_injective_onF (x₀ : X.V) :
    Function.Injective (componentIncl X x₀).onF := fun _ _ h => Subtype.ext h

theorem Hom.ext' {f g : Hom X Y} (hV : f.onV = g.onV) (hE : f.onE = g.onE)
    (hF : f.onF = g.onF) : f = g := by
  cases f; cases g; cases hV; cases hE; cases hF; rfl

theorem step_liftGerms {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b)
    {l l' : List (X.E × Bool)} (hstep : Step X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hPl := isPath_liftGerms ha hb hl
  have hPl' := isPath_liftGerms ha hb hl'
  rcases hc with ⟨p, q, eb, hlEq, hl'Eq⟩ | ⟨p, q, f, hlEq, hl'Eq⟩
  · have hsrc := reach_of_mem_path hl ha eb (hlEq ▸ List.mem_append_right _ List.mem_cons_self)
    refine Htpy.of_step ⟨hPl, hPl', Or.inl ⟨liftGerms X x₀ p, liftGerms X x₀ q,
      (⟨eb.1, hsrc⟩, eb.2), ?_, by rw [hl'Eq, liftGerms_append]⟩⟩
    rw [hlEq, liftGerms_append, liftGerms_cons hsrc, liftGerms_cons (eb := revGerm eb) hsrc]; rfl
  · cases hx : X.att f with
    | nil => rw [show liftGerms X x₀ l = liftGerms X x₀ l' by rw [hlEq, hl'Eq, hx]; simp]
    | cons eb t =>
      have hsrc := reach_of_mem_path hl ha eb (by rw [hlEq, hx]; simp)
      have hloop := X.att_isLoop f; rw [hx] at hloop
      refine Htpy.of_step ⟨hPl, hPl', Or.inr ⟨liftGerms X x₀ p, liftGerms X x₀ q,
        ⟨f, hloop.1 ▸ hsrc.germSrc_of_src⟩,
        by rw [hlEq, liftGerms_append, liftGerms_append]; rfl, by rw [hl'Eq, liftGerms_append]⟩⟩

theorem htpy_liftGerms {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b)
    {l l' : List (X.E × Bool)} (h : Htpy X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  induction h with
  | refl => exact Htpy.refl _
  | tail _ hstep ih =>
      exact ih.trans (hstep.elim (step_liftGerms ha hb) fun hs => (step_liftGerms ha hb hs).symm)

theorem mapPath_componentIncl (x₀ : X.V) (l : List ((component X x₀).E × Bool)) :
    mapPath (componentIncl X x₀) l = l.map cForget := rfl

theorem univLiftF_comp (g : Hom Y Z) (f : Hom X Y) (x₀ : X.V) (F : UF X x₀) :
    univLiftF (f.onV x₀) g (univLiftF x₀ f F) = univLiftF x₀ (g.comp f) F := by
  rcases F with ⟨⟨c, _⟩, _⟩
  refine Subtype.ext (Prod.ext ?_ rfl)
  induction c using UV.ind with | h p =>
  refine Quotient.sound ?_
  show Htpy Z _ _ (mapPath g (mapPath f p.1)) (mapPath (g.comp f) p.1)
  simp only [mapPath, List.map_map]; exact Htpy.refl _

theorem zeroPi2_comp_right (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 g) :
    ZeroPi2 (g.comp f) := by
  intro x₀ c hc
  show Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c = 0
  rw [show Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c =
      Finsupp.mapDomain (univLift Y g (f.onV x₀)).onF (Finsupp.mapDomain (univLift X f x₀).onF c) by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun F _ => (univLiftF_comp g f x₀ F).symm]
  exact hz (f.onV x₀) (chain2 (univLift X f x₀) c) (mem_pi2_chain2_univLift f hc)
