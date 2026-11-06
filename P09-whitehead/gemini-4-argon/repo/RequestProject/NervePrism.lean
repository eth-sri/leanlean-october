module

public import Mathlib

@[expose] public section

namespace FiniteChains.Nerve

universe u

open FreeAbelianGroup

variable {P Q : Type u}

abbrev Ch (P : Type u) : Type u := FreeAbelianGroup (List P)

theorem hom_ext {A : Type*} [AddCommGroup A] {F G : Ch P →+ A}
    (h : ∀ l : List P, F (of l) = G (of l)) : F = G := by
  ext x; exact h x

theorem ext_apply {A : Type*} [AddCommGroup A] {F G : Ch P →+ A}
    (h : ∀ l : List P, F (of l) = G (of l)) (x : Ch P) : F x = G x := by
  rw [hom_ext h]

def consMap (a : P) : Ch P →+ Ch P := lift fun l => of (a :: l)

@[simp] theorem consMap_of (a : P) (l : List P) : consMap a (of l) = of (a :: l) :=
  lift_apply_of _ _

def consList (pre : List P) : Ch P →+ Ch P := lift fun l => of (pre ++ l)

@[simp] theorem consList_of (pre l : List P) : consList pre (of l) = of (pre ++ l) :=
  lift_apply_of _ _

@[simp] theorem consList_nil (x : Ch P) : consList ([] : List P) x = x :=
  ext_apply (F := consList []) (G := .id _) (by simp) x

theorem consList_consMap (pre : List P) (a : P) (x : Ch P) :
    consList pre (consMap a x) = consList (pre ++ [a]) x :=
  ext_apply (F := (consList pre).comp (consMap a)) (G := consList (pre ++ [a])) (by simp) x

def bdryOn : List P → Ch P
  | [] => 0
  | a :: t => of t - consMap a (bdryOn t)

def bdry : Ch P →+ Ch P := lift bdryOn

@[simp] theorem bdry_of (l : List P) : bdry (of l) = bdryOn l := lift_apply_of _ _

@[simp] theorem bdryOn_nil : bdryOn ([] : List P) = 0 := rfl

theorem bdryOn_cons (a : P) (t : List P) : bdryOn (a :: t) = of t - consMap a (bdryOn t) := rfl

theorem bdry_consMap (a : P) (x : Ch P) : bdry (consMap a x) = x - consMap a (bdry x) :=
  ext_apply (F := bdry.comp (consMap a)) (G := .id _ - (consMap a).comp bdry)
    (by simp [bdryOn_cons]) x

theorem bdry_bdry (x : Ch P) : bdry (bdry x) = 0 := by
  refine ext_apply (F := bdry.comp bdry) (G := 0) (fun l => ?_) x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, bdry_of, AddMonoidHom.zero_apply]
  induction l with
  | nil => simp
  | cons a t ih => simp [bdryOn_cons, bdry_consMap, ih]

def cmap (f : P → Q) : Ch P →+ Ch Q := lift fun l => of (l.map f)

@[simp] theorem cmap_of (f : P → Q) (l : List P) : cmap f (of l) = of (l.map f) :=
  lift_apply_of _ _

@[simp] theorem cmap_id (x : Ch P) : cmap id x = x :=
  ext_apply (F := cmap id) (G := .id _) (by simp) x

theorem cmap_consMap (f : P → Q) (a : P) (x : Ch P) :
    cmap f (consMap a x) = consMap (f a) (cmap f x) :=
  ext_apply (F := (cmap f).comp (consMap a)) (G := (consMap (f a)).comp (cmap f)) (by simp) x

theorem cmap_bdry (f : P → Q) (x : Ch P) : cmap f (bdry x) = bdry (cmap f x) := by
  refine ext_apply (F := (cmap f).comp bdry) (G := bdry.comp (cmap f)) (fun l => ?_) x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, bdry_of, cmap_of]
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, bdryOn_cons, map_sub, cmap_consMap, ih, cmap_of]

def prismOn (f g : P → P) : List P → Ch P
  | [] => 0
  | a :: t => of (f a :: (a :: t).map g) - consMap (f a) (prismOn f g t)

def prism (f g : P → P) : Ch P →+ Ch P := lift (prismOn f g)

@[simp] theorem prism_of (f g : P → P) (l : List P) : prism f g (of l) = prismOn f g l :=
  lift_apply_of _ _

theorem prismOn_cons (f g : P → P) (a : P) (t : List P) :
    prismOn f g (a :: t) = of (f a :: (a :: t).map g) - consMap (f a) (prismOn f g t) := rfl

theorem prism_consMap (f g : P → P) (a : P) (x : Ch P) :
    prism f g (consMap a x) =
      consMap (f a) (consMap (g a) (cmap g x)) - consMap (f a) (prism f g x) :=
  ext_apply (F := (prism f g).comp (consMap a))
    (G := (consMap (f a)).comp ((consMap (g a)).comp (cmap g)) - (consMap (f a)).comp (prism f g))
    (by simp [prismOn_cons]) x

theorem bdry_prism_add_prism_bdry (f g : P → P) (x : Ch P) :
    bdry (prism f g x) + prism f g (bdry x) = cmap g x - cmap f x := by
  refine ext_apply (F := bdry.comp (prism f g) + (prism f g).comp bdry) (G := cmap g - cmap f)
    (fun l => ?_) x
  simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  induction l with
  | nil => simp [prismOn]
  | cons a t ih =>
      have h1 : bdry (prism f g (consMap a (of t))) =
          (consMap (g a) (cmap g (of t)) - consMap (f a) (cmap g (of t)) +
              consMap (f a) (consMap (g a) (bdry (cmap g (of t))))) -
            (prism f g (of t) - consMap (f a) (bdry (prism f g (of t)))) := by
        rw [prism_consMap, map_sub, bdry_consMap (f a) (consMap (g a) _),
          bdry_consMap (f a) (prism f g _), bdry_consMap (g a) (cmap g _), map_sub]
        abel
      have h2 : prism f g (bdry (consMap a (of t))) =
          prism f g (of t) - (consMap (f a) (consMap (g a) (bdry (cmap g (of t)))) -
            consMap (f a) (prism f g (bdry (of t)))) := by
        rw [bdry_consMap, map_sub, prism_consMap, cmap_bdry]
      have h3 := (map_add (consMap (f a)) (bdry (prism f g (of t))) (prism f g (bdry (of t)))).symm.trans
        ((congrArg (consMap (f a)) ih).trans (map_sub (consMap (f a)) _ _))
      change bdry (prism f g (consMap a (of t))) + prism f g (bdry (consMap a (of t))) =
        cmap g (consMap a (of t)) - cmap f (consMap a (of t))
      rw [h1, h2, cmap_consMap, cmap_consMap]
      linear_combination (norm := abel) h3

variable [Preorder P]

def Inc (P : Type u) [Preorder P] : AddSubgroup (Ch P) :=
  AddSubgroup.closure {x : Ch P | ∃ l : List P, List.IsChain (· ≤ ·) l ∧ x = of l}

theorem of_mem_inc {l : List P} (hl : List.IsChain (· ≤ ·) l) : of l ∈ Inc P :=
  AddSubgroup.subset_closure ⟨l, hl, rfl⟩

theorem hom_mem_inc (φ : Ch P →+ Ch P)
    (h : ∀ l : List P, List.IsChain (· ≤ ·) l → φ (of l) ∈ Inc P)
    {x : Ch P} (hx : x ∈ Inc P) : φ x ∈ Inc P := by
  refine AddSubgroup.closure_induction (p := fun y _ => φ y ∈ Inc P) ?_ (by simp)
    (fun _ _ _ _ hy hz => by simpa using AddSubgroup.add_mem _ hy hz)
    (fun _ _ hy => by simpa using AddSubgroup.neg_mem _ hy) hx
  rintro _ ⟨l, hl, rfl⟩; exact h l hl

theorem isChain_append_of_isChain_append_cons {pre t : List P} {a : P}
    (h : List.IsChain (· ≤ ·) (pre ++ a :: t)) : List.IsChain (· ≤ ·) (pre ++ t) := by
  rw [List.isChain_append] at h ⊢
  obtain ⟨hpre, hat, hlast⟩ := h
  rw [List.isChain_cons] at hat
  exact ⟨hpre, hat.2, fun x hx y hy => le_trans (hlast x hx a (by simp)) (hat.1 y hy)⟩

theorem consList_bdryOn_mem_inc :
    ∀ (l pre : List P), List.IsChain (· ≤ ·) (pre ++ l) → consList pre (bdryOn l) ∈ Inc P
  | [], _, _ => by simp
  | a :: t, pre, hpre => by
      rw [bdryOn_cons, map_sub, consList_of, consList_consMap]
      exact AddSubgroup.sub_mem _ (of_mem_inc (isChain_append_of_isChain_append_cons hpre))
        (consList_bdryOn_mem_inc t (pre ++ [a]) (by simpa using hpre))

theorem bdry_mem_inc {x : Ch P} (hx : x ∈ Inc P) : bdry x ∈ Inc P :=
  hom_mem_inc bdry (fun l hl => by simpa using consList_bdryOn_mem_inc l [] (by simpa using hl)) hx

theorem cmap_mem_inc {f : P → P} (hf : Monotone f) {x : Ch P} (hx : x ∈ Inc P) :
    cmap f x ∈ Inc P :=
  hom_mem_inc (cmap f) (fun l hl => by
    rw [cmap_of]; exact of_mem_inc (List.isChain_map_of_isChain f (fun _ _ h => hf h) hl)) hx

theorem consList_prismOn_mem_inc {f g : P → P} (hg : Monotone g) (hfg : ∀ p : P, f p ≤ g p) :
    ∀ (l pre : List P), List.IsChain (· ≤ ·) l → List.IsChain (· ≤ ·) (pre ++ l.map f) →
      consList pre (prismOn f g l) ∈ Inc P
  | [], _, _, _ => by simp [prismOn]
  | a :: t, pre, hl, hpre => by
      rw [prismOn_cons, map_sub, consList_of, consList_consMap]
      refine AddSubgroup.sub_mem _ (of_mem_inc ?_)
        (consList_prismOn_mem_inc hg hfg t (pre ++ [f a]) (List.isChain_cons.1 hl).2 (by simpa using hpre))
      rw [List.isChain_append] at hpre ⊢
      obtain ⟨hp, _, hlast⟩ := hpre
      refine ⟨hp, List.isChain_cons.2 ⟨?_, List.isChain_map_of_isChain g (fun _ _ h => hg h) hl⟩, ?_⟩
      · intro y hy; rw [show y = g a by simpa [eq_comm] using hy]; exact hfg a
      · intro x hx y hy; rw [show y = f a by simpa [eq_comm] using hy]; exact hlast x hx (f a) (by simp)

theorem prism_mem_inc {f g : P → P} (hf : Monotone f) (hg : Monotone g) (hfg : ∀ p : P, f p ≤ g p)
    {x : Ch P} (hx : x ∈ Inc P) : prism f g x ∈ Inc P :=
  hom_mem_inc (prism f g) (fun l hl => by
    simpa using consList_prismOn_mem_inc hg hfg l [] hl
      (by simpa using List.isChain_map_of_isChain f (fun _ _ h => hf h) hl)) hx

variable (ρ : P → P) (d : P)

noncomputable def contraction : Ch P →+ Ch P :=
  prism ρ id - prism ρ (fun _ => d) + (consMap d).comp (cmap (fun _ => d))

theorem cone_const_mem_inc (x : Ch P) : consMap d (cmap (fun _ => d) x) ∈ Inc P := by
  have hchain (l : List P) : List.IsChain (· ≤ ·) (l.map fun _ => d) := by
    induction l with
    | nil => simp
    | cons _ t ih =>
        exact List.isChain_cons.2 ⟨fun y hy => by cases t <;> simp [eq_comm] at hy; rw [hy], ih⟩
  refine FreeAbelianGroup.induction_on x (by simp) (fun l => ?_)
    (fun _ hl => by simpa using AddSubgroup.neg_mem _ hl)
    (fun _ _ hu hv => by simpa using AddSubgroup.add_mem _ hu hv)
  rw [cmap_of, consMap_of]
  exact of_mem_inc (hchain (d :: l))

theorem exists_bdry_eq_of_cycle (hρ : Monotone ρ) (hρle : ∀ p : P, ρ p ≤ p)
    (hρd : ∀ p : P, ρ p ≤ d) {x : Ch P} (hx : x ∈ Inc P) (hcyc : bdry x = 0) :
    ∃ y ∈ Inc P, bdry y = x := by
  refine ⟨contraction ρ d x,
    AddSubgroup.add_mem _ (AddSubgroup.sub_mem _
      (prism_mem_inc hρ monotone_id hρle hx)
      (prism_mem_inc hρ monotone_const hρd hx))
      (cone_const_mem_inc d x), ?_⟩
  have t1 : bdry (prism ρ id x) + prism ρ id (bdry x) = x - cmap ρ x := by
    simpa using bdry_prism_add_prism_bdry ρ id x
  have t2 := bdry_prism_add_prism_bdry ρ (fun _ => d) x
  have t3 : bdry (consMap d (cmap (fun _ => d) x)) + consMap d (cmap (fun _ => d) (bdry x)) =
      cmap (fun _ => d) x := by rw [bdry_consMap, cmap_bdry]; abel
  have hhtpy : bdry (contraction ρ d x) + contraction ρ d (bdry x) = x := by
    simp only [contraction, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp,
      Function.comp_apply, map_add, map_sub]
    linear_combination (norm := abel) t1 - t2 + t3
  rwa [hcyc, map_zero, add_zero] at hhtpy
