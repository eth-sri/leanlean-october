module

public import RequestProject.CombPi1

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u v
variable {X Y : Complex2.{u}} {G : Type v} [Group G]

namespace EdgeLabels
def germ (w : X.E → G) (e : X.E × Bool) : G := if e.2 then w e.1 else (w e.1)⁻¹
def read (w : X.E → G) (p : List (X.E × Bool)) : G := (p.map (germ w)).prod

@[simp] theorem read_nil (w : X.E → G) : read w [] = 1 := rfl
@[simp] theorem read_cons (w : X.E → G) (e : X.E × Bool) (p : List (X.E × Bool)) :
    read w (e :: p) = germ w e * read w p := rfl
theorem read_append (w : X.E → G) (p q : List (X.E × Bool)) :
    read w (p ++ q) = read w p * read w q := by simp [read, List.prod_append]

theorem read_htpy (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    {a b : X.V} {p q : List (X.E × Bool)} (h : Htpy X a b p q) : read w p = read w q := by
  have hcanc {p q : List (X.E × Bool)} (hc : Cancels X p q) : read w p = read w q := by
    rcases hc with ⟨a, b, ⟨e, _ | _⟩, rfl, rfl⟩ | ⟨a, b, f, rfl, rfl⟩
    · rw [read_append, read_append, read_cons, read_cons]; dsimp [germ, revGerm]; group
    · rw [read_append, read_append, read_cons, read_cons]; dsimp [germ, revGerm]; group
    · rw [read_append, read_append, read_append, hw, mul_one]
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      rcases hs with hs | hs
      exacts [ih.trans (hcanc hs.2.2), ih.trans (hcanc hs.2.2).symm]

def monodromy (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1) (a : X.V) : Pi1 X a →* G where
  toFun := Quotient.lift (fun p => read w p.val) (fun _ _ h => read_htpy w hw h)
  map_one' := rfl
  map_mul' := by rintro ⟨p⟩ ⟨q⟩; exact read_append w p.val q.val

theorem read_mapPath (w : Y.E → G) (f : Hom X Y) (p : List (X.E × Bool)) :
    read w (mapPath f p) = read (w ∘ f.onE) p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [mapPath, List.map_cons, read_cons] at *; rw [ih]; rfl

theorem read_potential (w : X.E → G) (v : X.V → G)
    (hw : ∀ e, w e = (v (X.src e))⁻¹ * v (X.tgt e))
    {p : List (X.E × Bool)} {a b : X.V} (hp : IsPath X.src X.tgt p a b) :
    read w p = (v a)⁻¹ * v b := by
  induction p generalizing a with
  | nil => cases hp; simp
  | cons e p ih =>
      rcases hp with ⟨rfl, hp⟩
      rw [read_cons, show germ w e = (v (germSrc X.src X.tgt e))⁻¹ * v (germTgt X.src X.tgt e) by
        rcases e with ⟨_, _ | _⟩ <;> simp [germ, germSrc, germTgt, hw, mul_inv_rev], ih hp]
      group
end EdgeLabels

structure RootPaths (X : Complex2.{u}) (a : X.V) where
  path : X.V → List (X.E × Bool)
  valid : ∀ b, IsPath X.src X.tgt (path b) a b
  at_root : path a = []

namespace RootPaths
variable {a : X.V} (r : RootPaths X a)

def choose (hc : IsConnected X) (a : X.V) : RootPaths X a where
  path b := if b = a then [] else Classical.choose (hc a b)
  valid b := by split <;> [ { rename_i h; cases h; rfl }; exact Classical.choose_spec (hc a b) ]
  at_root := by simp

def conjugate (p : List (X.E × Bool)) (b c : X.V) := r.path b ++ p ++ revPath (r.path c)

theorem conjugate_valid {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) :
    IsPath X.src X.tgt (r.conjugate p b c) a a :=
  isPath_append_iff.mpr ⟨c, isPath_append_iff.mpr ⟨b, r.valid b, hp⟩, isPath_revPath (r.valid c)⟩

def classOf {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) : Pi1 X a :=
  Pi1.mk ⟨r.conjugate p b c, r.conjugate_valid hp⟩

@[simp] theorem classOf_nil (b : X.V) : r.classOf (p := []) (b := b) (c := b) rfl = 1 :=
  Quotient.sound (by
    change Htpy X a a _ _
    simpa [loopSetoid, Pi1, Loop, conjugate] using htpy_append_revPath (r.valid b))

def edge (e : X.E) : Pi1 X a := r.classOf (isPath_single (e, true))

theorem read_classOf {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) :
    EdgeLabels.read r.edge p = r.classOf hp := by
  induction p generalizing b with
  | nil => cases hp; exact (r.classOf_nil _).symm
  | cons e p ih =>
      rcases hp with ⟨rfl, hp⟩
      rw [EdgeLabels.read_cons, show EdgeLabels.germ r.edge e = r.classOf (isPath_single e) by
        rcases e with ⟨e, _ | _⟩
        · exact Quotient.sound (by
            change Htpy X a a (revPath (r.conjugate [(e, true)] _ _)) (r.conjugate [(e, false)] _ _)
            simp only [conjugate, revPath_append, revPath_revPath, List.append_assoc]
            exact Htpy.refl _)
        · rfl, ih hp]
      exact Quotient.sound (by
        change Htpy X a a _ _
        simpa [loopSetoid, Pi1, Loop, conjugate, List.append_assoc] using
          (htpy_revPath_append (r.valid _)).congr_append
            (isPath_append_iff.mpr ⟨_, r.valid _, isPath_single e⟩)
            (isPath_append_iff.mpr ⟨_, hp, isPath_revPath (r.valid _)⟩))

theorem edge_rel (f : X.F) : EdgeLabels.read r.edge (X.att f) = 1 := by
  rw [r.read_classOf (X.att_isLoop f)]
  have h : Htpy X (X.base f) (X.base f) (X.att f) [] :=
    Htpy.of_step ⟨X.att_isLoop f, rfl, .inr ⟨[], [], f, by simp, rfl⟩⟩
  exact (Quotient.sound (h.congr_append (r.valid _) (isPath_revPath (r.valid _)))).trans (r.classOf_nil _)

theorem read_loop (p : Loop X a) : EdgeLabels.read r.edge p.val = Pi1.mk p := by
  rw [r.read_classOf p.property]
  exact Quotient.sound (by
    simp only [conjugate, r.at_root, List.nil_append, revPath_nil, List.append_nil]
    exact Htpy.refl _)

end RootPaths
end FiniteChains.Comb
