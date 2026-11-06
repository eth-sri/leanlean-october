import RequestProject.CombPi1
import RequestProject.Tac


/-! Group-valued edge labels and path choices. These read actual edge-path
homotopy classes and will detect the two factors in the descent pushout.
Unverified source. -/

noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Comb
universe u v
variable {X Y : Complex2.{u}} {G : Type v} [Group G]

namespace EdgeLabels
def germ (w : X.E → G) (e : X.E × Bool) := if e.2 then w e.1 else (w e.1)⁻¹
def read (w : X.E → G) (p : List (X.E × Bool)) := (p.map (germ w)).prod

@[simp] theorem read_nil (w : X.E → G) : read w [] = 1 := rfl
@[simp] theorem read_cons (w : X.E → G) e p :
    read w (e :: p) = germ w e * read w p := rfl
theorem read_append (w : X.E → G) p q :
    read w (p ++ q) = read w p * read w q := by simp [read, List.prod_append]
theorem germ_rev (w : X.E → G) e : germ w (revGerm e) = (germ w e)⁻¹ := by
  cases' e with e b
  cases b <;> simp [germ, revGerm]

theorem read_cancels (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    {p q} (h : Cancels X p q) : read w p = read w q := by
  rcases h with ⟨a, b, e, rfl, rfl⟩ | ⟨a, b, f, rfl, rfl⟩
  · simp [read_append, read_cons, germ_rev]
  · simp [read_append, hw, mul_one]

theorem read_htpy (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    {a b} {p q} (h : Htpy X a b p q) : read w p = read w q := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      rcases hs with hs | hs
      · exact ih.trans (read_cancels w hw hs.2.2)
      · exact ih.trans (read_cancels w hw hs.2.2).symm

def monodromy (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1) a : Pi1 X a →* G where
  toFun := Quotient.lift (read w ·.val) (fun _ _ h => read_htpy w hw h)
  map_one' := rfl
  map_mul' := by rintro ⟨p⟩ ⟨q⟩; exact read_append w p.val q.val

theorem read_mapPath (w : Y.E → G) f (p : List (X.E × Bool)) :
    read w (mapPath f p) = read (w ∘ f.onE) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [mapPath, List.map_cons, read_cons] at *; tauto

theorem read_potential w (v : X.V → G)
    (hw : ∀ e, w e = (v (X.src e))⁻¹ * v (X.tgt e))
    {p} {a b} (hp : IsPathX X p a b) :
    read w p = (v a)⁻¹ * v b := by
  have hg (e : X.E × Bool) : germ w e =
      (v (gSrcX X e))⁻¹ * v (gTgtX X e) := by
    cases' e with e b
    cases b <;> simp [germ, germSrc, germTgt, hw, mul_inv_rev]
  induction p generalizing a with
  | nil => simp_all
  | cons e p ih =>
      cases' hp with ha hp
      subst ha
      rw [read_cons, hg, ih hp]
      group
end EdgeLabels

/-- Paths from one root, with the empty path chosen at the root. -/
structure RootPaths (X : Complex2.{u}) (a : X.V) where
  path : X.V → List (X.E × Bool)
  valid : ∀ b, IsPathX X (path b) a b
  at_root : path a = []

namespace RootPaths
variable {a : X.V} (r : RootPaths X a)

def choose (hc : IsConnected X) a : RootPaths X a where
  path b := if b = a then [] else Classical.choose (hc a b)
  valid b := by
    split
    · simp_all
    grind
  at_root := by simp

def conjugate (p : List (X.E × Bool)) (b c : X.V) := r.path b ++ p ++ revPath (r.path c)

theorem conjugate_valid (hp : IsPathX X p b c) :
    IsPathX X (r.conjugate p b c) a a :=
  isPath_append_iff.mpr ⟨c, isPath_append_iff.mpr ⟨b, r.valid b, hp⟩, isPath_revPath (r.valid c)⟩

def classOf {p : List (X.E × Bool)} {b c : X.V} (hp : IsPathX X p b c) :=
  Pi1.mk ⟨r.conjugate p b c, r.conjugate_valid hp⟩

theorem classOf_htpy {b c}
    (hp : IsPathX X p b c) (hq : IsPathX X q b c)
    (h : Htpy X b c p q) : r.classOf hp = r.classOf hq :=
  Quotient.sound (h.congr_append (r.valid b) (isPath_revPath (r.valid c)))

@[simp] theorem classOf_nil b : r.classOf (p := []) (b := b) (c := b) rfl = 1 := by
  apply Quotient.sound
  change Htpy X a a _ _
  simpa [loopSetoid, Pi1, Loop, conjugate] using htpy_append_revPath (r.valid b)

theorem classOf_mul {b c d}
    (hp : IsPathX X p b c) (hq : IsPathX X q c d) :
    r.classOf hp * r.classOf hq = r.classOf (isPath_append_iff.mpr ⟨c, hp, hq⟩) := by
  apply Quotient.sound
  change Htpy X a a _ _
  have h := (htpy_revPath_append (r.valid c)).congr_append
    (isPath_append_iff.mpr ⟨b, r.valid b, hp⟩)
    (isPath_append_iff.mpr ⟨d, hq, isPath_revPath (r.valid d)⟩)
  grind [loopSetoid, Pi1, Loop, conjugate, List.append_assoc]

theorem classOf_rev (hp : IsPathX X p b c) :
    r.classOf (isPath_revPath hp) = (r.classOf hp)⁻¹ := by
  apply Quotient.sound
  simp [conjugate, revPath_append, revPath_revPath, List.append_assoc]

def edge (e : X.E) := r.classOf (isPath_single (e, true))

theorem germ_classOf e : EdgeLabels.germ r.edge e = r.classOf (isPath_single e) := by
  cases' e with e b
  cases b with
  | true => rfl
  | false =>
      exact (r.classOf_rev _).symm

theorem read_classOf (hp : IsPathX X p b c) :
    EdgeLabels.read r.edge p = r.classOf hp := by
  induction p generalizing b with
  | nil => cases hp; simp
  | cons e p ih =>
      cases' hp with hb hp
      subst hb
      rw [EdgeLabels.read_cons, r.germ_classOf, ih hp]
      exact r.classOf_mul _ hp

theorem edge_rel f : EdgeLabels.read r.edge (X.att f) = 1 := by
  rw [r.read_classOf (X.att_isLoop f)]
  have h : Htpy X (X.base f) (X.base f) (X.att f) [] :=
    Htpy.of_step ⟨X.att_isLoop f, rfl, Or.inr (by simp)⟩
  exact (r.classOf_htpy (q := []) _ rfl h).trans (r.classOf_nil _)

theorem read_loop p : EdgeLabels.read r.edge p.val = Pi1.mk p := by
  rw [r.read_classOf p.property]
  apply Quotient.sound
  simp [conjugate, r.at_root, List.nil_append, revPath_nil, List.append_nil]
