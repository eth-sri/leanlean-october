module

public import Mathlib

@[expose] public section

namespace FiniteChains.Comb

universe u v

variable {V E : Type*}

def germSrc (src tgt : E → V) (e : E × Bool) : V := if e.2 then src e.1 else tgt e.1

def germTgt (src tgt : E → V) (e : E × Bool) : V := if e.2 then tgt e.1 else src e.1

@[simp] theorem germSrc_true (src tgt : E → V) (e : E) : germSrc src tgt (e, true) = src e := rfl
@[simp] theorem germSrc_false (src tgt : E → V) (e : E) : germSrc src tgt (e, false) = tgt e := rfl
@[simp] theorem germTgt_true (src tgt : E → V) (e : E) : germTgt src tgt (e, true) = tgt e := rfl
@[simp] theorem germTgt_false (src tgt : E → V) (e : E) : germTgt src tgt (e, false) = src e := rfl

def IsPath (src tgt : E → V) : List (E × Bool) → V → V → Prop
  | [], a, b => a = b
  | e :: p, a, b => a = germSrc src tgt e ∧ IsPath src tgt p (germTgt src tgt e) b

@[simp] theorem isPath_nil (src tgt : E → V) (a b : V) :
    IsPath src tgt [] a b ↔ a = b := Iff.rfl

@[simp] theorem isPath_cons (src tgt : E → V) (e : E × Bool) (p : List (E × Bool)) (a b : V) :
    IsPath src tgt (e :: p) a b ↔
      a = germSrc src tgt e ∧ IsPath src tgt p (germTgt src tgt e) b := Iff.rfl

theorem IsPath.append {src tgt : E → V} {p q : List (E × Bool)} {a b c : V}
    (hp : IsPath src tgt p a b) (hq : IsPath src tgt q b c) : IsPath src tgt (p ++ q) a c := by
  induction p generalizing a with
  | nil => cases hp; exact hq
  | cons _ _ ih => exact ⟨hp.1, ih hp.2⟩

structure Complex2 : Type (u + 1) where
  V : Type u
  E : Type u
  F : Type u
  src : E → V
  tgt : E → V
  base : F → V
  att : F → List (E × Bool)
  att_isLoop : ∀ f, IsPath src tgt (att f) (base f) (base f)

variable (X : Complex2.{u})

def IsConnected : Prop := ∀ a b : X.V, ∃ p, IsPath X.src X.tgt p a b

noncomputable def pathChain (p : List (E × Bool)) : E →₀ ℤ :=
  (p.map (fun e => if e.2 then Finsupp.single e.1 (1 : ℤ) else -Finsupp.single e.1 (1 : ℤ))).sum

@[simp] theorem pathChain_nil : pathChain ([] : List (E × Bool)) = 0 := rfl

theorem pathChain_cons (e : E × Bool) (p : List (E × Bool)) :
    pathChain (e :: p) =
      (if e.2 then Finsupp.single e.1 (1 : ℤ) else -Finsupp.single e.1 (1 : ℤ)) +
        pathChain p := by
  simp [pathChain]

noncomputable def bdry1 : (X.E →₀ ℤ) →ₗ[ℤ] (X.V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (X.tgt e) (1 : ℤ)
    - Finsupp.single (X.src e) (1 : ℤ))

noncomputable def bdry2 : (X.F →₀ ℤ) →ₗ[ℤ] (X.E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f => pathChain (X.att f))

noncomputable def augC : (X.V →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))

variable {X}

@[simp] theorem bdry1_single (e : X.E) (n : ℤ) :
    bdry1 X (Finsupp.single e n) =
      n • (Finsupp.single (X.tgt e) (1 : ℤ) - Finsupp.single (X.src e) (1 : ℤ)) := by
  simp [bdry1]

@[simp] theorem bdry2_single (f : X.F) (n : ℤ) :
    bdry2 X (Finsupp.single f n) = n • pathChain (X.att f) := by
  simp [bdry2]

@[simp] theorem augC_single (a : X.V) (n : ℤ) : augC X (Finsupp.single a n) = n := by
  simp [augC]

theorem bdry1_pathChain_of_isPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) :
    bdry1 X (pathChain p) = Finsupp.single b (1 : ℤ) - Finsupp.single a (1 : ℤ) := by
  induction p generalizing a with
  | nil => cases hp; simp
  | cons e p ih =>
      rw [pathChain_cons, map_add, ih hp.2]
      rcases e with ⟨e, _ | _⟩ <;> simp [hp.1, germSrc, germTgt]

theorem bdry1_bdry2 (c : X.F →₀ ℤ) : bdry1 X (bdry2 X c) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | single f n =>
      rw [bdry2_single, map_smul, bdry1_pathChain_of_isPath (X.att_isLoop f)]; simp

structure IsAcyclic (X : Complex2.{u}) : Prop where
  h2 : Function.Injective (bdry2 X)
  h1 : ∀ c : X.E →₀ ℤ, bdry1 X c = 0 → ∃ u : X.F →₀ ℤ, bdry2 X u = c
  h0 : ∀ c : X.V →₀ ℤ, augC X c = 0 → ∃ u : X.E →₀ ℤ, bdry1 X u = c

structure Hom (X Y : Complex2.{u}) where
  onV : X.V → Y.V
  onE : X.E → Y.E
  onF : X.F → Y.F
  src_onE : ∀ e, Y.src (onE e) = onV (X.src e)
  tgt_onE : ∀ e, Y.tgt (onE e) = onV (X.tgt e)
  base_onF : ∀ f, Y.base (onF f) = onV (X.base f)
  att_onF : ∀ f, Y.att (onF f) = (X.att f).map (fun eb => (onE eb.1, eb.2))

variable {X Y : Complex2.{u}}

theorem germSrc_onE (p : Hom X Y) (eb : X.E × Bool) :
    germSrc Y.src Y.tgt (p.onE eb.1, eb.2) = p.onV (germSrc X.src X.tgt eb) := by
  rcases eb with ⟨_, _ | _⟩ <;> simp [germSrc, p.src_onE, p.tgt_onE]

def Germ (X : Complex2.{u}) (a : X.V) : Type u :=
  {eb : X.E × Bool // germSrc X.src X.tgt eb = a}

def germMap (p : Hom X Y) (a : X.V) : Germ X a → Germ Y (p.onV a) :=
  fun eb => ⟨(p.onE eb.1.1, eb.1.2), by rw [germSrc_onE p eb.1, eb.2]⟩

def cellMap (p : Hom X Y) : X.F → {gv : Y.F × X.V // Y.base gv.1 = p.onV gv.2} :=
  fun f => ⟨(p.onF f, X.base f), p.base_onF f⟩

structure IsCovering (p : Hom X Y) : Prop where
  surjV : Function.Surjective p.onV
  germ : ∀ a : X.V, Function.Bijective (germMap p a)
  cell : Function.Bijective (cellMap p)

structure DeckAction (X : Complex2.{u}) (Q : Type v) [Group Q] where
  smulV : Q → X.V → X.V
  smulE : Q → X.E → X.E
  smulF : Q → X.F → X.F
  one_smulV : ∀ a, smulV 1 a = a
  mul_smulV : ∀ q q' a, smulV (q * q') a = smulV q (smulV q' a)
  one_smulE : ∀ e, smulE 1 e = e
  mul_smulE : ∀ q q' e, smulE (q * q') e = smulE q (smulE q' e)
  one_smulF : ∀ f, smulF 1 f = f
  mul_smulF : ∀ q q' f, smulF (q * q') f = smulF q (smulF q' f)
  src_smul : ∀ q e, X.src (smulE q e) = smulV q (X.src e)
  tgt_smul : ∀ q e, X.tgt (smulE q e) = smulV q (X.tgt e)
  base_smul : ∀ q f, X.base (smulF q f) = smulV q (X.base f)
  att_smul : ∀ q f, X.att (smulF q f) = (X.att f).map (fun eb => (smulE q eb.1, eb.2))

structure IsRegular (p : Hom X Y) {Q : Type v} [Group Q] (A : DeckAction X Q) : Prop where
  compat : ∀ q a, p.onV (A.smulV q a) = p.onV a
  simply_transitive : ∀ a b : X.V, p.onV a = p.onV b → ∃! q : Q, A.smulV q a = b

end FiniteChains.Comb
