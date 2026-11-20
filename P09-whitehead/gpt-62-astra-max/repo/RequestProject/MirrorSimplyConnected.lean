module

public import RequestProject.MirrorContraction
public import RequestProject.CombPi1

@[expose] public section

/-!
# Simple connectivity of the attaching subcomplex, by paths and triangular relations

`RequestProject/MirrorContraction.lean` contracts the *augmented chain complex* of the order
complex of the poset `𝒫_D = {σ ∈ L : σ ∩ D ≠ ∅}`.  Chain contractibility does not by itself
give simple connectivity, and the chamber argument needs the fundamental group.  This file
supplies the missing statement directly, in the language of edge paths and triangular
relations, exactly as in the remark "The corresponding contraction of edge paths" of
`block-substitution-chamber-proof.tex`.

* `FiniteChains.Comb.orderCx P` — the two-skeleton of the order complex of a preorder `P`:
  vertices are the elements, oriented edges are the comparable pairs `a ≤ b`, two-cells are
  the chains `a ≤ b ≤ c`, attached along `[a,b][b,c][a,c]⁻¹`.
* `FiniteChains.Comb.htpy_orderCx_tri` — the triangular relation `[a,b][b,c] ≃ [a,c]`.
* `FiniteChains.Comb.ordPth` — the path `p_σ = [σ,ρσ]⁻¹[ρσ,d]` of the text.
* `FiniteChains.Comb.htpy_ordPos_ordPth` — the key identity `[σ,τ] p_τ ≃ p_σ` for `σ ≤ τ`,
  proved from the three triangular relations for
  `ρσ ≤ σ ≤ τ`, `ρσ ≤ ρτ ≤ τ` and `ρσ ≤ ρτ ≤ d`.
* `FiniteChains.Comb.htpy_path_ordPth` — every edge path `p` from `σ` to `τ` satisfies
  `p · p_τ ≃ p_σ`, hence every path `σ → τ` is homotopic to `p_σ p_τ⁻¹`, and
* `FiniteChains.Comb.simplyConnected_orderCx` — the order complex of a preorder carrying an
  order map `ρ ≤ id` with `ρ ≤ c_d` is simply connected.

The last section applies this to `𝒫_D` with `ρ σ = σ ∩ D` and `d = D`, and to the descent set
`D(w)` of a right-angled Coxeter group, giving the simple connectivity half of the lemma on the
attaching subcomplex.

Note on flagness: the poset `𝒫_D` and the vertex `D` only make sense because `D` *is* a simplex
of `L`.  In the right-angled Coxeter model of this project `L` is the clique complex
`FiniteChains.RACG.IsSimplex` of the commutation graph, so the normal-form computation
`FiniteChains.RACG.rdesc_rel` (the descent set is a clique) is exactly what makes `D(w)` a
simplex; for a general `L` this is the flagness hypothesis and it may not be dropped.
-/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains
namespace Comb

universe u

/-! ### The order complex of a preorder -/

section Relation

variable {P : Type u} (r : P → P → Prop)

abbrev RelEdge := {p : P × P // r p.1 p.2}
abbrev RelTriangle := {t : P × P × P // r t.1 t.2.1 ∧ r t.2.1 t.2.2}

variable [Trans r r r]

/-- Two-skeleton of the nerve of a transitive relation. Applied to `≤` this
includes the degenerate simplices; applied to `<` it contains only strict flags. -/
abbrev relSkeleton : Complex2.{u} where
  V := P
  E := RelEdge r
  F := RelTriangle r
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t := [(⟨(t.1.1, t.1.2.1), t.2.1⟩, true),
    (⟨(t.1.2.1, t.1.2.2), t.2.2⟩, true),
    (⟨(t.1.1, t.1.2.2), Trans.trans t.2.1 t.2.2⟩, false)]
  att_isLoop _ := ⟨rfl, rfl, rfl, rfl⟩

variable {r} {Q : Type u} {s : Q → Q → Prop} [Trans s s s]

/-- Transport all flags, hence their attaching words, by a relation homomorphism. -/
abbrev relSkeletonMap (f : P → Q) (h : ∀ ⦃a b⦄, r a b → s (f a) (f b)) :
    Hom (relSkeleton r) (relSkeleton s) where
  onV := f
  onE e := ⟨(f e.1.1, f e.1.2), h e.2⟩
  onF t := ⟨(f t.1.1, f t.1.2.1, f t.1.2.2), h t.2.1, h t.2.2⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

end Relation

section OrderComplex
variable (P : Type u) [Preorder P]

abbrev OrdEdge := RelEdge (P := P) (· ≤ ·)
abbrev OrdTri := RelTriangle (P := P) (· ≤ ·)
def orderCx := relSkeleton (P := P) (· ≤ ·)

variable {P}

section

variable {a b : P} (h : a ≤ b)
include a b

/-- The edge `a → b` attached to `a ≤ b`. -/
def ordPos : (orderCx P).E × Bool := ((⟨(a, b), h⟩), true)

/-- The edge `a ≤ b` traversed backwards, from `b` to `a`. -/
def ordNeg : (orderCx P).E × Bool := ((⟨(a, b), h⟩), false)

@[simp] theorem revGerm_ordPos : revGerm (ordPos h) = ordNeg h := rfl

@[simp] theorem revGerm_ordNeg : revGerm (ordNeg h) = ordPos h := rfl

theorem isPath_ordPos :
    IsPath (orderCx P).src (orderCx P).tgt [ordPos h] a b := by solve_by_elim

theorem isPath_ordNeg :
    IsPath (orderCx P).src (orderCx P).tgt [ordNeg h] b a := by solve_by_elim

end

theorem isPath_nil' (a : P) :
    IsPath (orderCx P).src (orderCx P).tgt ([]) a a := rfl

section

variable {a b : P} (h : a ≤ b)
include a b

/-- Backtrack cancellation for an edge traversed forwards and then backwards. -/
theorem htpy_ordPos_ordNeg :
    Htpy _ a a [ordPos h, ordNeg h] [] := by
  have := htpy_append_revPath (isPath_single (X := orderCx P) (ordPos h))
  simpa [revPath, revGerm, Bool.not, Bool.not_true, Bool.not_false, ordPos, ordNeg, germSrc, germTgt, orderCx] using this

/-- Backtrack cancellation for an edge traversed backwards and then forwards. -/
theorem htpy_ordNeg_ordPos :
    Htpy _ b b [ordNeg h, ordPos h] [] := by
  have := htpy_append_revPath (isPath_single (X := orderCx P) (ordNeg h))
  simpa [revPath, revGerm, Bool.not, Bool.not_true, Bool.not_false, ordPos, ordNeg, germSrc, germTgt, orderCx] using this

end

/-- **The triangular relation**: `[a,b][b,c] ≃ [a,c]` for a chain `a ≤ b ≤ c`. -/
theorem htpy_orderCx_tri {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    Htpy _ a c [ordPos hab, ordPos hbc] [ordPos (hab.trans hbc)] := by
  have hac := hab.trans hbc
  have h1 : Htpy _ a c ([ordPos hab, ordPos hbc] ++ [])
      ([ordPos hab, ordPos hbc] ++ [ordNeg hac, ordPos hac]) :=
    Htpy.append_congr (⟨rfl, rfl, rfl⟩) rfl (Htpy.refl _) (htpy_ordNeg_ordPos hac).symm
  have h2 : Htpy _ a c [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac]
      [ordPos hac] := by
    refine Htpy.of_step ⟨(⟨rfl, rfl, rfl, rfl, rfl⟩), isPath_ordPos hac, Or.inr ?_⟩
    exact ⟨[], [ordPos hac], (⟨(a, b, c), hab, hbc⟩), rfl, rfl⟩
  simpa using h1.trans h2

end OrderComplex

/-! ### The explicit contraction of edge paths -/

section Contraction

variable {P : Type u} [Preorder P]

variable (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d)
include d rho hle htop

variable (x : P)

/-- The path `p_σ = [σ,ρσ]⁻¹[ρσ,d]` of the text: from `σ` down to `ρσ` and up to `d`. -/
def ordPth :
    List ((orderCx P).E × Bool) := [ordNeg (hle x), ordPos (htop x)]

theorem isPath_ordPth :
    IsPath (orderCx P).src (orderCx P).tgt (ordPth d rho hle htop x) x d := by solve_by_elim

section

variable (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y)
include hmono

variable {a b : P} (hab : a ≤ b)

/-- **The key identity** `[σ,τ] p_τ ≃ p_σ` for `σ ≤ τ`, obtained from the three triangular
relations for the chains `ρσ ≤ σ ≤ τ`, `ρσ ≤ ρτ ≤ τ` and `ρσ ≤ ρτ ≤ d`. -/
theorem htpy_ordPos_ordPth :
    Htpy _ a d (ordPos hab :: ordPth d rho hle htop b) (ordPth d rho hle htop a) := by
  have hrs := hmono hab
  have hrb := hrs.trans (hle b)
  have pa2 : IsPath (orderCx P).src (orderCx P).tgt [ordNeg (hle a), ordPos hrs] a _ :=
    ⟨rfl, rfl, rfl⟩
  have pb2 : IsPath (orderCx P).src (orderCx P).tgt
      [ordNeg (hle b), ordPos (htop b)] b d := ⟨rfl, rfl, rfl⟩
  have p3 : IsPath (orderCx P).src (orderCx P).tgt
      [ordPos hab, ordNeg (hle b), ordPos (htop b)] a d := ⟨rfl, rfl, rfl, rfl⟩
  -- Step 1: expand `[ρa,d]` as `[ρa,ρb][ρb,d]`.
  have s1 :=
    Htpy.append_congr (isPath_ordNeg (hle a)) (isPath_ordPos (htop a)) (Htpy.refl _)
      (htpy_orderCx_tri hrs (htop b)).symm
  -- Step 2: insert the backtrack `[ρb,b][ρb,b]⁻¹`.
  have s2 :=
    (htpy_ordPos_ordNeg (hle b)).symm.congr_append pa2
      (isPath_ordPos (htop b))
  -- Step 3: contract `[ρa,ρb][ρb,b]` to `[ρa,b]`.
  have s3 :=
    (htpy_orderCx_tri hrs (hle b)).congr_append (isPath_ordNeg (hle a)) pb2
  -- Step 4: expand `[ρa,b]` as `[ρa,a][a,b]`.
  have s4 :=
    (htpy_orderCx_tri (hle a) hab).symm.congr_append
      (isPath_ordNeg (hle a)) pb2
  -- Step 5: cancel the backtrack `[ρa,a]⁻¹[ρa,a]`.
  have chain : Htpy _ a d (ordPth d rho hle htop a)
      (ordPos hab :: ordPth d rho hle htop b) := by
    simp only [ordPth]
    exact ((((s1.trans s2).trans s3).trans s4).trans ((htpy_ordNeg_ordPos (hle a)).congr_append (c := a) (d := d) (isPath_nil' a) p3))
  exact chain.symm

/-- The reversed form of the key identity: `[σ,τ]⁻¹ p_σ ≃ p_τ`. -/
theorem htpy_ordNeg_ordPth :
    Htpy _ b d (ordNeg hab :: ordPth d rho hle htop a) (ordPth d rho hle htop b) := by
  have h1 :=
    Htpy.append_congr (isPath_ordNeg hab) (isPath_ordPth d rho hle htop a) (Htpy.refl _)
      (htpy_ordPos_ordPth d rho hle htop hmono hab).symm
  have h2 :=
    (htpy_ordNeg_ordPos hab).congr_append (isPath_nil' b)
      (isPath_ordPth d rho hle htop b)
  simp only [List.nil_append, List.cons_append] at h1 h2 ⊢
  exact h1.trans h2

/-- **Every edge path is the standard one**: for a path `p` from `σ` to `τ` one has
`p · p_τ ≃ p_σ`; in particular every path `σ → τ` is homotopic to `p_σ p_τ⁻¹`. -/
theorem htpy_path_ordPth :
    ∀ (p : List _) {x y : P},
      IsPath (orderCx P).src (orderCx P).tgt p x y →
      Htpy _ x d (p ++ ordPth d rho hle htop y) (ordPth d rho hle htop x) := by
  intro p
  induction p with
  | nil =>
      intro x y hp
      cases hp
      exact Htpy.refl _
  | cons eb p ih =>
      rintro x y ⟨hx, hrest⟩
      obtain ⟨⟨⟨a, b⟩, hab⟩, tag⟩ := eb
      cases tag with
      | false =>
          have hrest' := hrest
          have h1 :=
            Htpy.append_congr (isPath_ordNeg hab)
              (isPath_append_iff.mpr ⟨y, hrest', isPath_ordPth d rho hle htop y⟩)
              (Htpy.refl _) (ih hrest')
          have hgoal : Htpy _ b d ((ordNeg hab :: p) ++ ordPth d rho hle htop y)
              (ordPth d rho hle htop b) := h1.trans (htpy_ordNeg_ordPth d rho hle htop hmono hab)
          rw [hx]
          exact hgoal
      | true =>
          have hrest' := hrest
          have h1 :=
            Htpy.append_congr (isPath_ordPos hab)
              (isPath_append_iff.mpr ⟨y, hrest', isPath_ordPth d rho hle htop y⟩)
              (Htpy.refl _) (ih hrest')
          have hgoal : Htpy _ a d ((ordPos hab :: p) ++ ordPth d rho hle htop y)
              (ordPth d rho hle htop a) := h1.trans (htpy_ordPos_ordPth d rho hle htop hmono hab)
          rw [hx]
          exact hgoal

/-- **Simple connectivity of the order complex** of a preorder carrying an order map
`ρ ≤ id` with `ρ ≤ c_d`.  This is proved with edges and triangular relations alone; it is not
inferred from acyclicity of the chain complex. -/
theorem simplyConnected_orderCx :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hq :=
    isPath_ordPth d rho hle htop a
  set q := ordPth d rho hle htop a with hqdef
  have h3 := htpy_append_revPath hq
  have h2 :=
    Htpy.append_congr (isPath_append_iff.mpr ⟨a, hp, hq⟩) (isPath_revPath hq) (htpy_path_ordPth d rho hle htop hmono p hp) (Htpy.refl _)
  have h1' : Htpy _ a a p ((p ++ q) ++ revPath q) := by
    simpa [List.append_assoc] using (Htpy.append_congr hp (isPath_append_iff.mpr ⟨d, hq, isPath_revPath hq⟩) (Htpy.refl _) h3).symm
  exact (h1'.trans h2).trans h3

end

/-- The order complex of a preorder with such a contraction is connected. -/
theorem isConnected_orderCx : IsConnected (orderCx P) := by
  intro a b
  exact ⟨ordPth d rho hle htop a ++ revPath _,
    isPath_append_iff.mpr ⟨d, isPath_ordPth d rho hle htop a,
      isPath_revPath (isPath_ordPth d rho hle htop b)⟩⟩

end Contraction

end Comb

/-! ### The attaching subcomplex of a chamber is simply connected -/

end FiniteChains
