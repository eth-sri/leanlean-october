import RequestProject.MirrorContraction
import RequestProject.CombPi1
import RequestProject.Tac


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

bwd

namespace FiniteChains
namespace Comb

universe u

/-! ### The order complex of a preorder -/

section OrderComplex

variable (P : Type u) [Preorder P]

/-- Oriented edges of the order complex: comparable ordered pairs. -/
def OrdEdge := {p : P × P // p.1 ≤ p.2}

/-- Two-cells of the order complex: chains `a ≤ b ≤ c`. -/
def OrdTri := {t : P × P × P // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2}

/-- The two-skeleton of the order complex of a preorder: vertices are elements, edges are
comparable pairs, and every chain `a ≤ b ≤ c` carries a triangle attached along
`[a,b][b,c][a,c]⁻¹`. -/
def orderCx : Complex2.{u} where
  V := P
  E := OrdEdge P
  F := OrdTri P
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t :=
    [((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true),
     ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true),
     ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false)]
  att_isLoop := fun _ => ⟨rfl, rfl, rfl, rfl⟩

variable {P}

/-- The edge `a → b` attached to `a ≤ b`. -/
def ordPos {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), true)

/-- The edge `a ≤ b` traversed backwards, from `b` to `a`. -/
def ordNeg {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), false)

@[simp] theorem revGerm_ordPos {a b : P} (h : a ≤ b) : revGerm (ordPos h) = ordNeg h := rfl

@[simp] theorem revGerm_ordNeg {a b : P} (h : a ≤ b) : revGerm (ordNeg h) = ordPos h := rfl

theorem isPath_ordPos (h : a ≤ b) :
    IsPathX (orderCx P) [ordPos h] a b := by tauto

theorem isPath_ordNeg (h : a ≤ b) :
    IsPathX (orderCx P) [ordNeg h] b a := by tauto

theorem isPath_nil' (a : P) :
    IsPathX (orderCx P) ([]) a a := rfl

/-- Backtrack cancellation for an edge traversed forwards and then backwards. -/
theorem htpy_ordPos_ordNeg {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) a a [ordPos h, ordNeg h] [] := by
  have := htpy_append_revPath (X := orderCx P) (isPath_single (X := orderCx P) (ordPos h))
  tauto

/-- Backtrack cancellation for an edge traversed backwards and then forwards. -/
theorem htpy_ordNeg_ordPos {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) b b [ordNeg h, ordPos h] [] := by
  have := htpy_append_revPath (X := orderCx P) (isPath_single (X := orderCx P) (ordNeg h))
  tauto

/-- **The triangular relation**: `[a,b][b,c] ≃ [a,c]` for a chain `a ≤ b ≤ c`. -/
theorem htpy_orderCx_tri {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    Htpy (orderCx P) a c [ordPos hab, ordPos hbc] [ordPos (hab.trans hbc)] := by
  have hac := hab.trans hbc
  have hp : IsPathX (orderCx P) [ordPos hab, ordPos hbc] a c :=
    by tauto
  have hq : IsPathX (orderCx P) ([]) c c := rfl
  have h1 :=
    Htpy.append_congr hp hq (Htpy.refl _) (htpy_ordNeg_ordPos hac).symm
  have hfull : IsPathX (orderCx P)
      [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac] a c := by trivial
  have h2 : Htpy _ a c [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac]
      [ordPos hac] := by
    refine Htpy.of_step ⟨hfull, isPath_ordPos hac, Or.inr ?_⟩
    exact ⟨[], [ordPos hac], ⟨(a, b, c), hab, hbc⟩, rfl, rfl⟩
  simpa using h1.trans h2

end OrderComplex

/-! ### The explicit contraction of edge paths -/

section Contraction

variable {P : Type u} [Preorder P]

/-- The path `p_σ = [σ,ρσ]⁻¹[ρσ,d]` of the text: from `σ` down to `ρσ` and up to `d`. -/
def ordPth d (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d) (x : P) := [ordNeg (hle x), ordPos (htop x)]


/-- **The key identity** `[σ,τ] p_τ ≃ p_σ` for `σ ≤ τ`, obtained from the three triangular
relations for the chains `ρσ ≤ σ ≤ τ`, `ρσ ≤ ρτ ≤ τ` and `ρσ ≤ ρτ ≤ d`. -/
theorem htpy_ordPos_ordPth d (rho : P → P) hle
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) a d (ordPos hab :: ordPth d rho hle htop b) (ordPth d rho hle htop a) := by
  have hrs := hmono hab
  have hrb : rho a ≤ b := by grind
  have pa2 : IsPathX (orderCx P) [ordNeg (hle a), ordPos hrs] a (rho b) :=
    by tauto
  have pb2 : IsPathX (orderCx P)
      [ordNeg (hle b), ordPos (htop b)] b d := by tauto
  have p3 : IsPathX (orderCx P)
      [ordPos hab, ordNeg (hle b), ordPos (htop b)] a d := by tauto
  -- Step 1: expand `[ρa,d]` as `[ρa,ρb][ρb,d]`.
  have s1 : Htpy _ a d ([ordNeg (hle a)] ++ [ordPos (htop a)])
      ([ordNeg (hle a)] ++ [ordPos hrs, ordPos (htop b)]) :=
    Htpy.append_congr (by tauto) (by tauto) (Htpy.refl _)
      (htpy_orderCx_tri hrs _).symm
  -- Step 2: insert the backtrack `[ρb,b][ρb,b]⁻¹`.
  have s2 : Htpy _ a d
      ([ordNeg (hle a), ordPos hrs] ++ [] ++ [ordPos (htop b)])
      ([ordNeg (hle a), ordPos hrs] ++ [ordPos (hle b), ordNeg (hle b)] ++
        [ordPos (htop b)]) :=
    (htpy_ordPos_ordNeg _).symm.congr_append (c := a) (d := d) pa2
      (by tauto)
  -- Step 3: contract `[ρa,ρb][ρb,b]` to `[ρa,b]`.
  have s3 : Htpy _ a d
      ([ordNeg (hle a)] ++ [ordPos hrs, ordPos (hle b)] ++ [ordNeg (hle b), ordPos (htop b)])
      ([ordNeg (hle a)] ++ [ordPos hrb] ++ [ordNeg (hle b), ordPos (htop b)]) :=
    (htpy_orderCx_tri hrs _).congr_append (c := a) (d := d) (by tauto) pb2
  -- Step 4: expand `[ρa,b]` as `[ρa,a][a,b]`.
  have s4 : Htpy _ a d
      ([ordNeg (hle a)] ++ [ordPos hrb] ++ [ordNeg (hle b), ordPos (htop b)])
      ([ordNeg (hle a)] ++ [ordPos (hle a), ordPos hab] ++
        [ordNeg (hle b), ordPos (htop b)]) :=
    (htpy_orderCx_tri _ hab).symm.congr_append (c := a) (d := d)
      (by tauto) pb2
  -- Step 5: cancel the backtrack `[ρa,a]⁻¹[ρa,a]`.
  have s5 :=
    (htpy_ordNeg_ordPos (hle a)).congr_append (c := a) (d := d) (isPath_nil' a) p3
  have chain := ((((s1.trans s2).trans s3).trans s4).trans s5)
  exact chain.symm

/-- The reversed form of the key identity: `[σ,τ]⁻¹ p_σ ≃ p_τ`. -/
theorem htpy_ordNeg_ordPth d (rho : P → P) hle
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) b d (ordNeg hab :: ordPth d rho hle htop a) (ordPth d rho hle htop b) := by
  have h1 :=
    Htpy.append_congr (isPath_ordNeg hab) (by tauto) (Htpy.refl _)
      (htpy_ordPos_ordPth d rho hle htop hmono hab).symm
  have h2 : Htpy _ b d
      ([] ++ [ordNeg hab, ordPos hab] ++ ordPth d rho hle htop b)
      ([] ++ [] ++ ordPth d rho hle htop b) :=
    (htpy_ordNeg_ordPos hab).congr_append (c := b) (d := d) (isPath_nil' b)
      (by tauto)
  exact h1.trans h2

/-- **Every edge path is the standard one**: for a path `p` from `σ` to `τ` one has
`p · p_τ ≃ p_σ`; in particular every path `σ → τ` is homotopic to `p_σ p_τ⁻¹`. -/
theorem htpy_path_ordPth d (rho : P → P) hle
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y}, x ≤ y → rho x ≤ rho y) :
    ∀ p {x y : P},
      IsPathX (orderCx P) p x y →
      Htpy (orderCx P) x d (p ++ ordPth d rho hle htop y) (ordPth d rho hle htop x) := by
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
          have hih := ih hrest'
          have h1 :=
            Htpy.append_congr (isPath_ordNeg hab)
              (isPath_append_iff.mpr (by tauto))
              (Htpy.refl _) hih
          have h2 := htpy_ordNeg_ordPth d rho hle htop hmono hab
          have hgoal := h1.trans h2
          aesop
      | true =>
          have hrest' := hrest
          have hih := ih hrest'
          have h1 :=
            Htpy.append_congr (isPath_ordPos hab)
              (isPath_append_iff.mpr (by tauto))
              (Htpy.refl _) hih
          have h2 := htpy_ordPos_ordPth d rho hle htop hmono hab
          have hgoal := h1.trans h2
          aesop

/-- **Simple connectivity of the order complex** of a preorder carrying an order map
`ρ ≤ id` with `ρ ≤ c_d`.  This is proved with edges and triangular relations alone; it is not
inferred from acyclicity of the chain complex. -/
theorem simplyConnected_orderCx d (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y}, x ≤ y → rho x ≤ rho y) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hq : IsPathX (orderCx P) (ordPth d rho hle htop a) a d :=
    by tauto
  set q := ordPth d rho hle htop a with hqdef
  have h := htpy_path_ordPth d rho hle htop hmono p hp
  have h3 := htpy_append_revPath hq
  have h1 :=
    Htpy.append_congr hp (isPath_append_iff.mpr (by tauto)) (Htpy.refl _) h3
  have h2 :=
    Htpy.append_congr (isPath_append_iff.mpr (by grind)) (isPath_revPath hq) h (Htpy.refl _)
  have h1' : Htpy _ a a p ((p ++ q) ++ revPath q) := by
    simpa using h1.symm
  exact (h1'.trans h2).trans h3

/-- The order complex of a preorder with such a contraction is connected. -/
theorem isConnected_orderCx d (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) : IsConnected (orderCx P) := by
  intro a b
  exact ⟨ordPth d rho hle htop a ++ revPath (ordPth d rho hle htop b),
    isPath_append_iff.mpr (by tauto)⟩

end Contraction

end Comb

/-! ### The attaching subcomplex of a chamber is simply connected -/

namespace Mirror

universe u

variable {V : Type u} [DecidableEq V]

section RACG

open RACG

variable [Fintype V] (A : CommRel V)
