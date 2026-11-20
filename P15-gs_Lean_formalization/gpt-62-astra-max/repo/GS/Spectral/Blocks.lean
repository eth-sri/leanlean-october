module
public import GS.Isometric.ShuffledCS
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-! Work with the actual 2-by-2 blocks. `mix S x` uses the same eigenbasis
in every block; equality is just a diagonal intertwining equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Matrix GS.Isometric
open scoped MatrixOrder ComplexOrder
namespace GS.Spectral
variable {𝕜 : Type*} [RCLike 𝕜] {m q : ℕ}
abbrev U (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) := ↥(unitary (Square 𝕜 q))
abbrev Box (𝕜 : Type*) (q : ℕ) := Fin q → Fin q → Square 𝕜 2

@[simp] lemma star_self (s : U 𝕜 m) : s.valᴴ*s.val = 1 := s.property.1
@[simp] lemma self_star (s : U 𝕜 m) : s.val*s.valᴴ = 1 := s.property.2
@[simp] lemma cancel (s : U 𝕜 m) (X : Square 𝕜 m) : s.valᴴ*(s.val*X) = X := IsU.star_cancel s.property X
@[simp] lemma cancel' (s : U 𝕜 m) (X : Square 𝕜 m) : s.val*(s.valᴴ*X) = X := IsU.cancel_star s.property X

/-- Coordinates on a family of middle blocks conjugated by one common basis. -/
def mix (s : U 𝕜 m) (a : Fin m → 𝕜) := s.valᴴ * diagonal a * s.val
lemma mix_eq {s t : U 𝕜 m} {a b : Fin m → 𝕜} : mix s a = mix t b ↔
    ∀ i j, (s.val*t.valᴴ) i j ≠ 0 → a i = b j := by
  have eq : mix s a = mix t b ↔ diagonal a * (s.val*t.valᴴ) = (s.val*t.valᴴ) * diagonal b := by
    refine ⟨fun h => ?_,fun h => ?_⟩
    · simpa [mix,mul_assoc,t.property.2] using congrArg (fun X => s.val * X * t.valᴴ) h
    · simpa [mix, mul_assoc] using congrArg (fun X => s.valᴴ * X * t.val) h
  rw [eq, ← Matrix.ext_iff]; simp only [diagonal_mul,mul_diagonal]
  grind [mul_comm]

/-- An injective change of coordinates preserves *all* fibres, including
coincident eigenvalues, without picking or ordering eigenvectors. -/
lemma mix_fibres {α : Type*} {β γ : Type} {x y : Fin m → α} {s t : U 𝕜 m}
    (f : α → β → 𝕜) (g : α → γ → 𝕜) (e : ∀ a b, f a = f b ↔ g a = g b) :
    (∀ j, mix s (fun k => f (x k) j) = mix t (fun k => f (y k) j)) ↔
      ∀ j, mix s (fun k => g (x k) j) = mix t (fun k => g (y k) j) := by
  have test {ι} (h : α → ι → 𝕜) : (∀ j, mix s (fun k => h (x k) j) = mix t (fun k => h (y k) j)) ↔
      ∀ i k, (s.val*t.valᴴ) i k ≠ 0 → h (x i) = h (y k) := by
    simp only [mix_eq,funext_iff]; grind
  rw [test f,test g]; simp_rw [e]

abbrev Raw (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) := (Fin q → U 𝕜 2) × (Fin 2 → U 𝕜 q) × (Fin q → U 𝕜 2)
def eval (p : Raw 𝕜 q) : Box 𝕜 q := fun i j => (p.1 i).val * diagonal (fun k => (p.2.1 k).val i j) * (p.2.2 j).val
@[fun_prop] lemma continuous_eval : Continuous (@eval 𝕜 _ q) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  apply Continuous.mul _ (by fun_prop); apply Continuous.mul (by fun_prop)
  apply Continuous.matrix_diagonal; apply continuous_pi; intro k
  exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_subtype_val.comp ((continuous_apply k).comp (continuous_fst.comp continuous_snd))))

/-- Undo the scalar index flattening; this is just a permutation of entries. -/
def unflat : Square 𝕜 (q*2) ≃ₜ Box 𝕜 q where
  toFun X i j a b := X (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b))
  invFun X i j := let x := finProdFinEquiv.symm i; let y := finProdFinEquiv.symm j; X x.1 y.1 x.2 y.2
  left_inv := by intro X; ext i j; grind
  right_inv := by intro X; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

abbrev Family (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) := let P := perm 𝕜 (scalarShuffle q 2); {X | In₃U 2 q 2 P Pᴴ X}

/-- In the two orderings of the scalar indices the supported factors are
precisely packed unitary blocks. Reading the product gives `eval` directly. -/
def familyBlocks : Family 𝕜 q ≃ₜ Set.range (@eval 𝕜 _ q) := unflat.subtype fun X => by
  let σ := scalarShuffle q 2
  let f := finProdFinEquiv (m := q) (n := 2)
  let e := (Equiv.prodComm ..).trans f
  let g := f.trans σ
  let P := perm 𝕜 σ
  have outer := packed (𝕜 := 𝕜) e (fun _ => rfl)
  have mid := packed (𝕜 := 𝕜) g (fun i => by simpa [g,f,σ] using (shuffle_label (σ.symm i)).symm)
  have block (u : Raw 𝕜 q) : unflat (pack e (fun i => (u.1 i).val) * Pᴴ * pack g (fun i => (u.2.1 i).val) * P * pack e (fun i => (u.2.2 i).val)) = eval u := by
    let B i := (u.2.1 i).val
    have he := unwire f σ B
    funext i j; change readBlock e (_ * Pᴴ * pack g B * P * _) i j = _
    rw [mul_assoc _ Pᴴ,mul_assoc _ (Pᴴ * _),he]
    simp [read_mul,ite_mul,mul_ite,e,read_cross,eval,B]
  constructor
  · rintro ⟨R,M,L,hr,hm,hl,ur,um,ul,rfl⟩
    obtain ⟨u,hu,rfl⟩ := (outer _).1 ⟨hl,ul⟩; obtain ⟨v,hv,rfl⟩ := (outer _).1 ⟨hr,ur⟩
    obtain ⟨b,hb,rfl⟩ := (mid _).1 ⟨hm,um⟩
    exact ⟨(fun i => ⟨u i,hu i⟩,fun i => ⟨b i,hb i⟩,fun i => ⟨v i,hv i⟩),(block _).symm⟩
  · rintro ⟨u,h⟩
    have side (w : Fin q → U 𝕜 2) := (outer _).2 ⟨_,fun i => (w i).property,rfl⟩
    obtain ⟨s,t⟩ := (mid _).2 ⟨_,fun i => (u.2.1 i).property,rfl⟩
    exact ⟨_,_,_,(side u.2.2).1,s,(side u.1).1,(side u.2.2).2,t,(side u.1).2, unflat.injective (h.symm.trans (block u).symm)⟩

lemma polar {u v : U 𝕜 m} {A B : Square 𝕜 m} (ha : A.PosDef) (hb : B.PosDef)
    (h : u.val*A = v.val*B) : u = v := by
  have eq : A^2 = B^2 := by simpa [conjTranspose_mul,ha.isHermitian.eq,hb.isHermitian.eq,mul_assoc,pow_two] using congrArg (fun X : Square 𝕜 m => Xᴴ*X) h
  obtain rfl := (CFC.sq_eq_sq_iff A B ha.posSemidef.nonneg hb.posSemidef.nonneg).mp eq
  exact Subtype.ext (ha.isUnit.mul_right_cancel h)
end GS.Spectral
