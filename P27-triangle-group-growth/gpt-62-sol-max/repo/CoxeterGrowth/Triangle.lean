module
public import CoxeterGrowth.TriangleNF

@[expose] public section
namespace CoxeterGrowth.Triangle

open CoxeterSystem

section Model

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

/-- Product of an alternating word starting at `i`. Mathlib's word ends at `i`, so reverse it. -/
def alt (i j : Fin 3) (k : ℕ) : W := (cs.wordProd (alternatingWord j i k))⁻¹

@[simp] lemma alt_zero (i j : Fin 3) : alt cs i j 0 = 1 := by simp [alt, alternatingWord]
@[simp] lemma alt_succ (i j : Fin 3) (k : ℕ) :
    alt cs i j (k+1) = cs.simple i * alt cs j i k := by
  simp [alt, alternatingWord_succ, cs.wordProd_append]

def headVal (i : Fin 3) (x : Bool × ℕ) : W := cs.simple 2 ^ x.1.toNat * alt cs i 2 x.2

def tailVal : Fin 3 → Fin 3 → List ℕ → W
  | _, _, [] => 1
  | i, j, k :: r => alt cs i 2 k * tailVal j i r

def readNF (i j : Fin 3) (v : Raw) : W := headVal cs i v.1 * tailVal cs j i v.2

lemma read_swap (i j : Fin 3) : ∀ v : Raw, readNF cs j i (swap v) = readNF cs i j v
  | ((_,0),[]) | ((_,0),_ :: _) | ((_,_+1),_) => by simp [readNF, headVal, swap, tailVal, mul_assoc]

lemma headVal_da (i : Fin 3) {m : ℕ} (h₂ : 2 ≤ m) (hm : M i 2 = m) (x : Bool × ℕ) (hj : x.2 < m) :
    headVal cs i (da m x) = cs.simple i * headVal cs i x := by
  obtain ⟨e,j⟩ := x
  cases e
  · rcases j with _ | _ | j <;> simp [da, headVal, ← mul_assoc]
  · by_cases h : j + 2 < m
    · simp [da, h, headVal]
    · have hm' := (M.symmetric 2 i).trans hm
      have hb := cs.prod_alternatingWord_eq_prod_alternatingWord_sub 2 i (j+2) (by rw [hm']; omega)
      rw [hm', show m*2-(j+2) = (2*m-j-3)+1 by omega] at hb
      have e : alt cs 2 i ((2*m-j-3)+1) = alt cs i 2 (j+2) := congrArg Inv.inv hb.symm
      simpa [da, h, headVal, mul_assoc] using e

structure IsTri (M : CoxeterMatrix (Fin 3)) (p q : ℕ) : Prop where
  hp : 2 ≤ p
  hq : 2 ≤ q
  h01 : M 0 1 = 0
  h02 : M 0 2 = p
  h12 : M 1 2 = q

variable {p q : ℕ} (h : IsTri M p q)

local notation "G" => gen h.hp h.hq
local notation "readA" => readNF cs 0 1

lemma read_gen (i : Fin 3) (v : NF p q) : readA (G i v) = cs.simple i * readA v := by
  match i with
  | 0 =>
    change readA (da p v.1.1, v.1.2) = _
    simp only [readNF, headVal_da cs 0 h.hp h.h02 _ v.2.1, mul_assoc]
  | 1 =>
    change readA (swap (da q (swap v).1, (swap v).2)) = _
    rw [read_swap cs 1 0, ← read_swap cs 0 1 v]
    simp only [readNF, headVal_da cs 1 h.hq h.h12 _ (swap_spec h.hq v v.2).1.1, mul_assoc]
  | 2 =>
    obtain ⟨⟨⟨e,j⟩,r⟩,hv⟩ := v
    change readA (dc (e,j), r) = cs.simple 2 * readA ((e,j),r)
    cases e <;> simp [dc, readNF, headVal, ← mul_assoc]

lemma gen_liftable : M.IsLiftable G := by
  intro i j
  wlog hij : i ≤ j generalizing i j with H
  · rw [M.symmetric i j]
    have hc : SemiconjBy (G j) (G i * G j) (G j * G i) := (mul_assoc ..).symm
    exact (hc.pow_right _).eq_one_iff.2 (H j i (le_of_not_ge hij))
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> simp [gen_sq,h.h01,h.h02,h.h12,gen_ac,gen_bc]

noncomputable def encode (w : W) : NF p q := cs.lift ⟨G, gen_liftable h⟩ w (emptyNF h.hp)

lemma encode_mul (i : Fin 3) (w : W) : encode cs h (cs.simple i * w) = G i (encode cs h w) := by
  simp [encode, Equiv.Perm.mul_apply]

/-- Read a reduced representative to see that encoding preserves its value and cannot add length. -/
lemma encode_spec (w : W) : readA (encode cs h w) = w ∧ len (encode cs h w) ≤ cs.length w := by
  obtain ⟨l,hl,rfl⟩ := cs.exists_isReduced w
  rw [hl.eq]
  clear hl
  induction l with
  | nil => simp [encode, emptyNF, readNF, headVal, tailVal, len, headLen]
  | cons i l ih =>
    rw [cs.wordProd_cons, encode_mul, read_gen cs h, ih.1, List.length_cons]
    exact ⟨rfl, (len_gen h.hp h.hq _ _).trans (Nat.succ_le_succ ih.2)⟩

/-- Descending generators recover the normal form and give the opposite length bound. -/
lemma read_short (v : NF p q) : encode cs h (readA v) = v ∧ cs.length (readA v) ≤ len v := by
  induction v using (measure (fun v : NF p q => len v.1)).wf.induction with
  | _ v ih =>
    rcases descent h.hp h.hq v with rfl | ⟨i, hi⟩
    · simp [encode, emptyNF, readNF, headVal, tailVal]
    obtain ⟨he,hl⟩ := ih (G i v) hi
    have hv : G i (G i v) = v := by rw [← Equiv.Perm.mul_apply, gen_sq]; rfl
    have hr := read_gen cs h i (G i v)
    rw [hv] at hr
    rw [hr, encode_mul, he, hv]
    refine ⟨rfl, ?_⟩
    exact (cs.length_mul_le _ _).trans (by rw [cs.length_simple]; omega)

noncomputable def modelEquiv : W ≃ NF p q :=
  ⟨encode cs h, fun v => readA v, fun w => (encode_spec cs h w).1, fun v => (read_short cs h v).1⟩

lemma encode_len (w : W) : cs.length w = len (encode cs h w) := by
  have h' := encode_spec cs h w
  exact le_antisymm (by simpa only [h'.1] using (read_short cs h (encode cs h w)).2) h'.2

end Model
end CoxeterGrowth.Triangle

namespace TriangleGrowth

open CoxeterGrowth.Triangle Finset PowerSeries

scoped notation:max "sphere(" cs "," n ")" => Nat.card {w // CoxeterSystem.length cs w = n}
scoped notation:max "series(" cs ")" => (PowerSeries.mk fun n => (sphere(cs,n) : ℤ))

section
variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

lemma sphere_card {p q : ℕ} (h : IsTri M p q) (n : ℕ) : sphere(cs,n) = nfCount p q n :=
  Nat.card_congr (((modelEquiv cs h).subtypeEquiv fun w => by rw [encode_len cs h]; rfl).trans (sliceInter p q n))

variable {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
include hp hq

/-- The growth series for a triangle of type `(p, q, ∞)`. -/
theorem growth_series (h01 : M 0 1 = 0)
    (h02 : M 0 2 = p) (h12 : M 1 2 = q) : series(cs) * (1 - P[p] * P[q]) = (1 + X) * R[p] * R[q] := by
  simpa only [sphere_card cs (show IsTri M p q from ⟨hp,hq,h01,h02,h12⟩)] using
    nf_series p q (by omega)

/-- Sphere sizes are monotone in each finite label. -/
theorem sphere_mono (hpp : p ≤ p') (hqq : q ≤ q')
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (h01' : M' 0 1 = 0)
    (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n : ℕ) : sphere(cs,n) ≤ sphere(cs',n) := by
  rw [sphere_card cs ⟨hp,hq,h01,h02,h12⟩, sphere_card cs' ⟨hp.trans hpp,hq.trans hqq,h01',h02',h12'⟩]
  exact slice_mono hpp hqq n

/-- Interchanging the two finite labels leaves the sphere sizes unchanged. -/
theorem sphere_symm (h01 : M 0 1 = 0) (h02 : M 0 2 = p)
    (h12 : M 1 2 = q) (h01' : M' 0 1 = 0) (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n : ℕ) :
    sphere(cs,n) = sphere(cs',n) := by
  rw [sphere_card cs ⟨hp,hq,h01,h02,h12⟩, sphere_card cs' ⟨hq,hp,h01',h02',h12'⟩]
  exact slice_symm hp hq n
end

/-- A Coxeter matrix of type `(p, q, ∞)` exists for every `p, q ≥ 2`. -/
theorem triangle_matrix_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q := by
  refine ⟨⟨!![1,0,p; 0,1,q; p,q,1], Matrix.IsSymm.ext ?_, ?_, ?_⟩, rfl,rfl,rfl⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega

end TriangleGrowth
