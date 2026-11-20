module
public import Mathlib

@[expose] public section
namespace CoxeterGrowth.Triangle

/-- The dihedral head `(e,j)` represents a possible `c` followed by `j` alternating letters starting at `s`. -/
abbrev Head (m : ℕ) := {x : Bool × ℕ // x.2 < m}

/-- Prepend the noncentral generator, reflecting at the far end of the dihedral cycle. -/
def da (m : ℕ) (x : Bool × ℕ) : Bool × ℕ :=
  if x.1 then
    if x.2+2 < m then (false,x.2+2) else (true,2*m-x.2-3)
  else if x.2 = 0 then (false,1) else if x.2 = 1 then (false,0) else (true,x.2-2)

def dc (x : Bool × ℕ) : Bool × ℕ := (!x.1, x.2)
def headLen (x : Bool × ℕ) : ℕ := x.1.toNat + x.2

lemma da_spec {m : ℕ} (hm : 2 ≤ m) (x : Head m) :
    (da m x).2 < m ∧ da m (da m x) = x ∧ headLen (da m x) ≤ headLen x + 1 := by
  rcases x with ⟨⟨_ | _,j⟩,hj⟩ <;> grind [da, headLen]

def headS {m : ℕ} (hm : 2 ≤ m) : Equiv.Perm (Head m) :=
  Function.Involutive.toPerm (f := fun x => ⟨da m x, (da_spec hm x).1⟩)
    fun x => Subtype.ext (da_spec hm x).2.1

def headC (m : ℕ) : Equiv.Perm (Head m) :=
  Function.Involutive.toPerm (f := fun x => ⟨dc x, x.2⟩)
    fun x => Subtype.ext (by simp [dc])

/-- Number the dihedral cycle so that the product of the two generators advances by two. -/
def sig (m : ℕ) (x : Bool × ℕ) : ℕ := if x.1 then 2*m-1-x.2 else x.2

lemma sig_T {m : ℕ} (hm : 2 ≤ m) (x : Head m) :
    (sig m (da m (dc x)) : ZMod (m*2)) = (sig m x : ZMod (m*2)) + 2 := by
  suffices sig m (da m (dc x)) ≡ sig m x + 2 [MOD m*2] by
    simpa using (ZMod.natCast_eq_natCast_iff ..).2 this
  rw [Nat.modEq_iff_dvd]
  rcases x with ⟨⟨_ | _,j⟩,hj⟩ <;> simp [da, dc, sig] <;> split_ifs <;> simp_all <;>
    first | exact ⟨0, by omega⟩ | exact ⟨1, by omega⟩

lemma sig_inj {m : ℕ} : Function.Injective (fun x : Head m => (sig m x : ZMod (m*2))) := by
  rintro ⟨⟨e,j⟩,hj⟩ ⟨⟨f,k⟩,hk⟩ h
  rw [ZMod.natCast_eq_natCast_iff] at h
  cases e <;> cases f <;> simp [sig] at h <;>
    have := h.eq_of_lt_of_lt (by omega) (by omega) <;> simp_all <;> omega

lemma head_rel {m : ℕ} (hm : 2 ≤ m) : (headS hm * headC m) ^ m = 1 := by
  have h : Function.Semiconj (fun x : Head m => (sig m x : ZMod (m*2)))
      (headS hm * headC m) (· + 2) := sig_T hm
  have h0 : (m : ZMod (m*2)) * 2 = 0 := (Nat.cast_mul m 2).symm.trans (ZMod.natCast_self _)
  exact Equiv.ext fun x => sig_inj (by
    simpa [Equiv.Perm.coe_pow, add_right_iterate_apply, nsmul_eq_mul, h0] using (h.iterate_right m).eq x)

@[local grind] def hl (x : ℕ × ℕ) : ℕ := x.1+x.2

/-- A dihedral head followed by nonempty alternating blocks. -/
abbrev Raw := (Bool × ℕ) × List ℕ

@[simp, local grind] def VT : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | p, q, k :: r => 0 < k ∧ k < p ∧ VT q p r

abbrev V (p q : ℕ) (v : Raw) : Prop := v.1.2 < p ∧ VT q p v.2
abbrev NF (p q : ℕ) := {v : Raw // V p q v}
@[local grind] def len (v : Raw) : ℕ := headLen v.1 + v.2.sum

/-- Change which generator has a possibly empty leading block. -/
def swap (v : Raw) : Raw :=
  let t := match v.1.2, v.2 with
    | 0, [] => (0, [])
    | 0, k :: r => (k, r)
    | j+1, r => (0, (j+1) :: r)
  ((v.1.1, t.1), t.2)

lemma swap_spec {p q : ℕ} (hq : 2 ≤ q) (v : Raw) (h : V p q v) :
    V q p (swap v) ∧ swap (swap v) = v := by
  grind [swap]

@[simp] lemma len_swap : ∀ v : Raw, len (swap v) = len v
  | ((_, 0), []) => rfl
  | ((_, 0), _ :: _) | ((_, _+1), _) => by simp [swap, len, headLen, add_assoc]

def swapEquiv {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) : NF p q ≃ NF q p where
  toFun v := ⟨swap v, (swap_spec hq v v.2).1⟩
  invFun v := ⟨swap v, (swap_spec hp v v.2).1⟩
  left_inv v := Subtype.ext (swap_spec hq v v.2).2
  right_inv v := Subtype.ext (swap_spec hp v v.2).2

/-- Extend a permutation of the dihedral head by leaving the tail unchanged. -/
def onHead {p q : ℕ} : Equiv.Perm (Head p) →* Equiv.Perm (NF p q) where
  toFun f := Equiv.subtypeProdEquivProd.symm.permCongr (f.prodCongr (Equiv.refl _))
  map_one' := rfl
  map_mul' _ _ := rfl

section Actions

variable {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)

local notation "A" => onHead (q := q) (headS hp)
local notation "C" => onHead (q := q) (headC p)
local notation "S" => Equiv.permCongrHom (swapEquiv hq hp)
local notation "B" => S (onHead (q := p) (headS hq))

def gen : Fin 3 → Equiv.Perm (NF p q)
  | 0 => A
  | 1 => B
  | 2 => C

lemma gen_sq (i : Fin 3) : gen hp hq i * gen hp hq i = 1 := by
  fin_cases i <;> exact mul_eq_one_iff_inv_eq.mpr rfl

lemma gen_ac : (gen hp hq 0 * gen hp hq 2) ^ p = 1 := by
  simpa [gen] using congrArg (onHead (q := q)) (head_rel hp)

lemma swap_C : S (onHead (q := p) (headC q)) = C := by
  refine Equiv.ext fun v => Subtype.ext ?_
  change (dc (swap (swap v)).1, (swap (swap v)).2) = (dc v.1.1, v.1.2)
  rw [(swap_spec hq v v.2).2]

lemma gen_bc : (gen hp hq 1 * gen hp hq 2) ^ q = 1 := by
  simpa only [gen, map_pow, map_mul, map_one, swap_C hp hq] using congrArg S (gen_ac hq hp)

lemma len_gen (i : Fin 3) (v : NF p q) : len (gen hp hq i v) ≤ len v + 1 := by
  have aux {m k} (hm : 2 ≤ m) (x : NF m k) : len (da m x.1.1,x.1.2) ≤ len x + 1 := by
    have := (da_spec hm ⟨x.1.1,x.2.1⟩).2.2
    simp [len] at *
    omega
  match i with
  | 0 => exact aux hp v
  | 1 =>
    change len (swap (da q (swap v).1, (swap v).2)) ≤ _
    rw [len_swap, ← len_swap v]
    exact aux hq (swapEquiv hp hq v)
  | 2 =>
    change len (dc v.1.1, v.1.2) ≤ _
    grind [headLen, dc, Bool.toNat]

lemma len_drop {m j : ℕ} (hj : 0 < j) (r : List ℕ) : len (da m (false,j),r) < len ((false,j),r) := by
  grind [len,headLen,da]

def emptyNF : NF p q := ⟨((false,0),[]), ⟨show 0 < p by omega, trivial⟩⟩

lemma descent : ∀ v : NF p q, v = emptyNF hp ∨ ∃ i : Fin 3, len (gen hp hq i v) < len v
  | ⟨((false,0),[]), _⟩ => Or.inl rfl
  | ⟨((false,0),k::r), h⟩ => Or.inr ⟨1, by
      change len (swap (da q (false,k),r)) < len ((false,0),k::r)
      rw [len_swap, ← len_swap ((false,0),k::r)]
      exact len_drop h.2.1 r⟩
  | ⟨((false,j+1),r), _⟩ => Or.inr ⟨0, len_drop (m := p) (Nat.succ_pos j) r⟩
  | ⟨((true,j),r), _⟩ => Or.inr ⟨2, by change len (dc (true,j),r) < _; simp [dc,len,headLen]⟩

end Actions
/-! ## Counting by length -/
open Finset PowerSeries

abbrev Slice (p q n : ℕ) := {v : Raw // V p q v ∧ len v = n}
noncomputable abbrev nfCount (p q n : ℕ) := Nat.card (Slice p q n)

def offsets (p q : ℕ) : Finset (ℕ × ℕ) := Ico 1 p ×ˢ Ico 1 q
lemma offset_bounds {p q : ℕ} {u : ℕ × ℕ} (h : u ∈ offsets p q) : 0 < hl u ∧ hl u < p+q := by
  grind [offsets]

section
variable (p q n : ℕ)

def cut := (offsets p q).filter fun u => hl u ≤ n
def base : Finset ((Bool × ℕ) × ℕ) := (univ ×ˢ range p) ×ˢ range (max 1 q)
def baseAt := (base p q).filter fun (x,k) => headLen x + k = n

end

@[simp, grind =] lemma in_cut {p q n : ℕ} {u : ℕ × ℕ} : u ∈ cut p q n ↔
    (0 < u.1 ∧ u.1 < p) ∧ (0 < u.2 ∧ u.2 < q) ∧ hl u ≤ n := by
  simp [cut, offsets, Nat.succ_le_iff, and_assoc]

@[simp, grind =] lemma mem_baseAt {p q n : ℕ} {x : Bool × ℕ} {k : ℕ} :
    (x,k) ∈ baseAt p q n ↔ x.2 < p ∧ (k = 0 ∨ k < q) ∧ headLen x + k = n := by
  simp [baseAt, base, lt_max_iff, and_assoc]

section
variable (p q n : ℕ)

/-- Strip two alternating blocks, or count a terminal tail. -/
def sliceSplit : Slice p q n ≃
    (baseAt p q n : Type) ⊕ (Σ u : cut p q n, Slice p q (n-hl u)) where
  toFun
    | ⟨(x,[]),h⟩ => .inl ⟨(x,0), by grind⟩
    | ⟨(x,[k]),h⟩ => .inl ⟨(x,k), by grind⟩
    | ⟨(x,k::j::r),h⟩ =>
      .inr ⟨⟨(j,k), by grind⟩,
        (x,r), by grind⟩
  invFun
    | .inl ⟨(x,0),h⟩ => ⟨(x,[]), by grind⟩
    | .inl ⟨(x,k+1),h⟩ => ⟨(x,[k+1]), by grind⟩
    | .inr ⟨⟨(j,k),hu⟩,⟨(x,r),hn⟩⟩ => ⟨(x,k::j::r), by grind⟩
  left_inv := by
    rintro ⟨⟨x, _ | ⟨k, _ | r⟩⟩,h,hn⟩
    · rfl
    · cases k; exact (Nat.lt_irrefl _ h.2.1).elim; rfl
    · rfl
  right_inv := by rintro (⟨⟨_, _ | _⟩,_⟩ | ⟨_,_⟩) <;> rfl

instance sliceFintype (k : ℕ) : Fintype (Slice p q k) := by
  letI (u : cut p q k) := sliceFintype (k - hl u)
  exact Fintype.ofEquiv _ (sliceSplit p q k).symm
termination_by k
decreasing_by
  have := in_cut.1 u.2
  simp [hl] at *
  omega

lemma card_rec : nfCount p q n = (baseAt p q n).card +
    ∑ u ∈ cut p q n, nfCount p q (n-hl u) := by
  rw [nfCount, Nat.card_congr (sliceSplit p q n), Nat.card_sum, Nat.card_eq_finsetCard, Nat.card_sigma,
    sum_coe_sort _ (fun u => nfCount p q (n-hl u))]

noncomputable abbrev nfSeries : ℤ⟦X⟧ := mk fun k => (nfCount p q k : ℤ)

scoped notation:max "S[" m "," x "]" => (∑ i ∈ Ico 1 m, x ^ i)
scoped notation:max "F[" p "," q "," x "]" => (S[p,x] * S[q,x])
scoped notation:max "P[" m "]" => S[m,(X : ℤ⟦X⟧)]
scoped notation:max "R[" m "]" => (∑ i ∈ range m, (X : ℤ⟦X⟧) ^ i)

lemma offset_sum {R : Type*} [CommSemiring R] (x : R) :
    ∑ u ∈ offsets p q, x ^ hl u = F[p,q,x] := by
  simp [offsets, sum_product, hl, pow_add, sum_mul_sum]

lemma coeff_base (hq : 1 ≤ q) :
    ((baseAt p q n).card : ℤ) = coeff n ((1 + X) * R[p] * R[q]) := by
  have hpoly : (∑ x ∈ base p q, (X : ℤ⟦X⟧) ^ (headLen x.1 + x.2)) = (1 + X) * R[p] * R[q] := by
    simp [base, headLen, max_eq_right hq, sum_product, pow_add, ← mul_sum, ← sum_mul, mul_comm, add_comm]
  rw [← hpoly, map_sum]
  simp [coeff_X_pow, eq_comm, baseAt]

/-- Generating function of length-graded normal forms. -/
theorem nf_series (hq : 1 ≤ q) : nfSeries p q * (1 - P[p] * P[q]) = (1 + X) * R[p] * R[q] := by
  ext n
  rw [← offset_sum, mul_sub, mul_one, map_sub, sub_eq_iff_eq_add, coeff_mk, card_rec,
    Nat.cast_add, coeff_base p q n hq]
  congr 1
  simp [cut, Nat.cast_sum, mul_sum, map_sum, coeff_mul_X_pow', ← sum_filter]

end

lemma slice_rec {p q n : ℕ} (hq : 1 ≤ q) (hn : p+q ≤ n) :
    nfCount p q n = ∑ u ∈ offsets p q, nfCount p q (n-hl u) := by
  have hz : baseAt p q n = ∅ := by
    ext ⟨⟨_ | _,j⟩,k⟩ <;> simp [headLen] <;> omega
  rw [card_rec, hz, card_empty, zero_add, cut, filter_true_of_mem (fun u hu => (offset_bounds hu).2.le.trans hn)]

lemma tail_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') {r : List ℕ} (h : VT p q r) :
    VT p' q' r := by
  induction r generalizing p q p' q' <;> grind

lemma slice_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (n : ℕ) :
    nfCount p q n ≤ nfCount p' q' n :=
  Nat.card_mono (Set.finite_coe_iff.1 (inferInstanceAs (Finite (Slice p' q' n))))
    fun _ ⟨⟨hj,hr⟩,hn⟩ => ⟨⟨hj.trans_le hp,tail_mono hq hp hr⟩,hn⟩

def sliceInter (p q n : ℕ) : {v : NF p q // len v = n} ≃ Slice p q n :=
  Equiv.subtypeSubtypeEquivSubtypeInter (V p q) (fun v => len v = n)

lemma slice_symm {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (n : ℕ) : nfCount p q n = nfCount q p n :=
  Nat.card_congr ((sliceInter p q n).symm.trans (((swapEquiv hp hq).subtypeEquiv
    fun v => by simp [swapEquiv]).trans (sliceInter q p n)))

lemma tail_ones (n : ℕ) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) : VT p q (List.replicate n 1) := by
  induction n generalizing p q <;> grind

lemma slice_pos {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (n : ℕ) : 0 < nfCount p q n := by
  have : Nonempty (Slice p q n) := ⟨⟨((false,0), List.replicate n 1), ⟨show 0 < p by omega, tail_ones n hq hp⟩, by simp [len, headLen]⟩⟩
  exact Nat.card_pos

end CoxeterGrowth.Triangle
