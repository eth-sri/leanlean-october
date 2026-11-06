module

public import PaperStatements
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring
public import ThreeSumApsp.Sec2.Levels

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### The alphabets -/

/-- The left variables, listed: `x i` is `.inl i`, and `p i j` is `.inr (i, j)`. -/
def LeftVar.equiv : LeftVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .x i => .inl i
    | .p i j => .inr (i, j)
  invFun
    | .inl i => .x i
    | .inr (i, j) => .p i j
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | ⟨_, _⟩ <;> rfl

/-- The right variables, listed: `y j` is `.inl j`, and `q i j` is `.inr (i, j)`. -/
def RightVar.equiv : RightVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .y j => .inl j
    | .q i j => .inr (i, j)
  invFun
    | .inl j => .y j
    | .inr (i, j) => .q i j
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- The terms, listed: `P i j` is `some (i, j)`, and `P0` is `none`. -/
def Term.equiv : Term ≃ Option (Fin 3 × Fin 3) where
  toFun
    | .P i j => some (i, j)
    | .P0 => none
  invFun
    | some (i, j) => .P i j
    | none => .P0
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- Section 2.2: there are "seven left variables". -/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- Section 2.2: there are "seven right variables". -/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]

/-- Section 2.2: "Schönhage's identity has ten terms". -/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]

/-! ### Linear forms as polynomials -/

/-! ### Lemma 6 -/

/-! ### Which terms contribute to which output variables -/

/-- Section 2.2, second observation: "every term contributes to z₀". -/
@[simp]
theorem Term.contributes_z0 (lam : Term) : lam.Contributes .z0 := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form]

/-- Section 2.2, second observation: "only P_ij contributes to z_ij". -/
@[simp]
theorem Term.contributes_z_iff (lam : Term) (i j : Fin 3) :
    lam.Contributes (.z i j) ↔ lam = .P i j := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form, Pi.single_apply, eq_comm]

/-- The second observation in one statement: a term contributes to `z` if and only if `z` is inner,
that is `z₀`, or the term is `z.privateTerm`, which is `P_ij` for `z = z_ij`. (This is the term that
the private leaf of Section 2.4.3 has at a level with the variable `z`.) -/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert

/-- A sum over the terms contributing to `z` has the one summand `P_ij` for `z = z_ij`, and runs
over all terms for `z = z₀`. This is how step (4) of the recursions assembles the slice at `z`. -/
theorem Term.sum_contributes {A : Type*} [AddCommMonoid A] (c : Term → A) (z : OutVar) :
    ∑ lam : Term with lam.Contributes z, c lam
      = match z with
        | .z i j => c (.P i j)
        | .z0 => ∑ lam, c lam := by
  cases z with
  | z i j => simp [filter_eq']
  | z0 => simp




/-! ### Which leaves contribute to an output string -/

/-- In the proof of Lemma 7: "the leaves contributing to zw' are the λτ' with λ
contributing to z and τ' contributing to w'".  Here `λ = τ 0`, `τ' = Fin.tail τ`, `z = w 0` and
`w' = Fin.tail w`. -/
theorem Leaf.contributes_succ {L : ℕ} {τ : Leaf (L + 1)} {w : OutStr (L + 1)} :
    Leaf.Contributes τ w
      ↔ (τ 0).Contributes (w 0) ∧ Leaf.Contributes (Fin.tail τ) (Fin.tail w) := by
  simp only [Leaf.Contributes, Fin.forall_fin_succ, Fin.tail]

/-- A sum over the strings of length `L + 1` is a sum over the first variable `s` and the rest `u'`
of the string `s u'`. -/
theorem sum_strings_succ {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℤ) :
    ∑ u, f u = ∑ s, ∑ u', f (Fin.cons s u') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun _ => rfl).symm

/-- A sum over the leaves contributing to `w`, split by the first term of the leaf. -/
theorem Leaf.sum_contributes_succ {L : ℕ} (w : OutStr (L + 1)) (f : Leaf (L + 1) → ℤ) :
    ∑ τ : Leaf (L + 1) with Leaf.Contributes τ w, f τ
      = ∑ lam : Term with lam.Contributes (w 0),
          ∑ τ' : Leaf L with Leaf.Contributes τ' (Fin.tail w), f (Fin.cons lam τ') := by
  simp only [sum_filter, sum_strings_succ, Leaf.contributes_succ, Fin.cons_zero,
    Fin.tail_cons]
  refine sum_congr rfl fun lam _ => ?_
  by_cases h : lam.Contributes (w 0) <;> simp [h]

/-- In the proof of Lemma 8: the leaves contributing to `w` "are the leaves whose term at
level ℓ contributes to w_ℓ, independently for each ℓ". -/
theorem Leaf.filter_contributes_eq_piFinset {L : ℕ} (w : OutStr L) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w)
      = Fintype.piFinset fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ) := by
  ext τ
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rfl

/-! ### The two encodings at once -/

section encodeWith

variable {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}

/-- The number `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`, for an array `a` on the strings over a finite alphabet
and the coefficients `c` of a family of linear forms, one for each term. By definition it is
`Φ_τ(a)` for `c = φ` and `Ψ_τ(b)` for `c = ψ`. -/
def encodeWith (τ : Leaf L) (a : (Fin L → α) → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, c (τ ℓ) (u ℓ)

/-- For `L = 0` the only string is empty, and so are the products over the levels. -/
theorem encodeWith_zero (τ : Leaf 0) (a : (Fin 0 → α) → ℤ) : encodeWith c τ a = a Fin.elim0 := by
  simp [encodeWith, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]

/-- The number at the leaf `λτ'` for `a` is the number at the leaf `τ'` for `∑_s c_λ(s) a_s`. -/
theorem encodeWith_cons (lam : Term) (τ' : Leaf L) (a : (Fin (L + 1) → α) → ℤ) :
    encodeWith c (Fin.cons lam τ' : Leaf (L + 1)) a
      = encodeWith c τ' fun u' => ∑ s, c lam s * sliceAt a s u' := by
  simp only [encodeWith, sum_strings_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sliceAt, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun u' _ => sum_congr rfl fun s _ => by ring

end encodeWith

/-! ### Lemma 7 -/

/-- In the proof of Lemma 7: "for every leaf λτ' we have
Φ_{λτ'}(a) = ∑_s φ_λ(s) Φ_{τ'}(a_s) = Φ_{τ'}(A_λ)". -/
theorem Phi_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (a : LeftStr (L + 1) → ℤ) :
    Phi (Fin.cons lam τ' : Leaf (L + 1)) a = Phi τ' (encodeStepL lam a) :=
  encodeWith_cons phi lam τ' a

/-- In the proof of Lemma 7: "and similarly Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)". -/
theorem Psi_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (b : RightStr (L + 1) → ℤ) :
    Psi (Fin.cons lam τ' : Leaf (L + 1)) b = Psi τ' (encodeStepR lam b) :=
  encodeWith_cons psi lam τ' b

/-- "For L = 0, the only leaf is the empty string τ, and Φ_τ(a) = a […], as the products over the
levels are empty" (proof of Lemma 7). -/
theorem Phi_zero (τ : Leaf 0) (a : LeftStr 0 → ℤ) : Phi τ a = a Fin.elim0 :=
  encodeWith_zero phi τ a

/-- "and Ψ_τ(b) = b" (proof of Lemma 7). -/
theorem Psi_zero (τ : Leaf 0) (b : RightStr 0 → ℤ) : Psi τ b = b Fin.elim0 :=
  encodeWith_zero psi τ b

/-- Step (4) of `Full`, as it is read in the proof of Lemma 7:
`c[z w'] = ∑_{λ contributing to z} C_λ[w']`. -/
theorem Full_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Full (L + 1) a b w = ∑ lam : Term with lam.Contributes (w 0),
      Full L (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  rw [Term.sum_contributes]
  rfl

/-- In the proof of Lemma 7:
`Mult(a, b)[z w'] = ∑_{λ contributing to z} Mult(A_λ, B_λ)[w']`. -/
theorem Mult_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Mult a b w = ∑ lam : Term with lam.Contributes (w 0),
      Mult (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  simp only [Mult, Leaf.sum_contributes_succ, Phi_cons, Psi_cons]

/-- **Lemma 7**, second half.  "and it returns Mult(a, b)." -/
theorem Lemma7.returns_Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    Full L a b = Mult a b := by
  induction L with
  | zero =>
    funext w
    simp [Full, Full.run, Mult, Leaf.Contributes, Phi_zero, Psi_zero]
  | succ L ih =>
    funext w
    simp only [Full_succ, Mult_succ, ih]

/-! ### Lemma 8 -/

/-- The display in the proof of Lemma 8: the sum, over the leaves `τ` contributing
to `w`, of `∏_ℓ φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ)` "is the product of sums ∏_ℓ ∑_{τ_ℓ contributing to w_ℓ}
φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ) = ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) by (3)". -/
theorem prod_gamma_eq_sum_contributes {L : ℕ} (u : LeftStr L) (v : RightStr L) (w : OutStr L) :
    ∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)
      = ∑ τ : Leaf L with Leaf.Contributes τ w, (∏ ℓ, phi (τ ℓ) (u ℓ)) * ∏ ℓ, psi (τ ℓ) (v ℓ) := by
  simp only [gamma]
  rw [prod_univ_sum, Leaf.filter_contributes_eq_piFinset]
  exact sum_congr rfl fun τ _ => prod_mul_distrib

/-- **Lemma 8**.  "For all arrays a, b and every output string w,
Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) γ(u₂, v₂, w₂) ⋯ γ(u_L, v_L, w_L) a[u] b[v],
the sum over all left strings u and right strings v." -/
theorem lemma_8 {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L) :
    Mult a b w = ∑ u, ∑ v, (∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)) * a u * b v := by
  -- "the coefficient of a[u] b[v] in (2) is ∑_τ ∏_ℓ φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ), summed over the
  -- leaves τ contributing to w": expand `Φ_τ(a) Ψ_τ(b)` and sum over `τ` last.
  simp only [Mult, Phi, Psi, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_gamma_eq_sum_contributes, sum_mul, sum_mul]
  exact sum_congr rfl fun τ _ => by ring




/-! ### The sizes of the matrices, and Figure 4 -/

/-! ### The input arrays -/

/-- The entry of the left input array at the string with inner set `Q`, outer part `r` and inner
part `π` is `X_Q[r, π]`. -/
@[simp]
theorem arrayL_leftStrOf {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (r : OuterStr L m) (π : InnerStr m) :
    arrayL m X (leftStrOf Q hQ r π) = X Q r π := by
  have h : (innerSetL (leftStrOf Q hQ r π)).card = m := by rw [innerSetL_leftStrOf, hQ]
  rw [arrayL, dif_pos h, outerPartL_leftStrOf, innerPartL_leftStrOf, innerSetL_leftStrOf]

/-- The entry of the right input array at the string with inner set `Q`, inner part `π` and outer
part `c` is `Y_Q[π, c]`. -/
@[simp]
theorem arrayR_rightStrOf {L m : ℕ} (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (π : InnerStr m) (c : OuterStr L m) :
    arrayR m Y (rightStrOf Q hQ π c) = Y Q π c := by
  have h : (innerSetR (rightStrOf Q hQ π c)).card = m := by rw [innerSetR_rightStrOf, hQ]
  rw [arrayR, dif_pos h, innerPartR_rightStrOf, outerPartR_rightStrOf, innerSetR_rightStrOf]

/-! ### The proof of Lemma 9 -/

/-- In the proof of Lemma 9: "the only monomials of G + E that contain z₀ are the p_ij q_ij
z₀, with coefficient 1." Stated for `γ(s, t, z₀)`, which is the coefficient of `s t z₀` in `G + E`
by `gamma_eq_coeff`. -/
theorem gamma_z0 (s : LeftVar) (t : RightVar) :
    gamma s t .z0 = if ∃ i j, s = .p i j ∧ t = .q i j then 1 else 0 := by
  decide +revert

/-- In the proof of Lemma 9: "The only monomial of G + E that contains z_ij and no inner
variable is x_i y_j z_ij, with coefficient 1". Stated for `γ(x_i', y_j', z_ij)`, which is the
coefficient of `x_i' y_j' z_ij` in `G + E` by `gamma_eq_coeff`. -/
theorem gamma_x_y_z (i' j' i j : Fin 3) :
    gamma (.x i') (.y j') (.z i j) = if i' = i ∧ j' = j then 1 else 0 := by
  decide +revert

/-- The statement on `γ(x_i', y_j', z_ij)` as it is used: if `s` and `t` are outer and
`γ(s, t, z_ij) ≠ 0`, then `(s, t) = (x_i, y_j)`. -/
theorem eq_x_y_of_gamma_ne_zero {s : LeftVar} {t : RightVar} {i j : Fin 3}
    (hs : ¬ s.IsInner) (ht : ¬ t.IsInner) (h : gamma s t (.z i j) ≠ 0) : s = .x i ∧ t = .y j := by
  rcases s with i' | _
  · rcases t with j' | _
    · by_contra hne
      exact h ((gamma_x_y_z i' j' i j).trans
        (if_neg fun ⟨hi, hj⟩ => hne ⟨hi ▸ rfl, hj ▸ rfl⟩))
    · exact (ht trivial).elim
  · exact (hs trivial).elim

/-- The summands of Lemma 8 that can be nonzero. Let `w` be the output string with inner
set `Q`, row `r` and column `c`. If `γ(u_ℓ, v_ℓ, w_ℓ) ≠ 0` at every level and the inner sets of `u`
and `v` have `m` elements, then `u` has inner set `Q`, outer part `r` and some inner part `π`, and
`v` has inner set `Q`, outer part `c` and the inner part with the same indices. -/
theorem exists_of_summand_ne_zero {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) {u : LeftStr L} {v : RightStr L}
    (hγ : ∀ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ) ≠ 0) (hu : (innerSetL u).card = m)
    (hv : (innerSetR v).card = m) : ∃ π, u = leftStrOf Q hQ r π ∧ v = rightStrOf Q hQ π c := by
  simp only [outStrOf, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel] at hγ
  obtain ⟨hγin, hγout⟩ := hγ
  -- "at a level ℓ ∈ Q we have w_ℓ = z₀ […] So (u_ℓ, v_ℓ) = (p_ij, q_ij) for some i, j."
  have hin : ∀ k, ∃ ij : Fin 2 × Fin 2,
      u (innerLevel Q hQ k) = .p ij.1 ij.2 ∧ v (innerLevel Q hQ k) = .q ij.1 ij.2 := fun k => by
    by_contra hne
    exact hγin k ((gamma_z0 _ _).trans (if_neg fun ⟨i, j, h⟩ => hne ⟨(i, j), h⟩))
  choose π hπ using hin
  -- "Thus u and v have an inner variable at every level of Q, and their inner sets are therefore
  -- exactly Q."  So "u_ℓ and v_ℓ are outer" at the levels outside Q.
  have huQ : innerSetL u = Q :=
    filter_eq_of_forall_innerLevel Q hQ (fun k => by rw [(hπ k).1]; trivial) hu
  have hvQ : innerSetR v = Q :=
    filter_eq_of_forall_innerLevel Q hQ (fun k => by rw [(hπ k).2]; trivial) hv
  have huout := ((filter_eq_iff_forall_level Q hQ).mp huQ).2
  have hvout := ((filter_eq_iff_forall_level Q hQ).mp hvQ).2
  -- "at a level ℓ ∉ Q we have w_ℓ = z_ij for some i, j […] so (u_ℓ, v_ℓ) = (x_i, y_j)."
  have hout : ∀ k, u (outerLevel Q hQ k) = .x (r k) ∧ v (outerLevel Q hQ k) = .y (c k) :=
    fun k => eq_x_y_of_gamma_ne_zero (huout k) (hvout k) (hγout k)
  exact ⟨π, (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).1, fun k => (hout k).1⟩,
    (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).2, fun k => (hout k).2⟩⟩

/-- In the proof of Lemma 9: the coefficient of the summand of `π` "is 1". -/
theorem prod_gamma_eq_one {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) (π : InnerStr m) :
    ∏ ℓ, gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
  have hone : ∀ ℓ,
      gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
    simp only [forall_level_iff Q hQ, leftStrOf, rightStrOf, outStrOf, glue_innerLevel,
      glue_outerLevel]
    exact ⟨fun _ => (gamma_z0 _ _).trans (if_pos ⟨_, _, rfl, rfl⟩),
      fun _ => (gamma_x_y_z _ _ _ _).trans (if_pos ⟨rfl, rfl⟩)⟩
  exact prod_eq_one fun ℓ _ => hone ℓ

/-- Lemma 9 for the output string with inner set `Q`, row `r` and column `c`: by Lemma 8 the entry
is a sum over all pairs `(u, v)`, and the summands that remain are those of the matrix product. -/
theorem Mult_arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Mult (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  -- To show: `∑_{(u,v)} ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) a[u] b[v] = ∑_π X_Q[r, π] Y_Q[π, c]`. The right-hand
  -- side is the part of the left-hand side over the pairs `(u, v)` that belong to some `π`.
  rw [lemma_8, Matrix.mul_apply, ← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_of_injective (fun π => (leftStrOf Q hQ r π, rightStrOf Q hQ π c)) ?_ _ _ ?_ ?_
  · -- "There is one such summand for each of the D strings π".
    exact fun π π' h => (leftStrOf_inj.mp (congrArg Prod.fst h)).2
  · -- Every other summand is zero.  "a[u] b[v] ≠ 0 requires the inner sets of u and v to have
    -- exactly m elements."
    rintro ⟨u, v⟩ hnot
    by_contra hne
    obtain ⟨⟨hγ, ha⟩, hb⟩ : ((∏ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ)) ≠ 0
        ∧ arrayL m X u ≠ 0) ∧ arrayR m Y v ≠ 0 := by
      simpa only [mul_ne_zero_iff] using hne
    obtain ⟨π, rfl, rfl⟩ := exists_of_summand_ne_zero Q hQ r c
      (fun ℓ => prod_ne_zero_iff.mp hγ ℓ (mem_univ ℓ))
      (by_contra fun h => ha (dif_neg h)) (by_contra fun h => hb (dif_neg h))
    exact hnot ⟨π, rfl⟩
  · -- The summand of `π` is `1 · X_Q[r, π] · Y_Q[π, c]`.
    intro π
    rw [prod_gamma_eq_one, one_mul, arrayL_leftStrOf, arrayR_rightStrOf]

/-- Section 2.3.3: "one run of Full […] computes all K of the products X_Q Y_Q." -/
theorem Full_arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Full L (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  rw [Lemma7.returns_Mult]
  exact Mult_arrays_eq_mul X Y Q hQ r c




/-! ### Section 2.4.1: the encodings -/

/-- Section 2.4.1, the procedure that computes the encoding of `a`: "we run Full with b left out and
without step (4): […] the left number at the leaf τ is Φ_τ(a), and the leaf stores it." What is left
of `Full` is step (2) for `a`, the recursive calls of step (3), and at depth `L` the number that has
been reached. "The encoding of b […] is computed in the same way", so the procedure is written once,
for the coefficients `c` of any family of linear forms: `c = φ` for `a`, and `c = ψ` for `b`. -/
def computeEncoding {α : Type} [Fintype α] (c : Term → α → ℤ) :
    (L : ℕ) → ((Fin L → α) → ℤ) → Leaf L → ℤ
  | 0, a, _ => a Fin.elim0
  | L + 1, a, τ => computeEncoding c L (fun u' => ∑ s, c (τ 0) s * sliceAt a s u') (Fin.tail τ)

/-- At the leaf `τ` the procedure of Section 2.4.1 stores `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`. -/
theorem computeEncoding_eq_encodeWith {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}
    (a : (Fin L → α) → ℤ) (τ : Leaf L) : computeEncoding c L a τ = encodeWith c τ a := by
  induction L with
  | zero => rw [computeEncoding, encodeWith_zero]
  | succ n ih => rw [computeEncoding, ih, ← encodeWith_cons, Fin.cons_self_tail]

/-- The procedure of Section 2.4.1 computes the encoding of `a`. -/
theorem computeEncoding_phi {L : ℕ} (a : LeftStr L → ℤ) : computeEncoding phi L a = encodingL a :=
  funext (computeEncoding_eq_encodeWith phi a)

/-- The procedure of Section 2.4.1 computes the encoding of `b`. -/
theorem computeEncoding_psi {L : ℕ} (b : RightStr L → ℤ) : computeEncoding psi L b = encodingR b :=
  funext (computeEncoding_eq_encodeWith psi b)

/-! ### Section 2.4.2: the sets `S_λ` of step (2) -/

/-! ### Lemma 10, first claim: the values -/

/-! ### Lemma 10, second claim: the calls that are made and the sets passed to them -/

/-! ### Lemma 10, third claim: the total size of the sets passed -/

end ThreeSumApsp
