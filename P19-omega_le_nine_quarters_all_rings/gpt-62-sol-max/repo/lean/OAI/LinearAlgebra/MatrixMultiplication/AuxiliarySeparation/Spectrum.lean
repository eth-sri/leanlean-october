module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth
public import Mathlib

public section

@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

noncomputable section

open Foundation TensorSemiring Filter
open scoped Topology NNReal

/-- An identity minor on the output leg forces quadratic rank. -/
theorem rank_lower {n r : ℕ} (h : matrixClass n ≤ (r : TensorClass)) : n ^ 2 ≤ r := by
  rcases n with _ | n
  · simp
  rw [← squareCoefficients_class, classOf_le_nat_iff_rankAtMost] at h
  obtain ⟨M, h⟩ := h
  rw [Tensor.restrict_diagonal] at h
  let j : Fin (n+1) := 0
  let L : Matrix (Fin (n+1) × Fin (n+1)) (Fin r) ℤ := fun i q => M.left (i.2,j) q * M.middle (j,i.1) q
  let R : Matrix (Fin r) (Fin (n+1) × Fin (n+1)) ℤ := fun q i => M.right i q
  have H : L * R = 1 := by
    ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [L, R, Tensor.squareCoefficients, Prod.ext_iff, eq_comm] using
      (congrArg (· (i.2,j) (j,i.1) k) h).symm
  simpa [H, pow_two] using (Matrix.rank_mul_le_left L R).trans L.rank_le_card_width

private def lowerRates : Set ℝ := {t | ∀ n r : ℕ, 0 < n →
  matrixClass n ≤ (r : TensorClass) → (n : ℝ)^t ≤ r}

/-- The lower bounds on the rates of all feasible blocks. -/
@[no_expose] def exactRankExponent : ℝ := sSup lowerRates

private theorem two_mem : 2 ∈ lowerRates := fun n _ hn h => by
  rw [Real.rpow_two]
  exact_mod_cast rank_lower h

private theorem lowerRates_bddAbove : BddAbove lowerRates := by
  obtain ⟨r, hr⟩ := exists_scalar_dominator (matrixClass 2)
  exact ⟨Real.logb 2 r, fun t ht => Real.le_logb_iff_rpow_le (by norm_num)
    (by positivity [rank_lower hr]) |>.mpr (by simpa using ht 2 r (by decide) hr)⟩

theorem exactRankExponent_lower : 2 ≤ exactRankExponent := le_csSup lowerRates_bddAbove two_mem

private theorem exactRankExponent_mem : exactRankExponent ∈ lowerRates := by
  have closed : IsClosed lowerRates := by
    simp only [lowerRates, Set.ofPred_forall]
    repeat apply isClosed_iInter; intro _
    exact isClosed_le (by fun_prop (disch := positivity)) continuous_const
  exact closed.csSup_mem ⟨2, two_mem⟩ lowerRates_bddAbove

theorem exists_near_optimal_block {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ n r : ℕ, 2 ≤ n ∧ matrixClass n ≤ (r : TensorClass) ∧ (r : ℝ) < (n : ℝ) ^ τ := by
  by_contra! h
  apply hτ.not_ge (le_csSup lowerRates_bddAbove ?_)
  intro n r hn hr
  rcases n with _ | _ | n
  · omega
  · simpa using Nat.cast_le (α := ℝ).mpr (rank_lower hr)
  exact h _ _ (by omega) hr

section

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S] [IsOrderedRing S] [IsBotZeroClass S]

private abbrev Cone := Submodule S (S × S)

private def baseCone : Cone (S := S) where
  carrier := {p | p.1 ≤ p.2}
  zero_mem' := le_rfl
  add_mem' := add_le_add
  smul_mem' s _ h := mul_le_mul_of_nonneg_left h (zero_le (a := s))

private abbrev Sound (P : Cone (S := S)) : Prop := ∀ c : S, (1+c,c) ∉ P

private abbrev extend (P : Cone (S := S)) (a b : S) :=
  P ⊔ Submodule.span S {(a,b)}

/-- Inconsistency of an extension witnesses a reversed scalar multiple. -/
private theorem certificate {P : Cone (S := S)} (hP : baseCone ≤ P) {a b : S}
    (h : ¬ Sound (extend P a b)) :
    ∃ c s : S, (1+c+s*b, c+s*a) ∈ P := by
  obtain ⟨c,h⟩ := not_forall.mp h
  obtain ⟨p,hp,q,hq,H⟩ := Submodule.mem_sup.mp (not_not.mp h)
  obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hq
  refine ⟨p.2, s, ?_⟩
  have hs : (s*a, s*a) ∈ baseCone := le_rfl
  convert P.add_mem hp (hP hs) using 1
  simp [Prod.ext_iff, smul_eq_mul, add_assoc] at H ⊢
  grind

private abbrev Saturated (P : Cone (S := S)) :=
  ∀ {a b c : S}, (a+c,b+c) ∈ P → (a,b) ∈ P

omit [PartialOrder S] [IsOrderedRing S] [IsBotZeroClass S] in
private theorem cone_trans {P : Cone (S := S)} (hsat : Saturated P) {a b c : S}
    (hab : (a,b) ∈ P) (hbc : (b,c) ∈ P) : (a,c) ∈ P :=
  hsat (c := b) (by simpa [add_comm c b] using P.add_mem hab hbc)

/-- Opposite certificates cannot coexist in a consistent cone. -/
private theorem totalCone {P₀ : Cone (S := S)} (h₀ : baseCone ≤ P₀) (hs₀ : Sound P₀) :
    ∃ P, P₀ ≤ P ∧ Sound P ∧ Saturated P ∧ ∀ a b, (a,b) ∈ P ∨ (b,a) ∈ P := by
  obtain ⟨P, hP, hm⟩ := zorn_le_nonempty₀ {P | Sound P} (by
    intro C hC hchain p hp
    refine ⟨sSup C, fun c h => ?_, fun q hq => le_sSup hq⟩
    obtain ⟨q,hq,h'⟩ := (Submodule.mem_sSup_of_directed ⟨p,hp⟩ hchain.directedOn).mp h
    exact hC hq c h') P₀ hs₀
  have hb := h₀.trans hP
  have bad {a b : S} (h : (a,b) ∉ P) : ¬Sound (extend P a b) := by
    intro hs
    exact h (hm.eq_of_le hs le_sup_left ▸ Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  -- A certificate of failure would still contradict soundness after adding
  -- the scaled comparison with a common summand.
  have hsat : Saturated P := by
    intro a b c hc
    by_contra h
    obtain ⟨d,s,hd⟩ := certificate hb (bad h)
    apply hm.prop (d+s*(a+b+c))
    convert P.add_mem hd (P.smul_mem s hc) using 1
    apply Prod.ext <;> dsimp [smul_eq_mul] <;> ring
  refine ⟨P, hP, hm.prop, hsat, fun a b => ?_⟩
  have cert {a b : S} (h : (a,b) ∉ P) : ∃ s, (1+s*b,s*a) ∈ P := by
    obtain ⟨c,s,H⟩ := certificate hb (bad h)
    exact ⟨s, hsat (c := c) (by convert H using 1; ac_rfl)⟩
  by_contra! hab
  obtain ⟨s,h₁⟩ := cert hab.1
  obtain ⟨t,h₂⟩ := cert hab.2
  have hst : (s+t,0) ∈ P := by
    apply hsat (c := s*t*(a+b))
    convert P.add_mem (P.smul_mem t h₁) (P.smul_mem s h₂) using 1
    apply Prod.ext <;> dsimp [smul_eq_mul] <;> ring
  have hs := cone_trans hsat (hb (le_add_of_nonneg_right (zero_le (a := t)))) hst
  exact hm.prop 0 (by simpa using (cone_trans hsat
    (hb (le_add_of_nonneg_right (zero_le (a := s*b))))
    (cone_trans hsat h₁ (by simpa [mul_comm] using P.smul_mem a hs))))

/-- Calibrate the total comparison against rational multiples of the unit.
The numerator of the approximant at denominator `n` is the largest integer
below `n • x`; the interval of uncertainty has width `1/n`. -/
private theorem realize_total (R : S → ℕ) (hR : ∀ x : S, x ≤ (R x : S))
    (P : Cone (S := S)) (hP : baseCone ≤ P) (hS : Sound P)
    (hsat : Saturated P) (ht : ∀ a b, (a,b) ∈ P ∨ (b,a) ∈ P) :
    ∃ f : S →+*o ℝ≥0, ∀ a b, (a,b) ∈ P → f a ≤ f b := by
  classical
  let r (a b : S) := (a,b) ∈ P
  have trans {a b c : S} (hab : r a b) (hbc : r b c) : r a c :=
    cone_trans hsat hab hbc
  have scale {a b : S} (h : r a b) (n : ℕ) : r (n • a) (n • b) := P.nsmul_mem h n
  have hnat {m n : ℕ} (h : r (m : S) (n : S)) : m ≤ n :=
    le_of_not_gt fun hh => hS n (trans (hP (show 1+(n : S) ≤ m by simpa [Nat.cast_succ, add_comm] using (Nat.mono_cast (α := S) hh))) h)
  let upper (x : S) : Set ℝ≥0 := {q | ∃ n m : ℕ, r (n.succ • x) (m : S) ∧ q = m/n.succ}
  let f (x : S) := sInf (upper x)
  have nonempty (x : S) : (upper x).Nonempty := ⟨R x,0,R x,by simpa using hP (hR x),by simp⟩
  have lo {x : S} {m n : ℕ} (h : r (m : S) (n.succ • x)) : (m : ℝ≥0) ≤ n.succ * f x := by
    apply (div_le_iff₀' (by positivity)).mp (le_csInf (nonempty x) ?_)
    rintro _ ⟨i,j,h',rfl⟩
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hh := trans (scale h i.succ) (by simpa only [smul_smul, mul_comm n.succ i.succ] using scale h' n.succ)
    have H : i.succ*m ≤ n.succ*j := hnat (by simpa [nsmul_eq_mul] using hh)
    simpa [mul_comm] using (Nat.cast_le (α := ℝ≥0)).mpr H
  have hi {x : S} {m n : ℕ} (h : r (n.succ • x) (m : S)) : n.succ * f x ≤ (m : ℝ≥0) :=
    (le_div_iff₀' (by positivity)).mp (csInf_le' ⟨n,m,h,rfl⟩)
  have hf {x y : S} (h : r x y) : f x ≤ f y :=
    csInf_le_csInf' (nonempty y) (by rintro _ ⟨n,m,H,rfl⟩; exact ⟨n,m,trans (scale h n.succ) H,rfl⟩)
  have bracket (x : S) : ∃ m : ℕ, r (m : S) x ∧ r x ((m+1 : ℕ) : S) := by
    let m := Nat.findGreatest (fun j => r (j : S) x) (R x)
    refine ⟨m, Nat.findGreatest_spec (P := fun j => r (j : S) x) (Nat.zero_le _) (by simpa using hP (zero_le (a := x))),
      ((ht _ _).resolve_right fun h => Nat.not_succ_le_self m ?_)⟩
    exact Nat.le_findGreatest (hnat (trans h (hP (hR x)))) h
  have eq_of_close {v w c : ℝ≥0} (h : ∀ n : ℕ, n.succ * v ≤ n.succ * w + c ∧ n.succ * w ≤ n.succ * v + c) : v = w :=
    NNReal.eq (le_antisymm (le_of_scaled_le fun n => by exact_mod_cast (h n).1)
      (le_of_scaled_le fun n => by exact_mod_cast (h n).2))
  have hadd (x y : S) : f (x+y) = f x + f y := by
    apply eq_of_close (c := 2)
    intro n
    obtain ⟨a,ha,ha'⟩ := bracket (n.succ • x)
    obtain ⟨b,hb,hb'⟩ := bracket (n.succ • y)
    have h₀ := lo (n := n) (x := x+y) (m := a+b) (by simpa [smul_add] using P.add_mem ha hb)
    have h₁ := hi (n := n) (x := x+y) (m := (a+1)+(b+1)) (by simpa [smul_add] using P.add_mem ha' hb')
    have := lo ha; have := lo hb; have := hi ha'; have := hi hb'
    push_cast [mul_add] at *
    constructor <;> linarith
  have f0 : f 0 = 0 := by simpa using (hadd 0 0).symm
  have f1 : f 1 = 1 := by
    have l := lo (x := 1) (n := 0) (m := 1) (by simpa using hP (le_refl (1 : S)))
    have u := hi (x := 1) (n := 0) (m := 1) (by simpa using hP (le_refl (1 : S)))
    simpa using le_antisymm u l
  let g : S →+ ℝ≥0 := ⟨⟨f, f0⟩, hadd⟩
  have fn (n : ℕ) (x : S) : f (n • x) = n * f x :=
    (map_nsmul g n x).trans (nsmul_eq_mul ..)
  have hmul (x y : S) : f (x*y) = f x * f y := by
    apply eq_of_close (c := f x)
    intro n
    obtain ⟨m,hm,hm'⟩ := bracket (n.succ • y)
    have L {a b : S} (h : r a b) : f (x*a) ≤ f (x*b) := hf (P.smul_mem x h)
    have h₀ := L hm
    have h₁ := L hm'
    simp only [mul_smul_comm, ← nsmul_eq_mul', fn] at h₀ h₁
    have := mul_le_mul_of_nonneg_right (a := f x) (lo hm) zero_le
    have := mul_le_mul_of_nonneg_right (a := f x) (hi hm') zero_le
    push_cast at *
    constructor <;> linarith
  exact ⟨⟨{g with map_one' := f1, map_mul' := hmul}, fun _ _ h => hf (hP h)⟩,
    fun _ _ h => hf h⟩

/-- A consistent detector inequality extends to a real-valued character. -/
theorem exists_character_of_no_catalyst (R : S → ℕ) (d k : S)
    (hR : ∀ a : S, a ≤ (R a : S))
    (hno : ∀ c s : S, ¬c + 1 + d*s ≤ c + k*s) :
    ∃ χ : S →+*o ℝ≥0, χ k ≤ χ d := by
  have hs : Sound (extend baseCone k d) := by
    by_contra hh
    obtain ⟨c,s,h⟩ := certificate (P := baseCone) le_rfl hh
    exact hno c s (by simpa [baseCone, add_comm c 1, mul_comm s] using h)
  obtain ⟨P, hP, hn, hsat, ht⟩ := totalCone (P₀ := extend baseCone k d) le_sup_left hs
  obtain ⟨χ, hχ⟩ := realize_total R hR P (le_sup_left.trans hP) hn hsat ht
  exact ⟨χ, hχ _ _ (hP (Submodule.mem_sup_right (Submodule.subset_span (by simp))))⟩

end

/-- At fixed `n` and exponent slack, compare the rank budget with powers of
one near-optimal block. The integer logarithm finds the largest power that fits. -/
private theorem catalytic_rank_bound_at_slack {d n budget R : ℕ}
    (hd : 0 < d) (hn : 1 ≤ n)
    (hbound : ∀ j : ℕ, ((n : TensorClass) * matrixClass d)^j ≤ (R : TensorClass) * (budget : TensorClass)^j)
    {δ : ℝ} (hδ : 0 < δ) :
    (d : ℝ) ^ exactRankExponent * (n : ℝ) ^ (exactRankExponent / (exactRankExponent + δ)) ≤ budget := by
  let ν := exactRankExponent
  let τ := ν + δ
  have hν : 0 ≤ ν := by linarith [exactRankExponent_lower]
  have hτ : 0 < τ := add_pos_of_nonneg_of_pos hν hδ
  obtain ⟨u, r, hu, hr, huR⟩ := exists_near_optimal_block (lt_add_of_pos_right ν hδ)
  have hur : 1 < r := by nlinarith [rank_lower hr]
  apply le_of_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * R) (Nat.cast_nonneg budget)
  intro j
  let l := Nat.log r (n ^ j)
  have hblock : matrixClass (u^l) ≤ (n : TensorClass)^j := by
    rw [map_pow, ← Nat.cast_pow]
    refine (pow_le_pow_left₀ zero_le hr l).trans ?_
    rw [← Nat.cast_pow]
    exact Nat.mono_cast (Nat.pow_log_le_self r (pow_ne_zero j (by omega : n ≠ 0)))
  have hrank : matrixClass (d^j*u^l) ≤ (↑(R * budget^j : ℕ) : TensorClass) := by
    push_cast
    rw [map_mul (matrixClass), map_pow]
    refine (mul_mono (le_refl (matrixClass d ^ j)) hblock).trans ?_
    simpa only [mul_pow, mul_comm] using hbound j
  have hsize : (n : ℝ) ^ j ≤ ((u : ℝ) ^ (l + 1)) ^ τ := by
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg u)]
    exact (by exact_mod_cast (Nat.lt_pow_succ_log_self hur (n ^ j)).le : (n : ℝ) ^ j ≤ (r : ℝ) ^ (l+1)).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg r) huR.le _)
  have hx := Real.rpow_le_rpow (by positivity) hsize (div_nonneg hν hτ.le)
  rw [← Real.rpow_mul (by positivity), show τ * (ν / τ) = ν by field_simp] at hx
  rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), Real.rpow_pow_comm (Nat.cast_nonneg n)]
  calc
    _ ≤ ((d : ℝ)^j)^ν * ((u : ℝ)^(l+1))^ν := by gcongr
    _ = (u : ℝ)^ν * (↑(d^j*u^l : ℕ) : ℝ)^ν := by
      simp (discharger := positivity) only [Nat.cast_mul, Nat.cast_pow, pow_succ' (u : ℝ), Real.mul_rpow]
      ring
    _ ≤ _ := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left (exactRankExponent_mem _ _ (by positivity) hrank) (by positivity : 0 ≤ (u : ℝ)^ν)

@[to_additive]
private theorem repeat_mul_le {M : Type*} [CommMonoid M] [Preorder M] [MulRightMono M]
    {D a b : M} (h : D * a ≤ D * b) (n : ℕ) : D * a^n ≤ D * b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ D * (b * a^n) := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_left h (a^n)
      _ ≤ _ := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_left ih b

/-- A fixed catalyst cannot make `k` copies dominate multiplication by `T_d`
unless `k ≥ d^ν`. No tensor factor is cancelled in the comparison. -/
theorem tensor_catalytic_obstruction_of_one_le
    {D s : TensorClass} {d k : ℕ} (hd : 0 < d) (hs : 1 ≤ s)
    (hcat : D + matrixClass d * s ≤ D + (k : TensorClass) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  obtain ⟨q,hq⟩ := exists_scalar_dominator D
  obtain ⟨R,hR⟩ := exists_scalar_dominator s
  apply le_of_scaled_le (C := q)
  intro j
  let n := j.succ
  let ν := exactRankExponent
  have hν : 0 < ν := by linarith [exactRankExponent_lower]
  have hc : ContinuousAt (fun δ : ℝ => (d : ℝ)^ν * (n : ℝ)^(ν / (ν + δ))) 0 := by
    fun_prop (disch := positivity)
  simpa [hν.ne', n, mul_comm ((d : ℝ)^ν)] using le_of_tendsto hc.continuousWithinAt
    ((show ∀ᶠ δ in 𝓝[Set.Ioi 0] (0 : ℝ), 0 < δ from self_mem_nhdsWithin).mono fun δ hδ => by
      rw [← Nat.cast_succ, ← Nat.cast_mul, ← Nat.cast_add]
      refine catalytic_rank_bound_at_slack hd j.succ_pos (R := R) (fun l => ?_) hδ
      have insert (x : TensorClass) : x ≤ s * x := by simpa using mul_mono hs (le_refl x)
      have H := (le_add_of_nonneg_left (show 0 ≤ D from zero_le)).trans
        ((repeat_add_le hcat n).trans (add_mono (hq.trans (insert _)) le_rfl))
      have hm : s * ((n : TensorClass) * matrixClass d) ≤ s * (↑(n*k+q : ℕ) : TensorClass) := by
        simpa [nsmul_eq_mul, mul_add, add_comm, mul_assoc, mul_left_comm, mul_comm] using H
      let : MulRightMono TensorClass := ⟨fun _ _ _ h => mul_mono h le_rfl⟩
      exact (insert _).trans ((repeat_mul_le hm l).trans (mul_mono hR le_rfl)))

/-- A strict additive gain lets us insert a unit on the multiplier leg. -/
private theorem not_catalytic_scalar_gain {D s : TensorClass} {d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ¬ D + 1 + matrixClass d * s ≤ D + (k : TensorClass) * s := by
  intro hc
  obtain ⟨q,hq⟩ := exists_scalar_dominator (matrixClass d)
  apply hk.not_ge (tensor_catalytic_obstruction_of_one_le (D := D) hd
    (s := 1 + q • s) (le_add_of_nonneg_right zero_le) ?_)
  calc
    _ ≤ D + q • (1 + matrixClass d * s) := by
      simp only [mul_add, mul_one, nsmul_add, mul_smul_comm, nsmul_one]
      gcongr
    _ ≤ D + q • ((k : TensorClass) * s) := repeat_add_le (by simpa [add_assoc] using hc) q
    _ ≤ _ := by
      simp only [mul_add, mul_one, mul_smul_comm]
      gcongr
      exact le_add_of_nonneg_left zero_le

/-- Characters detect every integer strictly below the exact-rank growth value. -/
theorem exists_detecting_character {d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ∃ χ : Character, (k : ℝ≥0) ≤ χ (matrixClass d) := by
  choose R hR using exists_scalar_dominator
  obtain ⟨χ, hχ⟩ := exists_character_of_no_catalyst R (matrixClass d) k hR
    (fun _ _ => not_catalytic_scalar_gain hd hk)
  aesop

end
end OAI.MatrixMultiplication.AuxiliarySeparation
