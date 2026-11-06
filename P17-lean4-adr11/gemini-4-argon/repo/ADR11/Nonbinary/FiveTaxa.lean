module

public import ADR11.Rootings.Proofs
public import ADR11.Trees.Classify

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem exp_bds {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (A : Finset (Fin 5))
    (hA : A ∈ H ∧ A ≠ univ := by decide) :
    0 < exp (-τ.length A) ∧ exp (-τ.length A) < 1 :=
  ⟨exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 (τ.length_pos A (h ▸ hA.1) hA.2))⟩

private theorem five_length_eq {x y : ℝ} (A B : ℝ) (n : ℕ) (hn : n ≠ 0) (hA : A ≠ 0)
    (h : A * exp (-x) ^ n + B = A * exp (-y) ^ n + B) : x = y := by
  have h1 : exp (-x) ^ n = exp (-y) ^ n := mul_left_cancel₀ hA (by linarith)
  have h2 := Real.exp_injective ((pow_left_inj₀ (exp_pos _).le (exp_pos _).le hn).1 h1)
  linarith

private theorem five_same_of_lengths {τ τ' : SpeciesTree (Fin 5)} {C : Finset (Finset (Fin 5))}
    (h : τ.clusters = hierarchyOf C) (h' : τ'.clusters = hierarchyOf C)
    (hl : ∀ A ∈ C, τ.length A = τ'.length A) : τ.SameRootedMetricTree τ' := by
  refine ⟨h.trans h'.symm, fun A hA h2 hu => hl A ?_⟩
  rw [h] at hA
  rcases mem_insert.1 hA with rfl | hA
  · exact absurd rfl hu
  rcases mem_union.1 hA with hA | hA
  · exact hA
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hA; simp at h2

private theorem ulen_mem {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (S A : Finset (Fin 5))
    (hA : H.filter (fun C => C ≠ univ ∧ (C = S ∨ C = Sᶜ)) = {A} := by decide) :
    τ.unrootedLength S = τ.length A := by
  unfold SpeciesTree.unrootedLength; rw [h, hA, sum_singleton]

private theorem ulen_one {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (S : Finset (Fin 5)) (a : ℕ)
    (ha : H.filter (fun C => C ≠ univ ∧ (C = S ∨ C = Sᶜ)) = {decC 5 a} := by decide +kernel) :
    exp (-τ.unrootedLength S) = exp (-τ.length (decC 5 a)) ∧
      exp (-τ.unrootedLength S) = monoVal τ.length [(a, 1)] := by
  have e := ulen_mem h S (decC 5 a) ha
  exact ⟨by rw [e], by simp [e, monoVal_cons, monoVal_nil]⟩

private theorem ulen_both {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (S A B : Finset (Fin 5))
    (hST : A ≠ B ∧ H.filter (fun C => C ≠ univ ∧ (C = S ∨ C = Sᶜ)) = {A, B} := by decide) :
    τ.unrootedLength S = τ.length A + τ.length B ∧
      exp (-τ.unrootedLength S) = exp (-τ.length A) * exp (-τ.length B) := by
  have e : τ.unrootedLength S = τ.length A + τ.length B := by
    unfold SpeciesTree.unrootedLength; rw [h, hST.2, sum_pair hST.1]
  exact ⟨e, by rw [e, neg_add, exp_add]⟩

private abbrev IsNR (H : Finset (Finset (Fin 5))) (A : Finset (Fin 5)) : Prop :=
  A ∈ H ∧ A ≠ univ ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ ∧
    H.filter (fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) = {A}

private theorem len_nr {τ τ' : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    {A : Finset (Fin 5)} (hA : IsNR H A := by decide) :
    τ.length A = τ'.length A := by
  rw [← ulen_mem hτ A A hA.2.2.2.2, ← ulen_mem hτ' A A hA.2.2.2.2]
  exact hU.2 A (mem_unroot.2 (Or.inl ⟨hτ ▸ hA.1, hA.2.1⟩))
    hA.2.2.1 hA.2.2.2.1

private theorem monoVal_eq_of_nr {τ τ' : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    (m : List (ℕ × ℕ)) (hm : ∀ p ∈ m, IsNR H (decC 5 p.1) := by decide +kernel) :
    monoVal τ.length m = monoVal τ'.length m := by
  unfold monoVal
  congr 1
  exact List.map_congr_left fun p hp => by rw [len_nr hτ hτ' hU (hm p hp)]

private theorem five_u_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) (i : ℕ) : u τ i = u τ' i := by
  unfold u; rw [h]

private theorem eval_lo_hi_bds {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (m : List (ℕ × ℕ)) (c : ℕ)
    (hc : decC 5 c ∈ H ∧ decC 5 c ≠ univ := by decide +kernel) :
    evalPoly τ.length (loP m c) < 1 / 15 * monoVal τ.length m ∧
      1 / 15 * monoVal τ.length m < evalPoly τ.length (hiP m c) := by
  simp only [loP, hiP, evalPoly_cons, evalPoly_nil, monoVal_append, monoVal_cons, monoVal_nil]
  push_cast
  obtain ⟨h0, h1⟩ := exp_bds h (decC 5 c) hc
  have : 0 < monoVal τ.length m * (1 - exp (-τ.length (decC 5 c)) ^ 6) :=
    mul_pos (monoVal_pos _ _) (sub_pos.2 (pow_lt_one₀ h0.le h1 (by norm_num)))
  exact ⟨by linarith, by linarith⟩

private theorem solve_loP {τ τ' : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (h' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    (i : ℕ) (m : List (ℕ × ℕ)) (c : ℕ)
    {C : Finset (Fin 5)} (hui : u τ i = u τ' i)
    (hm : ∀ p ∈ m, IsNR H (decC 5 p.1) := by decide +kernel)
    (hi : decF 5 (root_T5code i) = T5 i := by decide +kernel)
    (hc : decC 5 c = C := by decide +kernel)
    (hwf : wfCsB 5 H (c :: m.map Prod.fst) = true := by decide +kernel)
    (hcert : root_certsB 5 (unrootedL 5 (c :: m.map Prod.fst))
      [(root_T5code i, loP m c)] = true := by decide +kernel) :
    τ.length C = τ'.length C := by
  have f : u τ i = _ := (root_unrootedDist_eq_evalPoly τ h _ hwf hcert List.mem_cons_self hi).trans
    (eval_loP τ.length m c)
  have f' : u τ' i = _ := (root_unrootedDist_eq_evalPoly τ' h' _ hwf hcert List.mem_cons_self hi).trans
    (eval_loP τ'.length m c)
  have hm' := monoVal_eq_of_nr h h' hU m hm
  rw [← hc]
  exact five_length_eq (1 / 90 * monoVal τ'.length m) (1 / 18 * monoVal τ'.length m) 6
    (by norm_num) (by have := monoVal_pos τ'.length m; positivity)
    (by rw [← hm', ← f, hui, f', hm'])

private theorem solve_bal {τ τ' : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (h' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    (j : ℕ) (m : List (ℕ × ℕ))
    (z b : ℕ) {A B : Finset (Fin 5)} (huj : u τ j = u τ' j)
    (hz : decC 5 z = A := by decide +kernel) (hb : decC 5 b = B := by decide +kernel)
    (hAB : (A ≠ B ∧ H.filter (fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) = {A, B}) ∧
      A ∈ H ∧ A ≠ univ ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ := by decide)
    (hm : ∀ p ∈ m, IsNR H (decC 5 p.1) := by decide +kernel)
    (hj : decF 5 (root_T5code j) = T5 j := by decide +kernel)
    (hwf : wfCsB 5 H (z :: b :: m.map Prod.fst) = true := by decide +kernel)
    (hcert : root_certsB 5 (unrootedL 5 (z :: b :: m.map Prod.fst))
      [(root_T5code j, constP ([(z, 1)] ++ m ++ [(b, 3)]))] = true := by decide +kernel) :
    τ.length A = τ'.length A ∧ τ.length B = τ'.length B := by
  have e1 := ulen_both h A A B hAB.1
  have e1' := ulen_both h' A A B hAB.1
  have hUA : τ.unrootedLength A = τ'.unrootedLength A :=
    hU.2 A (mem_unroot.2 (Or.inl ⟨h ▸ hAB.2.1, hAB.2.2.1⟩)) hAB.2.2.2.1 hAB.2.2.2.2
  have hm' := monoVal_eq_of_nr h h' hU m hm
  have f : u τ j = _ := (root_unrootedDist_eq_evalPoly τ h _ hwf hcert List.mem_cons_self hj).trans
    (eval_constP τ.length _)
  have f' : u τ' j = _ := (root_unrootedDist_eq_evalPoly τ' h' _ hwf hcert List.mem_cons_self hj).trans
    (eval_constP τ'.length _)
  simp only [monoVal_append, monoVal_cons, monoVal_nil, pow_one, mul_one, hz, hb] at f f'
  have hW : 0 < monoVal τ'.length m := monoVal_pos _ _
  have hy : τ.length B = τ'.length B :=
    five_length_eq (1 / 15 * monoVal τ'.length m * exp (-τ'.unrootedLength A)) 0 2
      (by norm_num) (by positivity)
      (by
        have k1 : u τ j = 1 / 15 * monoVal τ'.length m * exp (-τ'.unrootedLength A) *
            exp (-τ.length B) ^ 2 + 0 := by rw [f, hm', ← hUA, e1.2]; ring
        have k2 : u τ' j = 1 / 15 * monoVal τ'.length m * exp (-τ'.unrootedLength A) *
            exp (-τ'.length B) ^ 2 + 0 := by rw [f', e1'.2]; ring
        linarith)
  exact ⟨by linarith [e1.1, e1'.1], hy⟩

noncomputable def branch2 (u₅ u₇ U₁ U₂ : ℝ) (H₁ H₂ H₃ H₄ : Finset (Finset (Fin 5))) :
    Finset (Finset (Fin 5)) :=
  if 1 / 15 * U₁ * U₂ ^ 3 < u₇ then H₁
  else if u₇ = 1 / 15 * U₁ * U₂ ^ 3 then H₂
  else if u₅ - u₇ = 1 / 6 * U₁ * U₂ - 1 / 6 * U₁ * U₂ ^ 3 then H₃
  else H₄

private theorem b2_bal {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (i j : ℕ) (m : List (ℕ × ℕ)) (z b : ℕ) (S : Finset (Fin 5)) {U₁ : ℝ}
    (hU₁ : U₁ = monoVal τ.length m)
    (hS : decC 5 z ≠ decC 5 b ∧
      H.filter (fun C => C ≠ univ ∧ (C = S ∨ C = Sᶜ)) = {decC 5 z, decC 5 b} := by decide +kernel)
    (hi : decF 5 (root_T5code i) = T5 i := by decide +kernel)
    (hj : decF 5 (root_T5code j) = T5 j := by decide +kernel)
    (hz : decC 5 z ∈ H ∧ decC 5 z ≠ univ := by decide +kernel)
    (hb : decC 5 b ∈ H ∧ decC 5 b ≠ univ := by decide +kernel)
    (hwf : wfCsB 5 H (z :: b :: m.map Prod.fst) = true := by decide +kernel)
    (hc : root_certsB 5 (unrootedL 5 (z :: b :: m.map Prod.fst))
      [(root_T5code i, p6Hi ([(z, 1)] ++ m) b),
       (root_T5code j, constP ([(z, 1)] ++ m ++ [(b, 3)]))] = true := by decide +kernel)
    {H₁ H₂ H₃ H₄ : Finset (Finset (Fin 5))} :
    u τ j < u τ i ∧
      branch2 (u τ i) (u τ j) U₁ (exp (-τ.unrootedLength S)) H₁ H₂ H₃ H₄ = H₁ := by
  obtain ⟨hi', hj'⟩ := root_u5_pair τ h _ i j _ _ hi hj hwf hc
  obtain ⟨z0, z1⟩ := exp_bds h (decC 5 z) hz
  obtain ⟨y0, y1⟩ := exp_bds h (decC 5 b) hb
  have hX := monoVal_pos τ.length m
  have hY2 : exp (-τ.length (decC 5 b)) ^ 2 < 1 := pow_lt_one₀ y0.le y1 (by norm_num)
  have hZ2 : exp (-τ.length (decC 5 z)) ^ 2 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have k1 : 0 < monoVal τ.length m * exp (-τ.length (decC 5 z)) * exp (-τ.length (decC 5 b)) *
      (1 - exp (-τ.length (decC 5 b)) ^ 2) :=
    mul_pos (mul_pos (mul_pos hX z0) y0) (by linarith)
  have k2 : 0 < monoVal τ.length m * exp (-τ.length (decC 5 z)) * exp (-τ.length (decC 5 b)) ^ 3 *
      (1 - exp (-τ.length (decC 5 z)) ^ 2) :=
    mul_pos (mul_pos (mul_pos hX z0) (pow_pos y0 3)) (by linarith)
  have hU₂' : exp (-τ.unrootedLength S) ^ 3 =
      exp (-τ.length (decC 5 b)) ^ 3 * exp (-τ.length (decC 5 z)) ^ 3 := by
    rw [(ulen_both h S (decC 5 z) (decC 5 b) hS).2]; ring
  simp only [p6Hi, constP, evalPoly_cons, evalPoly_nil, monoVal_append, monoVal_cons,
    monoVal_nil] at hi' hj'
  push_cast at hi' hj'
  exact ⟨by linarith, by unfold branch2; rw [ite_eq_left (by rw [hU₁, hU₂', hj']; linarith)]⟩

private theorem b2_p6 {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (i j : ℕ) (m : List (ℕ × ℕ)) (b : ℕ) (S : Finset (Fin 5)) {U₁ : ℝ}
    (hU₁ : U₁ = monoVal τ.length m)
    (hS : H.filter (fun C => C ≠ univ ∧ (C = S ∨ C = Sᶜ)) = {decC 5 b} := by decide +kernel)
    (hi : decF 5 (root_T5code i) = T5 i := by decide +kernel)
    (hj : decF 5 (root_T5code j) = T5 j := by decide +kernel)
    (hb : decC 5 b ∈ H ∧ decC 5 b ≠ univ := by decide +kernel)
    (hwf : wfCsB 5 H (b :: m.map Prod.fst) = true := by decide +kernel)
    (hc : root_certsB 5 (unrootedL 5 (b :: m.map Prod.fst))
      [(root_T5code i, p6Hi m b),
       (root_T5code j, constP (m ++ [(b, 3)]))] = true := by decide +kernel)
    {H₁ H₂ H₃ H₄ : Finset (Finset (Fin 5))} :
    u τ j < u τ i ∧
      branch2 (u τ i) (u τ j) U₁ (exp (-τ.unrootedLength S)) H₁ H₂ H₃ H₄ = H₂ := by
  obtain ⟨hi', hj'⟩ := root_u5_pair τ h _ i j _ _ hi hj hwf hc
  obtain ⟨y0, y1⟩ := exp_bds h (decC 5 b) hb
  have hY2 : exp (-τ.length (decC 5 b)) ^ 2 < 1 := pow_lt_one₀ y0.le y1 (by norm_num)
  have k1 : 0 < monoVal τ.length m * exp (-τ.length (decC 5 b)) *
      (1 - exp (-τ.length (decC 5 b)) ^ 2) :=
    mul_pos (mul_pos (monoVal_pos _ _) y0) (by linarith)
  simp only [p6Hi, constP, evalPoly_cons, evalPoly_nil, monoVal_append, monoVal_cons,
    monoVal_nil] at hi' hj'
  push_cast at hi' hj'
  have heq : u τ j = 1 / 15 * U₁ * exp (-τ.unrootedLength S) ^ 3 := by
    rw [hU₁, (ulen_one h S b hS).1, hj']; ring
  exact ⟨by linarith, by unfold branch2; rw [ite_eq_right (by linarith), ite_eq_left heq]⟩

private theorem b2_cat (cat1 : Bool) {τ : SpeciesTree (Fin 5)} {H : Finset (Finset (Fin 5))}
    (h : τ.clusters = H) (i j : ℕ) (m : List (ℕ × ℕ)) (b c : ℕ) (S : Finset (Fin 5)) {U₁ : ℝ}
    (hU₁ : U₁ = monoVal τ.length m)
    (hS : H.filter (fun C => C ≠ univ ∧ (C = S ∨ C = Sᶜ)) = {decC 5 b} := by decide +kernel)
    (hi : decF 5 (root_T5code i) = T5 i := by decide +kernel)
    (hj : decF 5 (root_T5code j) = T5 j := by decide +kernel)
    (hb : decC 5 b ∈ H ∧ decC 5 b ≠ univ := by decide +kernel)
    (hc : decC 5 c ∈ H ∧ decC 5 c ≠ univ := by decide +kernel)
    (hwf : wfCsB 5 H (b :: c :: m.map Prod.fst) = true := by decide +kernel)
    (hcert : root_certsB 5 (unrootedL 5 (b :: c :: m.map Prod.fst))
      [(root_T5code i, if cat1 then cat1Hi m b c else cat0Hi m b c),
       (root_T5code j, loP (m ++ [(b, 3)]) c)] = true := by decide +kernel)
    {H₁ H₂ H₃ H₄ : Finset (Finset (Fin 5))} :
    u τ j < u τ i ∧
      branch2 (u τ i) (u τ j) U₁ (exp (-τ.unrootedLength S)) H₁ H₂ H₃ H₄ =
        if cat1 then H₄ else H₃ := by
  obtain ⟨hi', hj'⟩ := root_u5_pair τ h _ i j _ _ hi hj hwf hcert
  obtain ⟨y0, y1⟩ := exp_bds h (decC 5 b) hb
  obtain ⟨z0, z1⟩ := exp_bds h (decC 5 c) hc
  have hU₂ := (ulen_one h S b hS).1
  have hY2 : exp (-τ.length (decC 5 b)) ^ 2 < 1 := pow_lt_one₀ y0.le y1 (by norm_num)
  have hZ6 : exp (-τ.length (decC 5 c)) ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have k1 : 0 < monoVal τ.length m * exp (-τ.length (decC 5 b)) *
      (1 - exp (-τ.length (decC 5 b)) ^ 2) :=
    mul_pos (mul_pos (monoVal_pos _ _) y0) (by linarith)
  have k2 : 0 < monoVal τ.length m * exp (-τ.length (decC 5 b)) ^ 3 *
      (1 - exp (-τ.length (decC 5 c)) ^ 6) :=
    mul_pos (mul_pos (monoVal_pos _ _) (pow_pos y0 3)) (by linarith)
  simp only [loP, evalPoly_cons, evalPoly_nil, monoVal_append, monoVal_cons, monoVal_nil,
    mul_one, add_zero] at hj'
  push_cast at hj'
  have hlt : u τ j < 1 / 15 * U₁ * exp (-τ.unrootedLength S) ^ 3 := by
    rw [hU₁, hU₂, hj']; linarith
  unfold branch2
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith)]
  cases cat1 <;>
    (simp only [Bool.false_eq_true, ↓reduceIte, cat0Hi, cat1Hi, evalPoly_cons, evalPoly_nil,
       monoVal_append, monoVal_cons, monoVal_nil, pow_one, mul_one, add_zero] at hi'
     push_cast at hi')
  · exact ⟨by linarith, ite_eq_left (by rw [hU₁, hU₂, hi', hj']; ring)⟩
  · exact ⟨by linarith, ite_eq_right (by rw [hU₁, hU₂] at *; linarith)⟩

/-! ### `U5 0` -/

noncomputable def cls0 (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  if u τ 5 = 1 / 15 then hierarchyOf ∅
  else if 1 / 15 < u τ 5 then hierarchyOf {{0, 1, 2, 4}}
  else if 1 / 15 < u τ 6 then hierarchyOf {{0, 1, 2, 3}}
  else if 1 / 15 < u τ 4 then hierarchyOf {{0, 2, 3, 4}}
  else if 1 / 15 < u τ 1 then hierarchyOf {{0, 1, 3, 4}}
  else hierarchyOf {{1, 2, 3, 4}}

private theorem cls0_eq (τ : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 0) :
    cls0 τ = τ.clusters := by
  have hR := classify_mem_rootings5 τ 0 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  unfold cls0
  rcases hR with h | h | h | h | h | h
  · obtain ⟨h5, _⟩ := root_u5_pair τ h [] 5 6 (constP []) (constP [])
    rw [h, h5, eval_constP, monoVal_nil, mul_one, ite_eq_left rfl]
  · obtain ⟨h1, h4, h5, h6⟩ := root_u5_1456 τ h [30]
      (loP [] 30) (loP [] 30) (loP [] 30) (loP [] 30)
    have hlt := (eval_lo_hi_bds h [] 30).1; simp only [monoVal_nil, mul_one] at hlt
    rw [h, h1, h4, h5, h6, ite_eq_right (by linarith), ite_eq_right (by linarith),
      ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (by linarith)]
  · obtain ⟨h1, h4, h5, h6⟩ := root_u5_1456 τ h [29]
      (loP [] 29) (hiP [] 29) (loP [] 29) (loP [] 29)
    obtain ⟨hlt, hgt⟩ := eval_lo_hi_bds h [] 29
    simp only [monoVal_nil, mul_one] at hlt hgt
    rw [h, h1, h4, h5, h6, ite_eq_right (by linarith), ite_eq_right (by linarith),
      ite_eq_right (by linarith), ite_eq_left (by linarith)]
  · obtain ⟨h1, h4, h5, h6⟩ := root_u5_1456 τ h [27]
      (hiP [] 27) (loP [] 27) (loP [] 27) (loP [] 27)
    obtain ⟨hlt, hgt⟩ := eval_lo_hi_bds h [] 27
    simp only [monoVal_nil, mul_one] at hlt hgt
    rw [h, h1, h4, h5, h6, ite_eq_right (by linarith), ite_eq_right (by linarith),
      ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_left (by linarith)]
  · obtain ⟨h5, _⟩ := root_u5_pair τ h [23] 5 6 (hiP [] 23) (loP [] 23)
    have hgt := (eval_lo_hi_bds h [] 23).2; simp only [monoVal_nil, mul_one] at hgt
    rw [h, h5, ite_eq_right (by linarith), ite_eq_left (by linarith)]
  · obtain ⟨h5, h6⟩ := root_u5_pair τ h [15] 5 6 (loP [] 15) (hiP [] 15)
    obtain ⟨hlt, hgt⟩ := eval_lo_hi_bds h [] 15
    simp only [monoVal_nil, mul_one] at hlt hgt
    rw [h, h5, h6, ite_eq_right (by linarith), ite_eq_right (by linarith),
      ite_eq_left (by linarith)]

/-! ### `U5 1` -/

noncomputable def cls1 (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  let U := exp (-τ.unrootedLength {0, 1})
  if u τ 5 < u τ 4 then
    branch2 (u τ 4) (u τ 5) 1 U
      (hierarchyOf {{0, 1}, {2, 3, 4}})
      (hierarchyOf {{2, 3, 4}})
      (hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}})
      (hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}})
  else if u τ 4 < u τ 5 then hierarchyOf {{0, 1}, {0, 1, 2, 4}}
  else if u τ 5 = 1 / 15 * U then hierarchyOf {{0, 1}}
  else if u τ 5 < u τ 6 then hierarchyOf {{0, 1}, {0, 1, 2, 3}}
  else hierarchyOf {{0, 1}, {0, 1, 3, 4}}

private theorem cls1_eq (τ : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 1) :
    cls1 τ = τ.clusters := by
  have hR := classify_mem_rootings5 τ 1 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  unfold cls1
  rcases hR with h | h | h | h | h | h | h | h
  · obtain ⟨h4, h5⟩ := root_u5_pair τ h [3] 4 5 (constP [(3, 1)]) (constP [(3, 1)])
    rw [h, (ulen_one h {0, 1} 3).2, h4, h5, eval_constP,
      ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_left rfl]
  · obtain ⟨hlt, hb⟩ := b2_p6 h 4 5 [] 28 {0, 1} (monoVal_nil _).symm
    rw [h, ite_eq_left hlt, hb]
  · obtain ⟨hlt, hb⟩ := b2_bal h 4 5 [] 3 28 {0, 1} (monoVal_nil _).symm
    rw [h, ite_eq_left hlt, hb]
  · obtain ⟨hlt, hb⟩ := b2_cat false h 4 5 [] 28 30 {0, 1} (monoVal_nil _).symm
    rw [h, ite_eq_left hlt, hb]; rfl
  · obtain ⟨hlt, hb⟩ := b2_cat true h 4 5 [] 28 29 {0, 1} (monoVal_nil _).symm
    rw [h, ite_eq_left hlt, hb]; rfl
  · obtain ⟨h4, h5⟩ := root_u5_pair τ h [3, 27] 4 5 (loP [(3, 1)] 27) (loP [(3, 1)] 27)
    obtain ⟨_, h6⟩ := root_u5_pair τ h [3, 27] 5 6 (loP [(3, 1)] 27) (loP [(3, 1)] 27)
    have hlo := (eval_lo_hi_bds h [(3, 1)] 27).1
    rw [h, (ulen_one h {0, 1} 3).2, h4, h5, h6, ite_eq_right (by linarith),
      ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (by linarith)]
  · obtain ⟨h4, h5⟩ := root_u5_pair τ h [3, 23] 4 5 (loP [(3, 1)] 23) (hiP [(3, 1)] 23)
    obtain ⟨hlo, hhi⟩ := eval_lo_hi_bds h [(3, 1)] 23
    rw [h, h4, h5, ite_eq_right (by linarith), ite_eq_left (by linarith)]
  · obtain ⟨h4, h5⟩ := root_u5_pair τ h [3, 15] 4 5 (loP [(3, 1)] 15) (loP [(3, 1)] 15)
    obtain ⟨_, h6⟩ := root_u5_pair τ h [3, 15] 5 6 (loP [(3, 1)] 15) (hiP [(3, 1)] 15)
    obtain ⟨hlo, hhi⟩ := eval_lo_hi_bds h [(3, 1)] 15
    rw [h, (ulen_one h {0, 1} 3).2, h4, h5, h6, ite_eq_right (by linarith),
      ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_left (by linarith)]

/-! ### `U5 2` -/

noncomputable def cls2 (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  let U₁ := exp (-τ.unrootedLength {0, 1})
  let U₂ := exp (-τ.unrootedLength {0, 1, 2})
  if u τ 7 < u τ 5 then
    branch2 (u τ 5) (u τ 7) U₁ U₂
      (hierarchyOf {{0, 1}, {3, 4}, {0, 1, 2}})
      (hierarchyOf {{0, 1}, {0, 1, 2}})
      (hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}})
      (hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}})
  else if u τ 5 < u τ 7 then
    branch2 (u τ 7) (u τ 5) U₂ U₁
      (hierarchyOf {{3, 4}, {0, 1}, {2, 3, 4}})
      (hierarchyOf {{3, 4}, {2, 3, 4}})
      (hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}})
      (hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}})
  else if u τ 7 = 1 / 15 * U₁ * U₂ then hierarchyOf {{0, 1}, {3, 4}}
  else hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}

private theorem cls2_eq (τ : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 2) :
    cls2 τ = τ.clusters := by
  have hR := classify_mem_rootings5 τ 2 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  unfold cls2
  rcases hR with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨hlt, hb⟩ := b2_cat false h 5 7 [(3, 1)] 7 15 {0, 1, 2} (ulen_one h {0, 1} 3).2
    rw [h, ite_eq_left hlt, hb]; rfl
  · obtain ⟨hlt, hb⟩ := b2_cat true h 5 7 [(3, 1)] 7 23 {0, 1, 2} (ulen_one h {0, 1} 3).2
    rw [h, ite_eq_left hlt, hb]; rfl
  · obtain ⟨hlt, hb⟩ := b2_cat false h 7 5 [(24, 1)] 28 30 {0, 1} (ulen_one h {0, 1, 2} 24).2
    rw [h, ite_eq_right (by linarith), ite_eq_left hlt, hb]; rfl
  · obtain ⟨hlt, hb⟩ := b2_cat true h 7 5 [(24, 1)] 28 29 {0, 1} (ulen_one h {0, 1, 2} 24).2
    rw [h, ite_eq_right (by linarith), ite_eq_left hlt, hb]; rfl
  · obtain ⟨h5, h7⟩ := root_u5_pair τ h [3, 24, 27] 5 7
      (loP [(3, 1), (24, 1)] 27) (loP [(3, 1), (24, 1)] 27)
    have hlo := (eval_lo_hi_bds h [(3, 1), (24, 1)] 27).1
    simp only [monoVal_cons, monoVal_nil, pow_one, mul_one] at hlo
    rw [h, h5, h7, (ulen_one h {0, 1} 3).1, (ulen_one h {0, 1, 2} 24).1,
      ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (by linarith)]
  · obtain ⟨hlt, hb⟩ := b2_bal h 5 7 [(3, 1)] 24 7 {0, 1, 2} (ulen_one h {0, 1} 3).2
    rw [h, ite_eq_left hlt, hb]
  · obtain ⟨hlt, hb⟩ := b2_bal h 7 5 [(24, 1)] 3 28 {0, 1} (ulen_one h {0, 1, 2} 24).2
    rw [h, ite_eq_right (by linarith), ite_eq_left hlt, hb]
  · obtain ⟨h5, h7⟩ := root_u5_pair τ h [3, 24] 5 7
      (constP [(3, 1), (24, 1)]) (constP [(3, 1), (24, 1)])
    rw [h, h5, h7, (ulen_one h {0, 1} 3).1, (ulen_one h {0, 1, 2} 24).1,
      ite_eq_right (by linarith), ite_eq_right (by linarith),
      ite_eq_left (by simp [eval_constP, monoVal_cons, monoVal_nil, mul_assoc])]
  · obtain ⟨hlt, hb⟩ := b2_p6 h 5 7 [(3, 1)] 7 {0, 1, 2} (ulen_one h {0, 1} 3).2
    rw [h, ite_eq_left hlt, hb]
  · obtain ⟨hlt, hb⟩ := b2_p6 h 7 5 [(24, 1)] 28 {0, 1} (ulen_one h {0, 1, 2} 24).2
    rw [h, ite_eq_right (by linarith), ite_eq_left hlt, hb]

set_option maxHeartbeats 400000 in
private theorem u5_all (k : ℕ) (hk : k ∈ ({0, 1, 2} : Finset ℕ)) (τ τ' : SpeciesTree (Fin 5))
    (he : unroot τ.clusters = U5 k) (he' : unroot τ'.clusters = U5 k)
    (hd : τ.unrootedDist id = τ'.unrootedDist id) (hU' : τ.SameUnrootedMetricTree τ') :
    τ.SameRootedMetricTree τ' := by
  have hu := five_u_congr hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;>
    (have hR := classify_mem_rootings5 τ _ (by decide) he
     simp only [rootings5, mem_insert, mem_singleton] at hR)
  · have hcl : τ.clusters = τ'.clusters := by
      rw [← cls0_eq τ he, ← cls0_eq τ' he']; simp only [cls0, hu 1, hu 4, hu 5, hu 6]
    rcases hR with h | h | h | h | h | h <;> (have h' := hcl.symm.trans h)
    · exact five_same_of_lengths h h' (by simp)
    all_goals refine five_same_of_lengths h h' ?_; simp only [mem_singleton, forall_eq]
    · exact solve_loP h h' hU' 5 [] 30 (hu 5)
    · exact solve_loP h h' hU' 5 [] 29 (hu 5)
    · exact solve_loP h h' hU' 5 [] 27 (hu 5)
    · exact solve_loP h h' hU' 6 [] 23 (hu 6)
    · exact solve_loP h h' hU' 5 [] 15 (hu 5)
  · have hU1 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1} :=
      hU'.2 {0, 1} (he ▸ by decide) (by decide) (by decide)
    have hcl : τ.clusters = τ'.clusters := by
      rw [← cls1_eq τ he, ← cls1_eq τ' he']; simp only [cls1, hU1, hu 4, hu 5, hu 6]
    rcases hR with h | h | h | h | h | h | h | h <;> (have h' := hcl.symm.trans h) <;>
      refine five_same_of_lengths h h' ?_ <;>
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    · exact len_nr h h' hU'
    · exact len_nr h h' hU'
    · exact solve_bal h h' hU' 5 [] 3 28 (hu 5)
    · exact ⟨len_nr h h' hU', solve_loP h h' hU' 5 [(28, 3)] 30 (hu 5)⟩
    · exact ⟨len_nr h h' hU', solve_loP h h' hU' 5 [(28, 3)] 29 (hu 5)⟩
    · exact ⟨len_nr h h' hU', solve_loP h h' hU' 5 [(3, 1)] 27 (hu 5)⟩
    · exact ⟨len_nr h h' hU', solve_loP h h' hU' 6 [(3, 1)] 23 (hu 6)⟩
    · exact ⟨len_nr h h' hU', solve_loP h h' hU' 5 [(3, 1)] 15 (hu 5)⟩
  · have hU1 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1} :=
      hU'.2 {0, 1} (he ▸ by decide) (by decide) (by decide)
    have hU2 : τ.unrootedLength {0, 1, 2} = τ'.unrootedLength {0, 1, 2} :=
      hU'.2 {0, 1, 2} (he ▸ by decide) (by decide) (by decide)
    have hcl : τ.clusters = τ'.clusters := by
      rw [← cls2_eq τ he, ← cls2_eq τ' he']; simp only [cls2, hU1, hU2, hu 5, hu 7]
    rcases hR with h | h | h | h | h | h | h | h | h | h <;> (have h' := hcl.symm.trans h) <;>
      refine five_same_of_lengths h h' ?_ <;>
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    · exact ⟨len_nr h h' hU', len_nr h h' hU', solve_loP h h' hU' 7 [(3, 1), (7, 3)] 15 (hu 7)⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU', solve_loP h h' hU' 7 [(3, 1), (7, 3)] 23 (hu 7)⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU', solve_loP h h' hU' 5 [(24, 1), (28, 3)] 30 (hu 5)⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU', solve_loP h h' hU' 5 [(24, 1), (28, 3)] 29 (hu 5)⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU', solve_loP h h' hU' 7 [(3, 1), (24, 1)] 27 (hu 7)⟩
    · exact ⟨len_nr h h' hU', solve_bal h h' hU' 7 [(3, 1)] 24 7 (hu 7)⟩
    · exact ⟨len_nr h h' hU', solve_bal h h' hU' 5 [(24, 1)] 3 28 (hu 5)⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU'⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU'⟩
    · exact ⟨len_nr h h' hU', len_nr h h' hU'⟩

theorem appC_sameRootedMetricTree (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) (hU : σ.SameUnrootedMetricTree σ') :
    σ.SameRootedMetricTree σ' := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  refine u5_all k hk _ _ he ?_ ((SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h)
    ((SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e.symm).2 hU)
  rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hU.1, ← unroot_relabelFamily]
  exact he

end ADR11
