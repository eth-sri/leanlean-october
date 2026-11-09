module

public import ADR11.Rootings.Proofs

@[expose] public section

namespace ADR11

open Finset Real

abbrev Same5 (τ : SpeciesTree (Fin 5)) : Prop :=
  ∀ τ' : SpeciesTree (Fin 5), τ'.clusters = τ.clusters →
    τ.unrootedDist id = τ'.unrootedDist id → τ.SameRootedMetricTree τ'

noncomputable def tag0 (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  h5 (if u τ 1 < u τ 13 then [30]
      else if u τ 1 < u τ 4 then [29]
      else if u τ 2 < u τ 1 then [27]
      else if u τ 1 < u τ 2 then [23]
      else if u τ 1 < u τ 3 then [15]
      else [])

noncomputable def tag1 (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  h5 (if u τ 5 < u τ 4 then
        if u τ 4 < u τ 13 then [28, 30]
        else if u τ 13 < u τ 4 then [28, 29]
        else if linVal τ [(6, 4), (9, 5)] ^ 3 < linVal τ [(15, 5)] then [3, 28]
        else [28]
      else
        if u τ 4 < u τ 5 then [3, 23]
        else if u τ 2 < u τ 1 then [3, 27]
        else if u τ 1 < u τ 3 then [3, 15]
        else [3])

noncomputable def tag2 (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  h5 (if u τ 7 < u τ 5 then
        if u τ 5 < u τ 6 then [3, 7, 15]
        else if u τ 6 < u τ 5 then [3, 7, 23]
        else if linVal τ [(3, 2), (3, 5), (9, 7)] ^ 2 * linVal τ [(6, 5), (9, 7)] <
            linVal τ [(15, 7)] then [24, 3, 7]
        else [3, 7]
      else if u τ 5 < u τ 7 then
        if u τ 7 < u τ 14 then [24, 28, 30]
        else if u τ 14 < u τ 7 then [24, 28, 29]
        else if linVal τ [(3, 4), (3, 7), (9, 5)] ^ 2 * linVal τ [(6, 7), (9, 5)] <
            linVal τ [(15, 5)] then [3, 24, 28]
        else [24, 28]
      else
        if u τ 5 < u τ 8 then [3, 24, 27]
        else [3, 24])

variable {τ : SpeciesTree (Fin 5)}

theorem same_one (a d : ℕ) {L : List (ℚ × ℕ)}
    {reqs : List (List (ℚ × ℕ) × List (ℚ × List (ℕ × ℕ)))}
    (hτ : τ.clusters = h5 [a])
    (hc : root_fullCertB [a] ((L, [(1, [(a, d)])]) :: reqs) = true := by decide +kernel)
    (hd : d ≠ 0 := by decide) :
    (decC 5 a ∈ τ.clusters ∧ decC 5 a ≠ univ) ∧
      (linVal τ L = evalPoly τ.length [(1, [(a, d)])] ∧
        reqs.Forall (fun r => linVal τ r.1 = evalPoly τ.length r.2)) ∧ Same5 τ := by
  obtain ⟨hm, hall⟩ := fullCert_all τ hτ hc
  have h1 := (List.forall_cons ..).1 hall
  refine ⟨hm a List.mem_cons_self, h1, fun τ' hτ' hd' => ?_⟩
  have h1' := (List.forall_cons ..).1 (fullCert_all τ' (hτ'.trans hτ) hc).2
  exact sameRooted_of_cs hτ hτ' (length_eq_of_single (monoVal_eq_of_lin hd' h1.1 h1'.1) hd)

theorem same_two (a c e d : ℕ) {L₁ L₂ : List (ℚ × ℕ)}
    {reqs : List (List (ℚ × ℕ) × List (ℚ × List (ℕ × ℕ)))}
    (hτ : τ.clusters = h5 [a, c])
    (hc : root_fullCertB [a, c]
      ((L₁, [(1, [(a, 1)])]) :: (L₂, [(1, normKey [(a, e), (c, d)])]) :: reqs) = true := by decide +kernel)
    (hd : d ≠ 0 := by decide) :
    ((decC 5 a ∈ τ.clusters ∧ decC 5 a ≠ univ) ∧ (decC 5 c ∈ τ.clusters ∧ decC 5 c ≠ univ)) ∧
      reqs.Forall (fun r => linVal τ r.1 = evalPoly τ.length r.2) ∧ Same5 τ := by
  obtain ⟨hm, h1, h2⟩ := fullCert_all τ hτ hc
  have h2 := (List.forall_cons ..).1 h2
  refine ⟨⟨hm a (by simp), hm c (by simp)⟩, h2.2, fun τ' hτ' hd' => ?_⟩
  obtain ⟨_, h1', h2'⟩ := fullCert_all τ' (hτ'.trans hτ) hc
  have l1 := length_eq_of_single (monoVal_eq_of_lin hd' h1 h1')
  have m2 := monoVal_eq_of_lin hd' h2.1 ((List.forall_cons ..).1 h2').1
  rw [monoVal_normKey, monoVal_normKey] at m2
  exact sameRooted_of_cs hτ hτ' ⟨l1, length_eq_of_pair l1 m2 hd⟩

theorem same_cube2 (a b i₅ i₇ : ℕ) {reqs : List (List (ℚ × ℕ) × List (ℚ × List (ℕ × ℕ)))}
    (hτ : τ.clusters = h5 [a, b])
    (hc : root_fullCertB [a, b]
      (([(6, i₅), (9, i₇)], [(1, [(a, 1), (b, 1)])]) ::
       ([(15, i₇)], [(1, [(a, 1), (b, 3)])]) ::
       ([(1, i₅), (-1, i₇)], diffPoly (1 / 6) [(a, 1)] b 1 2) :: reqs) = true := by decide +kernel) :
    (decC 5 a ∈ τ.clusters ∧ decC 5 a ≠ univ) ∧
      u τ i₇ < u τ i₅ ∧
      linVal τ [(6, i₅), (9, i₇)] = monoVal τ.length [(a, 1), (b, 1)] ∧
      linVal τ [(15, i₇)] = monoVal τ.length [(a, 1), (b, 3)] ∧
      reqs.Forall (fun r => linVal τ r.1 = evalPoly τ.length r.2) ∧ Same5 τ := by
  obtain ⟨hm, h1, h2, h3⟩ := fullCert_all τ hτ hc
  have h3 := (List.forall_cons ..).1 h3
  refine ⟨hm a (by simp), u_lt_of_lin (hm b (by simp)) h3.1,
    linVal_eq_monoVal h1, linVal_eq_monoVal h2, h3.2, fun τ' hτ' hd' => ?_⟩
  obtain ⟨_, h1', h2', _⟩ := fullCert_all τ' (hτ'.trans hτ) hc
  have m1 := monoVal_eq_of_lin hd' h1 h1'
  have lb := length_eq_of_cube (p := [(a, 1)]) m1 (monoVal_eq_of_lin hd' h2 h2')
  exact sameRooted_of_cs hτ hτ' ⟨length_eq_of_pair_left lb m1, lb⟩

theorem p3_spec (a k i o₁ o₂ o₃ : ℕ) (hτ : τ.clusters = h5 [a])
    (hc : root_fullCertB [a] [
      ([(30, k), (-15, i)], [(1, [(a, 6)])]),
      ([(1, i), (-1, k)], diffPoly (1 / 18) [] a 0 6),
      ([(1, o₁), (-1, k)], []),
      ([(1, o₂), (-1, k)], []),
      ([(1, o₃), (-1, k)], [])] = true := by decide +kernel) :
    (u τ k < u τ i ∧ u τ o₁ = u τ k ∧ u τ o₂ = u τ k ∧ u τ o₃ = u τ k) ∧ Same5 τ := by
  obtain ⟨ha, ⟨_, h1, h2, h3, h4⟩, hs⟩ := same_one a 6 hτ hc
  exact ⟨⟨u_lt_of_lin ha h1, u_eq_of_lin h2, u_eq_of_lin h3, u_eq_of_lin h4⟩, hs⟩

theorem p9_spec (c k i : ℕ) (hτ : τ.clusters = h5 [28, c])
    (hc : root_fullCertB [28, c] [
      ([(3, 4), (9, 5), (3, 13)], [(1, [(28, 1)])]),
      ([(15, k), (15, 5), (-15, i)], [(1, normKey [(28, 3), (c, 6)])]),
      ([(1, k), (-1, 5)], diffPoly (1 / 6) [] 28 1 2),
      ([(1, i), (-1, k)], diffPoly (1 / 18) [(28, 3)] c 0 6)] = true := by decide +kernel) :
    (u τ 5 < u τ k ∧ u τ k < u τ i) ∧ Same5 τ := by
  obtain ⟨⟨h28, hc'⟩, ⟨h1, h2⟩, hs⟩ := same_two 28 c 3 6 hτ hc
  exact ⟨⟨u_lt_of_lin h28 h1, u_lt_of_lin hc' h2⟩, hs⟩

theorem cat_spec (a b c i₂ i₅ i₆ i₇ : ℕ) (hτ : τ.clusters = h5 [a, b, c])
    (hc : root_fullCertB [a, b, c] [
      ([(1, i₅), (-1, i₇)], diffPoly (1 / 6) [(a, 1)] b 1 2),
      ([(1, i₆), (-1, i₅)], diffPoly (1 / 18) [(a, 1), (b, 3)] c 0 6),
      ([(3, i₂), (3, i₆), (9, i₇)], [(1, [(b, 1)])]),
      ([(3, i₅), (3, i₆), (9, i₇)], [(1, [(a, 1), (b, 1)])]),
      ([(15, i₅), (-15, i₆), (15, i₇)], [(1, [(a, 1), (b, 3), (c, 6)])])] = true := by decide +kernel) :
    (u τ i₇ < u τ i₅ ∧ u τ i₅ < u τ i₆) ∧ Same5 τ := by
  obtain ⟨hm, h1, h2, h3, h4, h5⟩ := fullCert_all τ hτ hc
  refine ⟨⟨u_lt_of_lin (hm b (by simp)) h1, u_lt_of_lin (hm c (by simp)) h2⟩, fun τ' hτ' hd => ?_⟩
  obtain ⟨_, _, _, h3', h4', h5'⟩ := fullCert_all τ' (hτ'.trans hτ) hc
  have lb := length_eq_of_single (monoVal_eq_of_lin hd h3 h3')
  have la := length_eq_of_pair_left lb (monoVal_eq_of_lin hd h4 h4')
  exact sameRooted_of_cs hτ hτ' ⟨la, lb, length_eq_of_triple la lb (monoVal_eq_of_lin hd h5 h5')⟩

theorem bal_spec (c a b i₂ i₅ i₆ i₇ : ℕ) (hτ : τ.clusters = h5 [c, a, b])
    (hc : root_fullCertB [c, a, b] [
      ([(1, i₅), (-1, i₆)], []),
      ([(1, i₅), (-1, i₇)], diffPoly (1 / 6) [(c, 1), (a, 1)] b 1 2),
      ([(3, i₂), (3, i₅), (9, i₇)], [(1, [(c, 1), (b, 1)])]),
      ([(6, i₅), (9, i₇)], [(1, [(c, 1), (a, 1), (b, 1)])]),
      ([(15, i₇)], [(1, [(c, 1), (a, 1), (b, 3)])])] = true := by decide +kernel) :
    (u τ i₅ = u τ i₆ ∧ u τ i₇ < u τ i₅ ∧
      linVal τ [(3, i₂), (3, i₅), (9, i₇)] ^ 2 * linVal τ [(6, i₅), (9, i₇)] <
        linVal τ [(15, i₇)]) ∧ Same5 τ := by
  obtain ⟨hm, h1, h2, h3, h4, h5⟩ := fullCert_all τ hτ hc
  have hc_mem := hm c List.mem_cons_self
  have hlt : linVal τ [(3, i₂), (3, i₅), (9, i₇)] ^ 2 * linVal τ [(6, i₅), (9, i₇)] <
      linVal τ [(15, i₇)] := by
    rw [linVal_eq_monoVal h3, linVal_eq_monoVal h4, linVal_eq_monoVal h5,
      show monoVal τ.length [(c, 1), (b, 1)] ^ 2 * monoVal τ.length [(c, 1), (a, 1), (b, 1)] =
        monoVal τ.length [(c, 2)] * monoVal τ.length [(c, 1), (a, 1), (b, 3)] by
        simp only [monoVal_cons, monoVal_nil]; ring]
    exact mul_lt_of_lt_one_left (monoVal_pos _ _) (monoVal_single_lt_one τ hc_mem.1 hc_mem.2)
  refine ⟨⟨u_eq_of_lin h1, u_lt_of_lin (hm b (by simp)) h2, hlt⟩, fun τ' hτ' hd => ?_⟩
  obtain ⟨_, _, _, h3', h4', h5'⟩ := fullCert_all τ' (hτ'.trans hτ) hc
  have m4 := monoVal_eq_of_lin hd h4 h4'
  have lb := length_eq_of_cube (p := [(c, 1), (a, 1)]) m4 (monoVal_eq_of_lin hd h5 h5')
  have lc := length_eq_of_pair_left lb (monoVal_eq_of_lin hd h3 h3')
  exact sameRooted_of_cs hτ hτ' ⟨lc, length_eq_of_pair_left lb (monoVal_cons_cancel lc m4), lb⟩

theorem p6_spec (a b i₂ i₅ i₆ i₇ : ℕ) (hτ : τ.clusters = h5 [a, b])
    (hc : root_fullCertB [a, b] [
      ([(6, i₅), (9, i₇)], [(1, [(a, 1), (b, 1)])]),
      ([(15, i₇)], [(1, [(a, 1), (b, 3)])]),
      ([(1, i₅), (-1, i₇)], diffPoly (1 / 6) [(a, 1)] b 1 2),
      ([(1, i₅), (-1, i₆)], []),
      ([(3, i₂), (3, i₅), (9, i₇)], [(1, [(b, 1)])])] = true := by decide +kernel) :
    (u τ i₅ = u τ i₆ ∧ u τ i₇ < u τ i₅ ∧
      linVal τ [(3, i₂), (3, i₅), (9, i₇)] ^ 2 * linVal τ [(6, i₅), (9, i₇)] =
        linVal τ [(15, i₇)]) ∧ Same5 τ := by
  obtain ⟨_, hlt, m1, m2, ⟨h1, h3⟩, hs⟩ := same_cube2 a b i₅ i₇ hτ hc
  refine ⟨⟨u_eq_of_lin h1, hlt, ?_⟩, hs⟩
  rw [linVal_eq_monoVal h3, m1, m2]
  simp only [monoVal_cons, monoVal_nil]; ring

theorem rootings_zero_main (hk : unroot τ.clusters = U5 0) :
    tag0 τ = τ.clusters ∧ Same5 τ := by
  have hR := classify_mem_rootings5 τ 0 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h
  · obtain ⟨_, h1, h2, h3, h4⟩ := fullCert_all τ h (reqs := [
      ([(1, 13), (-1, 1)], []), ([(1, 4), (-1, 1)], []),
      ([(1, 2), (-1, 1)], []), ([(1, 3), (-1, 1)], [])]) (by decide +kernel)
    exact ⟨by simp [tag0, u_eq_of_lin h1, u_eq_of_lin h2, u_eq_of_lin h3, u_eq_of_lin h4, h],
      fun τ' h' _ => sameRooted_of_cs h h' trivial⟩
  · obtain ⟨⟨h1, _, _, _⟩, hs⟩ := p3_spec 30 1 13 2 3 4 h
    exact ⟨by simp [tag0, h1, h], hs⟩
  · obtain ⟨⟨h1, h2, _, _⟩, hs⟩ := p3_spec 29 1 4 13 2 3 h
    exact ⟨by simp [tag0, h2, h1, h], hs⟩
  · obtain ⟨⟨h1, h2, h3, _⟩, hs⟩ := p3_spec 27 2 1 13 4 3 h
    exact ⟨by simp [tag0, h2, h3, h1, not_lt_of_gt h1, h], hs⟩
  · obtain ⟨⟨h1, h2, h3, _⟩, hs⟩ := p3_spec 23 1 2 13 4 3 h
    exact ⟨by simp [tag0, h2, h3, h1, not_lt_of_gt h1, h], hs⟩
  · obtain ⟨⟨h1, h2, h3, h4⟩, hs⟩ := p3_spec 15 1 3 13 4 2 h
    exact ⟨by simp [tag0, h2, h3, h4, h1, h], hs⟩

theorem p10_spec (c m i j o₁ k₁ o₂ k₂ : ℕ) (hτ : τ.clusters = h5 [3, c])
    (hc : root_fullCertB [3, c] [
      ([(12, 4), (3, m)], [(1, [(3, 1)])]),
      ([(30, 4), (-15, m)], [(1, normKey [(3, 1), (c, 6)])]),
      ([(1, j), (-1, i)], diffPoly (1 / 18) [(3, 1)] c 0 6),
      ([(1, o₁), (-1, k₁)], []),
      ([(1, o₂), (-1, k₂)], [])] = true := by decide +kernel) :
    (u τ i < u τ j ∧ u τ o₁ = u τ k₁ ∧ u τ o₂ = u τ k₂) ∧ Same5 τ := by
  obtain ⟨⟨_, hc'⟩, ⟨h1, h2, h3⟩, hs⟩ := same_two 3 c 1 6 hτ hc
  exact ⟨⟨u_lt_of_lin hc' h1, u_eq_of_lin h2, u_eq_of_lin h3⟩, hs⟩

theorem rootings_one_main (hk : unroot τ.clusters = U5 1) :
    tag1 τ = τ.clusters ∧ Same5 τ := by
  have hR := classify_mem_rootings5 τ 1 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h
  · obtain ⟨_, ⟨_, h1, h2, h3⟩, hs⟩ := same_one 3 1 (L := [(15, 4)])
      (reqs := [([(1, 5), (-1, 4)], []), ([(1, 2), (-1, 1)], []), ([(1, 3), (-1, 1)], [])]) h
    exact ⟨by simp [tag1, u_eq_of_lin h1, u_eq_of_lin h2, u_eq_of_lin h3, h], hs⟩
  · obtain ⟨h28, ⟨h4, h1, h2, h3⟩, hs⟩ := same_one 28 3 (L := [(15, 5)])
      (reqs := [([(1, 4), (-1, 5)], diffPoly (1 / 6) [] 28 1 2),
        ([(1, 13), (-1, 4)], []), ([(6, 4), (9, 5)], [(1, [(28, 1)])])]) h
    have lt1 := u_lt_of_lin h28 h1
    have eq2 : linVal τ [(6, 4), (9, 5)] ^ 3 = linVal τ [(15, 5)] := by
      rw [linVal_eq_monoVal h3, linVal_eq_monoVal h4]; simp only [monoVal_cons, monoVal_nil]; ring
    exact ⟨by simp [tag1, lt1, u_eq_of_lin h2, eq2, h], hs⟩
  · obtain ⟨h3, lt1, m1, m2, h2, hs⟩ := same_cube2 3 28 4 5
      (reqs := [([(1, 13), (-1, 4)], [])]) h
    have lt2 : linVal τ [(6, 4), (9, 5)] ^ 3 < linVal τ [(15, 5)] := by
      rw [m1, m2, show monoVal τ.length [(3, 1), (28, 1)] ^ 3 =
        monoVal τ.length [(3, 2)] * monoVal τ.length [(3, 1), (28, 3)] by
        simp only [monoVal_cons, monoVal_nil]; ring]
      exact mul_lt_of_lt_one_left (monoVal_pos _ _) (monoVal_single_lt_one τ h3.1 h3.2)
    exact ⟨by simp [tag1, lt1, u_eq_of_lin h2, lt2, h], hs⟩
  · obtain ⟨⟨h1, h2⟩, hs⟩ := p9_spec 30 4 13 h
    exact ⟨by simp [tag1, h1, h2, h], hs⟩
  · obtain ⟨⟨h1, h2⟩, hs⟩ := p9_spec 29 13 4 h
    exact ⟨by simp [tag1, lt_trans h1 h2, not_lt_of_gt h2, h2, h], hs⟩
  · obtain ⟨⟨h1, h2, _⟩, hs⟩ := p10_spec 27 8 2 1 5 4 4 4 h
    exact ⟨by simp [tag1, h2, h1, h], hs⟩
  · obtain ⟨⟨h1, _, _⟩, hs⟩ := p10_spec 23 5 4 5 4 4 4 4 h
    exact ⟨by simp [tag1, not_lt_of_gt h1, h1, h], hs⟩
  · obtain ⟨⟨h1, h2, h3⟩, hs⟩ := p10_spec 15 6 1 3 5 4 2 1 h
    exact ⟨by simp [tag1, h2, h3, h1, h], hs⟩

set_option maxHeartbeats 400000 in
theorem rootings_two_main (hk : unroot τ.clusters = U5 2) :
    tag2 τ = τ.clusters ∧ Same5 τ := by
  have hR := classify_mem_rootings5 τ 2 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨⟨h1, h2⟩, hs⟩ := cat_spec 3 7 15 2 5 6 7 h
    exact ⟨by simp [tag2, h1, h2, h], hs⟩
  · obtain ⟨⟨h1, h2⟩, hs⟩ := cat_spec 3 7 23 3 6 5 7 h
    exact ⟨by simp [tag2, lt_trans h1 h2, not_lt_of_gt h2, h2, h], hs⟩
  · obtain ⟨⟨h1, h2⟩, hs⟩ := cat_spec 24 28 30 4 7 14 5 h
    exact ⟨by simp [tag2, not_lt_of_gt h1, h1, h2, h], hs⟩
  · obtain ⟨⟨h1, h2⟩, hs⟩ := cat_spec 24 28 29 13 14 7 5 h
    have h57 := lt_trans h1 h2
    exact ⟨by simp [tag2, not_lt_of_gt h57, h57, not_lt_of_gt h2, h2, h], hs⟩
  · have hc : root_fullCertB [3, 24, 27] [
      ([(1, 7), (-1, 5)], []),
      ([(1, 8), (-1, 5)], diffPoly (1 / 18) [(3, 1), (24, 1)] 27 0 6),
      ([(3, 4), (9, 5), (3, 8)], [(1, [(3, 1)])]),
      ([(3, 2), (9, 5), (3, 8)], [(1, [(24, 1)])]),
      ([(30, 5), (-15, 8)], [(1, [(3, 1), (24, 1), (27, 6)])])] = true := by decide +kernel
    obtain ⟨hm, h1, h2, h3, h4, h5⟩ := fullCert_all τ h hc
    have lt1 := u_lt_of_lin (hm 27 (by simp)) h2
    refine ⟨by simp [tag2, u_eq_of_lin h1, lt1, h], fun τ' h' hd => ?_⟩
    obtain ⟨_, _, _, h3', h4', h5'⟩ := fullCert_all τ' (h'.trans h) hc
    have l3 := length_eq_of_single (monoVal_eq_of_lin hd h3 h3')
    have l24 := length_eq_of_single (monoVal_eq_of_lin hd h4 h4')
    exact sameRooted_of_cs h h' ⟨l3, l24, length_eq_of_triple l3 l24
      (monoVal_eq_of_lin hd h5 h5')⟩
  · obtain ⟨⟨h1, h2, h3⟩, hs⟩ := bal_spec 24 3 7 2 5 6 7 h
    exact ⟨by simp [tag2, h2, ← h1, h3, h], hs⟩
  · obtain ⟨⟨h1, h2, h3⟩, hs⟩ := bal_spec 3 24 28 4 7 14 5 h
    exact ⟨by simp [tag2, not_lt_of_gt h2, h2, ← h1, h3, h], hs⟩
  · obtain ⟨_, ⟨h1, h2⟩, hs⟩ := same_two 3 24 0 1
      (L₁ := [(3, 4), (12, 5)]) (L₂ := [(3, 2), (12, 5)])
      (reqs := [([(1, 7), (-1, 5)], []), ([(1, 8), (-1, 5)], [])]) h
    exact ⟨by simp [tag2, u_eq_of_lin h1, u_eq_of_lin h2, h], hs⟩
  · obtain ⟨⟨h1, h2, h3⟩, hs⟩ := p6_spec 3 7 2 5 6 7 h
    exact ⟨by simp [tag2, h2, ← h1, h3, h], hs⟩
  · obtain ⟨⟨h1, h2, h3⟩, hs⟩ := p6_spec 24 28 4 7 14 5 h
    exact ⟨by simp [tag2, not_lt_of_gt h2, h2, ← h1, h3, h], hs⟩

end ADR11
