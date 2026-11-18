module

public import Chazelle.Core.ShootCutShK1R
public import Chazelle.Core.ShootCutGen
public import Chazelle.Core.ShootCutArc
public import Chazelle.Core.ShootCutValid

/-!
# WP-G, part 53: the length of a kind-1 piece

A kind-1 piece handed by the core covers `2^g` counted walk edges inside the subarc, so
`2^g` is at most the weight of the subarc, hence at most `γ` (`kind1_pw_le`).  This bounds the
size of the chain the ray-shooter queries.

* `KPath.mem`: every piece of a path of increasing unwrapped keys has unwrapped ends inside the
  range of the path.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (sideInArc)

namespace ShootCut

variable {M : Model} {Q : Polygon}

/-- **The unwrapped ends of a piece** of a path lie within the range of the path. -/
theorem KPath.mem {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q n V ps V' →
    ∀ pc ∈ ps, ∃ U U₁ : ℝ, V ≤ U ∧ U < U₁ ∧ U₁ ≤ V' ∧ (∃ i : ℤ, U = M.key Q pc.s + i * n) ∧
      ∃ j : ℤ, U₁ = M.key Q pc.e + j * n
  | _, [], _, _, _, h => by simp at h
  | V, q :: qs, V', ⟨h1, V₁, h2, h3, h4⟩, pc, hpc => by
    rcases List.mem_cons.1 hpc with rfl | hpc
    · exact ⟨V, V₁, le_rfl, h2, h4.le, h1, h3⟩
    · obtain ⟨U, U₁, a1, a2, a3, a4, a5⟩ := KPath.mem h4 pc hpc
      exact ⟨U, U₁, by linarith, a2, a3, a4, a5⟩

/-- **A kind-1 piece is no longer than the weight of the subarc.** -/
theorem kind1_pw_le {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ : ℕ} {s e : WPos}
    {ps : List Pc} (arc : ArcOK C (Qof P) s e ps)
    (hs : 0 ≤ (chainModel C).key (Qof P) s ∧
      (chainModel C).key (Qof P) s < ((2 * C.m + 7 : ℕ) : ℝ))
    (he : 0 ≤ (chainModel C).key (Qof P) e ∧
      (chainModel C).key (Qof P) e < ((2 * C.m + 7 : ℕ) : ℝ))
    {pc : Pc} (hpc : pc ∈ ps) (hok : PcOK P C m₀ h γ pc) (hk : pc.kind = 1) :
    pc.pw ≤ (chainModel C).arcWt ((chainModel C).key (Qof P) s)
      ((chainModel C).key (Qof P) e) := by
  obtain ⟨g, b, -, -, -, -, hpw, -, -, -, hs0, he0, h6, hee, hem, -, -⟩ :=
    hok.2.2.2.2.2.2 hk
  set n := 2 * C.m + 7 with hn
  set a := (chainModel C).key (Qof P) s with ha
  set b' := (chainModel C).key (Qof P) e with hb'
  have hn0 : (0 : ℝ) < (n : ℝ) := by rw [hn]; positivity
  set T := a + len (n : ℝ) a b' with hT
  have hTA : T ≤ a + n := by have := len_le (n : ℝ) a b' hs.1 he.2; linarith
  obtain ⟨U, U₁, hAU, hUU, hUT, ⟨i, hi⟩, ⟨j, hj⟩⟩ := KPath.mem arc.kp pc hpc
  have ks : (chainModel C).key (Qof P) pc.s = (pc.s.edge : ℝ) := by
    rw [show pc.s = ⟨pc.s.edge, 0⟩ by rw [← hs0]]; exact key_hgt0 _ _ _
  have ke : (chainModel C).key (Qof P) pc.e = (pc.s.edge : ℝ) + ((2 ^ g : ℕ) : ℝ) := by
    rw [show pc.e = ⟨pc.e.edge, 0⟩ by rw [← he0], key_hgt0, hee]; push_cast; ring
  rw [ks] at hi
  rw [ke] at hj
  replace hi : U = (pc.s.edge : ℝ) + i * (n : ℝ) := hi
  replace hj : U₁ = (pc.s.edge : ℝ) + ((2 ^ g : ℕ) : ℝ) + j * (n : ℝ) := hj
  replace hAU : a ≤ U := hAU
  replace hUT : U₁ ≤ T := hUT
  set p₀ := pc.s.edge with hp₀
  have hpn : (p₀ : ℝ) + ((2 ^ g : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast (show p₀ + 2 ^ g + 1 ≤ n by omega)
  have hg0 : (0 : ℝ) < ((2 ^ g : ℕ) : ℝ) := by positivity
  -- the two unwrappings agree
  have hji : j = i := by
    have d1 : (0 : ℝ) < ((2 ^ g : ℕ) : ℝ) + ((j : ℝ) - i) * n := by linarith
    have d2 : ((2 ^ g : ℕ) : ℝ) + ((j : ℝ) - i) * n ≤ n := by linarith
    have ec : ((j - i : ℤ) : ℝ) = (j : ℝ) - i := by push_cast; ring
    have a1 : ((j - i : ℤ) : ℝ) > -1 := by
      rw [ec]; by_contra hc; push Not at hc; nlinarith
    have a2 : ((j - i : ℤ) : ℝ) < 1 := by
      rw [ec]; by_contra hc; push Not at hc; nlinarith
    have b1 : j - i > -1 := by exact_mod_cast a1
    have b2 : j - i < 1 := by exact_mod_cast a2
    omega
  rw [hji] at hj
  -- the unwrapped start is a natural number
  have hi0 : 0 ≤ i := by
    have : (-1 : ℝ) < i := by
      by_contra hc; push Not at hc
      have : (i : ℝ) * n ≤ -n := by nlinarith
      have hp0 : (p₀ : ℝ) + 1 ≤ n := by linarith
      linarith [hs.1]
    have : (-1 : ℤ) < i := by exact_mod_cast this
    omega
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, (Int.toNat_of_nonneg hi0).symm⟩
  have hv : ((p₀ + i' * n : ℕ) : ℝ) = U := by rw [hi]; push_cast; ring
  have hv2 : ((p₀ + i' * n : ℕ) : ℝ) + ((2 ^ g : ℕ) : ℝ) = U₁ := by rw [hj]; push_cast; ring
  rw [hpw]
  obtain ⟨k, hk'⟩ := T_unw a b' (n : ℝ)
  refine arcWt_ge C (A := a) (T := T) hs he ⟨0, by simp⟩ ⟨k, hk'⟩ hTA
    (v := p₀ + i' * n) (L := 2 ^ g) ?_ ?_ (by rw [hv]; exact hAU) ?_
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [hv2]; exact hUT

/-- **A kind-1 piece of a subarc of weight `≤ γ`** has at most `γ` edges. -/
theorem kind1_pw_le_γ {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ : ℕ} {s e : WPos}
    {ps : List Pc} (arc : ArcOK C (Qof P) s e ps)
    (hsP : ProperPos (chainModel C) (Qof P) P.n s) (heP : ProperPos (chainModel C) (Qof P) P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key (Qof P) s)
      ((chainModel C).key (Qof P) e) ≤ γ)
    {pc : Pc} (hpc : pc ∈ ps) (hok : PcOK P C m₀ h γ pc) (hk : pc.kind = 1) : pc.pw ≤ γ :=
  le_trans (kind1_pw_le arc (key_range hsP hs1) (key_range heP he1) hpc hok hk) hwt

/-- **The cost of a query** on a kind-1 piece: granularity `gg ≤ cutGran γ`, `M ≤ γ` edges. -/
theorem query_cost_le {κ gg M γ : ℕ} (hg : gg ≤ cutGran γ) (hM : M ≤ γ) :
    ⌈(κ : ℝ) * ((gg : ℝ) ^ ((1 : ℝ) / 3) * ((M : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)⌉₊ ≤
      κ * (rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + 1) := by
  have e : (gg : ℝ) ^ ((1 : ℝ) / 3) * ((M : ℝ) + 1) ^ ((2 : ℝ) / 3) =
      ((gg : ℝ) * ((M : ℝ) + 1) ^ 2) ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have h1 : ((gg : ℝ) * ((M : ℝ) + 1) ^ 2) ^ ((1 : ℝ) / 3) ≤
      (((cutGran γ * (γ + 1) ^ 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    push_cast
    have a : (gg : ℝ) ≤ cutGran γ := by exact_mod_cast hg
    have b0 : (M : ℝ) ≤ γ := by exact_mod_cast hM
    have b : (M : ℝ) + 1 ≤ γ + 1 := by linarith
    have b2 : ((M : ℝ) + 1) ^ 2 ≤ ((γ : ℝ) + 1) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) b
    exact mul_le_mul a b2 (by positivity) (by positivity)
  have h2 : (((cutGran γ * (γ + 1) ^ 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤
      (rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) : ℝ) := Nat.le_ceil _
  rw [e]
  apply Nat.ceil_le.2
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith [h1.trans h2]) (by positivity)

/-- **The query facts of a kind-1 piece**, read from the grade table in any memory `m'` agreeing
with `m` below the bound `A` of the table: its Lemma 3.6 structure, the chain of the structure
(whose point set is the piece), its granularity and its length. -/
theorem kind1_query {O : OracleIface} {P : Polygon} {C : Chain} {m m' : ℕ → ℕ} {h γ A : ℕ}
    {pc : Pc} (hok : PcOK P C m h γ pc) (hk : pc.kind = 1)
    (hR : Robust A m fun m'' => GradeRaw O P m'' h A) (hm' : ∀ a, a < A → m' a = m a) :
    pc.entry + 2 < A ∧ O.At P m' (m' (pc.entry + 2)) ∧
      (∃ Hs Cα, ChainDescAt m' (m' (m' (pc.entry + 2))) (Qof P) Hs Cα ∧
        Cα.set = (chainModel C).arcSet (pc.s.edge : ℝ) ((pc.s.edge + pc.pw : ℕ) : ℝ)) ∧
      m' (m' (pc.entry + 2) + 2) ≤ cutGran γ ∧ m' (m' (m' (pc.entry + 2)) + 2) = pc.pw := by
  obtain ⟨hwf', Hs', Cα', N', hC', -, -, hset, -, -⟩ := kind1_facts hok hk hR hm' (le_refl A)
  obtain ⟨-, -, -, -, -, -, h1⟩ := hok
  obtain ⟨g, b, hg1, hgΛ, hb, hE, hpw, hx0, hbn, hgran, hs0, he0, h6, hee, hem, hdir, hW⟩ := h1 hk
  have hR' : Robust A m' fun m'' => GradeRaw O P m'' h A := hR.transport hm'
  have hΛ : g < m' h := by
    have := (grade_low hR).1
    rw [hm' h (by omega)]; exact hgΛ
  obtain ⟨Hs, Cα, N, hC, -, -, -, -, -, hmC, -, -, hAt, hS0, -, hS2⟩ := hR'.holds.2.2.2 g b hΛ hb
  obtain ⟨h2, hr, hlt⟩ := grade_entry hR hgΛ hb
  have hent : m' (m' (h + 2) + g) + 3 * b = pc.entry := by
    have e1 : m' (h + 2) = m (h + 2) := hm' _ h2
    have e2 : m' (m (h + 2) + g) = m (m (h + 2) + g) := hm' _ hr
    rw [e1, e2, hE]; rfl
  rw [hent] at hC hAt hS0 hS2
  have hlen : Cα.m = 2 ^ g := by rw [hmC]; exact gradeLen_full hbn
  refine ⟨by rw [hE]; exact hlt, hAt, ⟨Hs', Cα', by rw [hS0]; exact hC', ?_⟩,
    by rw [hS2]; exact hgran, ?_⟩
  · rw [← hset, show pc.s = ⟨pc.s.edge, 0⟩ by rw [← hs0], show pc.e = ⟨pc.e.edge, 0⟩ by rw [← he0],
      key_hgt0, key_hgt0, hee, hpw]
  · rw [hS0, hC.2.2.2.1, hlen, hpw]

end ShootCut

end

end Chazelle.Core
