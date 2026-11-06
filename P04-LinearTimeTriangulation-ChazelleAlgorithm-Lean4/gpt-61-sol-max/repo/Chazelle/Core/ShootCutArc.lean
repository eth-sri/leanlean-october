module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutFirst2

/-!
# WP-G, part 31: the pieces tile the subarc

`ArcOK s e ps`: the pieces `ps` start at `s`, end at a position with the key of `e`, are
consecutive, satisfy the tiling conjunct of `CutterOK` (the end of every piece but the last lies
strictly inside the cyclic interval from its start to `e`), and form a path of increasing
unwrapped keys from `k_s` to `k_s + len (k_s, k_e)` (`KPath`, for the shooter).

* `arcOK_single`: the single piece `[s, e]`;
* `arcOK_general`: the first piece, a path of walk vertices (the main loop) and the last piece.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (sideInArc)

namespace ShootCut

/-- The list of pieces goes from `x` to `y` (consecutively). -/
theorem Chained.get {x y : WPos} {ps : List Pc} (h : Chained x ps y) :
    ∀ i (hi : i + 1 < ps.length), (ps[i]'(by omega)).e = (ps[i + 1]'hi).s := by
  induction ps generalizing x with
  | nil => simp_all
  | cons p ps ih =>
    intro i hi
    obtain ⟨_, h2⟩ := h
    cases i with
    | zero =>
      cases ps with
      | nil => simp at hi
      | cons q qs =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        exact h2.1.symm
    | succ i =>
      grind

theorem Chained.append' : ∀ {x y z : WPos} {ps qs : List Pc}, Chained x ps y → Chained y qs z →
    Chained x (ps ++ qs) z
  | _, _, _, [], _, h, hq => by simp_all [Chained] 
  | _, _, _, _ :: _, _, ⟨h1, h2⟩, hq => ⟨h1, Chained.append' h2 hq⟩

theorem Chained.last : ∀ {x y : WPos} {ps : List Pc}, Chained x ps y → (hne : ps ≠ []) →
    (ps.getLast hne).e = y
  | _, _, [], _, hne => absurd rfl hne
  | _, _, [_], ⟨_, h2⟩, _ => h2
  | _, _, _ :: q :: qs, ⟨_, h2⟩, _ => by
      rw [List.getLast_cons (List.cons_ne_nil q qs)]
      exact Chained.last h2 (List.cons_ne_nil q qs)

theorem upath_chained {n : ℕ} : ∀ {u : ℕ} {ps : List Pc} {u' : ℕ}, UPath n u ps u' →
    Chained ⟨u % n, 0⟩ ps ⟨u' % n, 0⟩
  | _, [], _, h => by grind [Chazelle.Core.ShootCut.Chained, UPath]
  | _, _ :: _, _, ⟨h1, _, _, h3, h4⟩ => ⟨h1, by rw [h3]; exact upath_chained h4⟩

variable (C : Chain) (Q : Polygon)

/-- **The pieces tile the subarc** from `s` to `e`. -/
structure ArcOK (s e : WPos) (ps : List Pc) : Prop where
  ne : ps ≠ []
  hs : (ps.head ne).s = s
  he : (chainModel C).key Q (ps.getLast ne).e = (chainModel C).key Q e
  ch : ∀ i (hi : i + 1 < ps.length), (ps[i]'(by omega)).e = (ps[i + 1]'hi).s
  e6 : ∀ i (hi : i + 1 < ps.length), sideInArc ((chainModel C).key Q (ps[i]'(by omega)).s)
    ((chainModel C).key Q e) ((chainModel C).key Q (ps[i]'(by omega)).e)
  kp : KPath (chainModel C) Q ((2 * C.m + 7 : ℕ) : ℝ) ((chainModel C).key Q s) ps
    ((chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ) ((chainModel C).key Q s)
      ((chainModel C).key Q e))
  ends : ∀ pc ∈ ps, (pc.s = s ∨ pc.s.hgt = 0) ∧ (pc.e = e ∨ pc.e.hgt = 0)

variable {C Q}

theorem key_range {N : ℕ} {x : WPos} (hx : ProperPos (chainModel C) Q N x)
    (h1 : x.edge < 2 * C.m + 7) :
    0 ≤ (chainModel C).key Q x ∧ (chainModel C).key Q x < ((2 * C.m + 7 : ℕ) : ℝ) := by
  have := key_bounds hx
  have e : (x.edge : ℝ) + 1 ≤ ((2 * C.m + 7 : ℕ) : ℝ) := by exact_mod_cast h1
  ram_grind

theorem T_unw (k k' n : ℝ) : ∃ j : ℤ, k + len n k k' = k' + j * n := by
  unfold len
  split_ifs
  · simp_all
  · exact ⟨1, by grind⟩

/-- **A single piece** `[s, e]`. -/
theorem arcOK_single {N : ℕ} {s e : WPos} (hs : ProperPos (chainModel C) Q N s)
    (he : ProperPos (chainModel C) Q N e) (hs1 : s.edge < 2 * C.m + 7)
    (he1 : e.edge < 2 * C.m + 7) {p : Pc} (hps : p.s = s) (hpe : p.e = e) :
    ArcOK C Q s e [p] := by
  have ks := key_range hs hs1
  have ke := key_range he he1
  refine ⟨by simp, hps, by simp [hpe], fun i hi => by simp at hi, fun i hi => by simp at hi, ?_,
    fun pc hpc => ?_⟩
  swap
  · simp_all
  have hl := len_pos ((2 * C.m + 7 : ℕ) : ℝ) ((chainModel C).key Q s) ((chainModel C).key Q e)
    ks.2 ke.1
  refine ⟨⟨0, by simp [hps]⟩, (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
    ((chainModel C).key Q s) ((chainModel C).key Q e), by linarith, by rw [hpe]; exact T_unw _ _ _,
    rfl⟩

/-- The keys of a valid piece are keys of the walk. -/
theorem pcOK_keys {P : Polygon} {m₀ : ℕ → ℕ} {h γ : ℕ} {pc : Pc} (hp : PcOK P C m₀ h γ pc) :
    (0 ≤ (chainModel C).key (Qof P) pc.s ∧
      (chainModel C).key (Qof P) pc.s < ((2 * C.m + 7 : ℕ) : ℝ)) ∧
    (0 ≤ (chainModel C).key (Qof P) pc.e ∧
      (chainModel C).key (Qof P) pc.e < ((2 * C.m + 7 : ℕ) : ℝ)) :=
  ⟨key_range hp.1 hp.2.2.1, key_range hp.2.1 hp.2.2.2.1⟩

/-- The pieces of a path of walk vertices start and end at walk vertices. -/
theorem UPath.ends {n : ℕ} : ∀ {u : ℕ} {ps : List Pc} {u' : ℕ}, UPath n u ps u' →
    ∀ pc ∈ ps, pc.s.hgt = 0 ∧ pc.e.hgt = 0
  | _, [], _, _, _, h => by simp at h
  | _, _ :: _, _, ⟨h1, _, _, h2, h3⟩, pc, hpc => by
    rcases List.mem_cons.1 hpc with rfl | hpc
    · simp_all
    · exact UPath.ends h3 pc hpc

/-- **The general case**: the first piece to the walk vertex of `U₀`, the main loop from `U₀`
to `F`, and the last piece from the vertex of `F` to `e` (if `F < T`). -/
theorem arcOK_general {P : Polygon} {m₀ : ℕ → ℕ} {h γ : ℕ} {s e : WPos}
    (hs : ProperPos (chainModel C) (Qof P) P.n s) (he : ProperPos (chainModel C) (Qof P) P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7) {U₀ F : ℕ} {p₁ : Pc}
    {loop fin : List Pc} (hp₁s : p₁.s = s) (hp₁e : p₁.e = ⟨U₀ % (2 * C.m + 7), 0⟩)
    (hks : (chainModel C).key (Qof P) s < U₀) (hloop : UPath (2 * C.m + 7) U₀ loop F)
    (hfin : (fin = [pVE (F % (2 * C.m + 7)) e] ∧ (F : ℝ) < (chainModel C).key (Qof P) s +
        len ((2 * C.m + 7 : ℕ) : ℝ) ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e)) ∨
      (fin = [] ∧ (F : ℝ) = (chainModel C).key (Qof P) s +
        len ((2 * C.m + 7 : ℕ) : ℝ) ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e)))
    (hok : ∀ pc ∈ p₁ :: (loop ++ fin), PcOK P C m₀ h γ pc) :
    ArcOK C (Qof P) s e (p₁ :: (loop ++ fin)) := by
  set n := 2 * C.m + 7 with hn
  set M := chainModel C
  set Q := Qof P
  set ks := M.key Q s
  set ke := M.key Q e
  set T := ks + len (n : ℝ) ks ke with hT
  have hn0 : (0 : ℝ) < (n : ℝ) := by grind
  have kS := key_range hs hs1
  have kE := key_range he he1
  have hTle : T ≤ ks + n := by
    have := len_le (n : ℝ) ks ke kS.1 kE.2; linarith
  have hTu := T_unw ks ke (n : ℝ)
  -- the whole path of keys
  have hkU : ∀ u : ℕ, ∃ j : ℤ, (u : ℝ) = M.key Q ⟨u % n, 0⟩ + j * n := fun u => by
    refine ⟨((u / n : ℕ) : ℤ), ?_⟩
    rw [key_hgt0, Int.cast_natCast]
    have := Nat.mod_add_div u n
    have e : ((u % n : ℕ) : ℝ) + ((u / n : ℕ) : ℝ) * (n : ℝ) = (u : ℝ) := by
      exact_mod_cast (show u % n + u / n * n = u by grind)
    linarith
  have hfinP : KPath M Q (n : ℝ) (F : ℝ) fin T := by
    rcases hfin with ⟨rfl, hlt⟩ | ⟨rfl, heq⟩
    · exact ⟨hkU F, T, hlt, hTu, rfl⟩
    · exact heq
  have hkp : KPath M Q (n : ℝ) ks (p₁ :: (loop ++ fin)) T :=
    ⟨⟨0, by grind⟩, U₀, hks, by rw [hp₁e]; exact hkU U₀,
      (kpath_of_upath hloop).append fin hfinP⟩
  have hne : p₁ :: (loop ++ fin) ≠ [] := List.cons_ne_nil _ _
  -- the last key is the key of `e`
  have hlast : M.key Q ((p₁ :: (loop ++ fin)).getLast hne).e = ke := by
    obtain ⟨j, hj⟩ := KPath.last hkp hne
    obtain ⟨j', hj'⟩ := hTu
    have hb := (pcOK_keys (hok _ (List.getLast_mem hne))).2
    exact key_eq_of_unw hn0 hb kE (i := j) (j := j') (by grind)
  -- consecutive
  have hch : Chained s (p₁ :: (loop ++ fin)) ((p₁ :: (loop ++ fin)).getLast hne).e := by
    have hc : ∃ y, Chained s (p₁ :: (loop ++ fin)) y := by
      have hl := upath_chained hloop
      rcases hfin with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact ⟨e, hp₁s, by rw [hp₁e]; exact Chained.append' hl ⟨rfl, rfl⟩⟩
      · exact ⟨_, hp₁s, by rw [hp₁e, List.append_nil]; exact hl⟩
    obtain ⟨y, hy⟩ := hc
    rw [Chained.last hy hne]; exact hy
  refine ⟨hne, hp₁s, hlast, fun i hi => Chained.get hch i hi, fun i hi => ?_, hkp, ?_⟩
  swap
  · intro pc hpc
    rcases List.mem_cons.1 hpc with rfl | hpc
    · ram_grind
    rcases List.mem_append.1 hpc with hpc | hpc
    · have := UPath.ends hloop pc hpc; omega
    · rcases hfin with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · rw [List.mem_singleton] at hpc; subst hpc; exact ⟨Or.inr rfl, Or.inl rfl⟩
      grind
  have := e6_of_kpath hn0 hkp (by linarith) (fun pc hpc => pcOK_keys (hok pc hpc)) hne i hi
  grind

end ShootCut

end

end Chazelle.Core
