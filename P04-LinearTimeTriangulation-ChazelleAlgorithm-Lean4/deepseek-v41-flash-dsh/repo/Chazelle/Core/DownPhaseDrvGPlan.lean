module

public import Chazelle.Core.DownPhaseDrvRPlD

/-!
# Down-phase driver, region procedure (D5), part 1: the gaps between the leaves

The pieces of a region chain `⟨H.poly Q, 0, M⟩` (`M + 1` host points) are the leaves
`hostLeaves n C 0 H` (`DownPhaseDrvRPc`) and the connectors, the non-empty gaps between
consecutive leaves (and before the first, after the last).  `GapsLe B L e M`: the leaves `L` are
ordered from `e` on and every gap is at most `B` edges.

* `chunks_gaps`, `runLeaves_gaps`: the leaves of a run start at most `2` points after its first
  point, end at most `2` before its last, and leave gaps of at most one edge (the wrap-around
  edge `v_{n-1} v_0`); a run without leaves has at most `3` points unless it is *degenerate*
  (`.run (n - 2) 3`, whose only interior edge is the wrap-around edge);
* `hostLeaves_gaps`: a host of at most `20` items with at most one degenerate run has gaps of at
  most `64` edges;
* `degCount_le_one`: a simple host polygon has at most one degenerate run (both would contain the
  vertex `v_{n-1}`);
* `hostLeaves_length_le`: at most `3` leaves per run of at most `2 C` edges.
-/

namespace Chazelle.Core

namespace DrvG

open DrvR

@[expose] public section

/-! ## Gaps -/

/-- **The gaps of a leaf list**: the leaves are ordered from `e` on, each starts at most `B`
edges after the end of the previous one (or `e`), and `M` is at most `B` edges after the end of
the last one. -/
def GapsLe (B : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Prop
  | [], e, M => e ≤ M ∧ M ≤ e + B
  | x :: L, e, M => e ≤ x.1 ∧ x.1 ≤ e + B ∧ GapsLe B L (x.1 + x.2.1) M

/-- The end of the last leaf (`e` if none). -/
def lastEnd : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], e => e
  | x :: L, _ => lastEnd L (x.1 + x.2.1)

theorem gapsLe_append {B : ℕ} : ∀ (L₁ L₂ : List (ℕ × ℕ × ℕ)) (e M M₁ : ℕ),
    GapsLe B L₁ e M₁ → GapsLe B L₂ (lastEnd L₁ e) M → GapsLe B (L₁ ++ L₂) e M
  | [], _L₂, _e, _M, _M₁, _, h₂ => h₂
  | x :: L₁, L₂, _e, M, M₁, ⟨h1, h2, h3⟩, h₂ =>
    ⟨h1, h2, gapsLe_append L₁ L₂ (x.1 + x.2.1) M M₁ h3 h₂⟩

theorem gapsLe_mono {B B' : ℕ} (hB : B ≤ B') : ∀ (L : List (ℕ × ℕ × ℕ)) (e M : ℕ),
    GapsLe B L e M → GapsLe B' L e M
  | [], e, M, ⟨h1, h2⟩ => ⟨h1, by omega⟩
  | x :: L, e, M, ⟨h1, h2, h3⟩ => ⟨h1, by omega, gapsLe_mono hB L _ M h3⟩

theorem lastEnd_append : ∀ (L₁ L₂ : List (ℕ × ℕ × ℕ)) (e : ℕ),
    lastEnd (L₁ ++ L₂) e = lastEnd L₂ (lastEnd L₁ e)
  | [], _, _ => rfl
  | x :: L₁, L₂, _ => lastEnd_append L₁ L₂ (x.1 + x.2.1)

/-- **The pieces of a segment** from `s`, contiguous, ending at `s + L`, seen from any `e ≤ s`
at most `B` edges before `s`. -/
theorem chunks_gaps {C : ℕ} (hC : 1 ≤ C) : ∀ (L s a e B : ℕ), 1 ≤ L → e ≤ s → s ≤ e + B →
    GapsLe B (chunks C s a L) e (s + L) ∧ lastEnd (chunks C s a L) e = s + L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s a e B hL he hB
    rw [chunks_cons hC hL]
    by_cases h : L ≤ C
    · rw [min_eq_right h, Nat.sub_self, chunks_zero]
      refine ⟨⟨he, hB, ?_, ?_⟩, rfl⟩ <;> simp only <;> omega
    · rw [min_eq_left (by omega)]
      obtain ⟨h1, h2⟩ := ih (L - C) (by omega) (s + C) (a + C) (s + C) B (by omega) (le_refl _)
        (by omega)
      rw [show s + C + (L - C) = s + L by omega] at h1 h2
      exact ⟨⟨he, hB, h1⟩, h2⟩

/-- A run is **degenerate** when its only interior edge is the wrap-around edge
`v_{n-1} v_0`. -/
def Degen (n a ℓ : ℕ) : Prop := ℓ = 3 ∧ (a + 1) % n = n - 1

instance (n a ℓ : ℕ) : Decidable (Degen n a ℓ) := by unfold Degen; infer_instance

/-- **The leaves of a run**: none if the run is short or degenerate; otherwise they start at
most two points after the first point of the run, are separated by at most one edge, and end at
most two points before its last point. -/
theorem runLeaves_gaps {n C p a ℓ : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) (hℓ : ℓ < n) :
    (runLeaves n C p a ℓ = [] ∧ (ℓ < 3 ∨ Degen n a ℓ)) ∨
      (3 ≤ ℓ ∧ ¬ Degen n a ℓ ∧ ∀ e, e ≤ p + 1 →
        GapsLe (p + 2 - e) (runLeaves n C p a ℓ) e (lastEnd (runLeaves n C p a ℓ) e) ∧
        p + ℓ - 2 ≤ lastEnd (runLeaves n C p a ℓ) e ∧
        lastEnd (runLeaves n C p a ℓ) e ≤ p + ℓ - 1) := by
  have hu : (a + 1) % n < n := Nat.mod_lt _ (by omega)
  by_cases h3 : ℓ < 3
  · left; exact ⟨by unfold runLeaves; rw [ite_eq_left h3], Or.inl h3⟩
  by_cases hdg : Degen n a ℓ
  · left
    refine ⟨?_, Or.inr hdg⟩
    obtain ⟨hl, hm⟩ := hdg
    unfold runLeaves
    rw [ite_eq_right h3, ite_eq_right (by omega), hm, show n - 1 - (n - 1) = 0 by omega, chunks_zero,
      show ℓ - 2 - (n - (n - 1)) = 0 by omega, chunks_zero]
    rfl
  right
  refine ⟨by omega, hdg, fun e he => ?_⟩
  have hDg : ¬ (ℓ = 3 ∧ (a + 1) % n = n - 1) := hdg
  unfold runLeaves
  rw [ite_eq_right h3]
  split_ifs with hw
  · obtain ⟨g1, g2⟩ := chunks_gaps hC (ℓ - 2) (p + 1) ((a + 1) % n) e (p + 2 - e) (by omega) he
      (by omega)
    rw [g2]
    exact ⟨g1, by omega, by omega⟩
  · by_cases h1 : n - 1 - (a + 1) % n = 0
    · have h2 : 1 ≤ ℓ - 2 - (n - (a + 1) % n) := by omega
      rw [h1, chunks_zero, List.nil_append]
      obtain ⟨g1, g2⟩ := chunks_gaps hC (ℓ - 2 - (n - (a + 1) % n)) (p + 1 + (n - (a + 1) % n)) 0
        e (p + 2 - e) h2 (by omega) (by omega)
      rw [g2]
      exact ⟨g1, by omega, by omega⟩
    · obtain ⟨g1, g2⟩ := chunks_gaps hC (n - 1 - (a + 1) % n) (p + 1) ((a + 1) % n) e (p + 2 - e)
        (by omega) he (by omega)
      by_cases h2 : ℓ - 2 - (n - (a + 1) % n) = 0
      · rw [h2, chunks_zero, List.append_nil, g2]
        exact ⟨g1, by omega, by omega⟩
      · obtain ⟨k1, k2⟩ := chunks_gaps hC (ℓ - 2 - (n - (a + 1) % n)) (p + 1 + (n - (a + 1) % n)) 0
          (p + 1 + (n - 1 - (a + 1) % n)) (p + 2 - e) (by omega) (by omega) (by omega)
        have hl : lastEnd (chunks C (p + 1) ((a + 1) % n) (n - 1 - (a + 1) % n) ++
            chunks C (p + 1 + (n - (a + 1) % n)) 0 (ℓ - 2 - (n - (a + 1) % n))) e =
            p + 1 + (n - (a + 1) % n) + (ℓ - 2 - (n - (a + 1) % n)) := by
          rw [lastEnd_append, g2, k2]
        rw [hl]
        refine ⟨gapsLe_append _ _ e _ _ g1 ?_, by omega, by omega⟩
        rw [g2]; exact k1

/-! ## The gaps of a host -/

/-- The number of degenerate runs of a host. -/
def degCount (n : ℕ) : Host → ℕ
  | [] => 0
  | .run a ℓ :: H => (if Degen n a ℓ then 1 else 0) + degCount n H
  | .pt _ :: H => degCount n H

theorem hostLeaves_gapsG {n C : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) : ∀ (H : Host) (p e k d : ℕ),
    HostWF n H → e ≤ p → p ≤ e + 3 * k + d + 3 → k + H.length ≤ 20 → d + degCount n H ≤ 1 →
    e + 1 ≤ p + (H.pts n).length →
    GapsLe 64 (hostLeaves n C p H) e (p + (H.pts n).length - 1)
  | [], p, e, k, d, _, h1, h2, h3, h4, h5 => by
    simp only [hostLeaves, Host.pts, List.flatMap_nil, List.length_nil, Nat.add_zero] at h5 ⊢
    simp only [List.length_nil] at h3
    exact ⟨by omega, by omega⟩
  | .pt x :: H, p, e, k, d, hwf, h1, h2, h3, h4, h5 => by
    have hwf' : HostWF n H := fun it h => hwf it (List.mem_cons_of_mem _ h)
    have hl : (Host.pts n (HostItem.pt x :: H)).length = (Host.pts n H).length + 1 := by
      rw [DownMath.pts_cons, List.length_append]; simp [HostItem.pts]; omega
    rw [hl] at h5 ⊢
    simp only [List.length_cons] at h3
    simp only [degCount] at h4
    rw [hostLeaves, show p + ((Host.pts n H).length + 1) - 1 = p + 1 + (Host.pts n H).length - 1 by
      omega]
    exact hostLeaves_gapsG hC hn H (p + 1) e (k + 1) d hwf' (by omega) (by omega) (by omega) h4
      (by omega)
  | .run a ℓ :: H, p, e, k, d, hwf, h1, h2, h3, h4, h5 => by
    have hwf' : HostWF n H := fun it h => hwf it (List.mem_cons_of_mem _ h)
    have hit := hwf (.run a ℓ) (List.mem_cons_self ..)
    simp only at hit
    have hl : (Host.pts n (HostItem.run a ℓ :: H)).length = (Host.pts n H).length + ℓ + 1 := by
      rw [DownMath.pts_cons, List.length_append, DownMath.run_pts_length]; omega
    rw [hl] at h5 ⊢
    simp only [List.length_cons] at h3
    simp only [degCount] at h4
    rw [hostLeaves, show p + ((Host.pts n H).length + ℓ + 1) - 1 =
      p + ℓ + 1 + (Host.pts n H).length - 1 by omega]
    rcases runLeaves_gaps (p := p) hC hn hit.2 with ⟨he, hsh⟩ | ⟨h3l, hdg, hg⟩
    · rw [he, List.nil_append]
      have hd : ℓ + 1 ≤ 3 + (if Degen n a ℓ then 1 else 0) := by
        rcases hsh with h | hdg'
        · split_ifs <;> omega
        · rw [ite_eq_left hdg']; have := hdg'.1; omega
      exact hostLeaves_gapsG hC hn H (p + ℓ + 1) e (k + 1) (d + if Degen n a ℓ then 1 else 0)
        hwf' (by omega) (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨g1, g2, g3⟩ := hg e (by omega)
      rw [ite_eq_right hdg] at h4
      refine gapsLe_append _ _ e _ _ (gapsLe_mono (by omega) _ _ _ g1) ?_
      exact hostLeaves_gapsG hC hn H (p + ℓ + 1) _ 0 d hwf' (by omega) (by omega) (by omega)
        (by omega) (by omega)

/-- **The gaps of a host** of at most `20` items with at most one degenerate run are at most `64`
edges. -/
theorem hostLeaves_gaps {n C : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) {H : Host} (hwf : HostWF n H)
    (hl : H.length ≤ 20) (hd : degCount n H ≤ 1) (hp : 1 ≤ (H.pts n).length) :
    GapsLe 64 (hostLeaves n C 0 H) 0 ((H.pts n).length - 1) := by
  have := hostLeaves_gapsG hC hn H 0 0 0 0 hwf (le_refl _) (by omega) (by omega) (by omega)
    (by omega)
  simpa using this

/-! ## At most one degenerate run -/

theorem degCount_first (n : ℕ) : ∀ H : Host, 1 ≤ degCount n H →
    ∃ H₁ a ℓ H₂, H = H₁ ++ HostItem.run a ℓ :: H₂ ∧ Degen n a ℓ ∧
      degCount n H₂ + 1 = degCount n H
  | [], h => by simp [degCount] at h
  | .pt x :: H, h => by
    simp only [degCount] at h
    obtain ⟨H₁, a, ℓ, H₂, e, hd, hc⟩ := degCount_first n H h
    exact ⟨.pt x :: H₁, a, ℓ, H₂, by rw [e]; rfl, hd, by simp only [degCount]; omega⟩
  | .run a ℓ :: H, h => by
    simp only [degCount] at h ⊢
    by_cases hd : Degen n a ℓ
    · exact ⟨[], a, ℓ, H, rfl, hd, by rw [ite_eq_left hd]; omega⟩
    · rw [ite_eq_right hd] at h
      obtain ⟨H₁, a', ℓ', H₂, e, hd', hc⟩ := degCount_first n H (by omega)
      exact ⟨.run a ℓ :: H₁, a', ℓ', H₂, by rw [e]; rfl, hd', by rw [ite_eq_right hd]; omega⟩

/-- **A simple host polygon has at most one degenerate run** (two would both contain the vertex
`v_{n-1}`). -/
theorem degCount_le_one {Q : Polygon} {H : Host} (hS : (H.poly Q).Simple) :
    degCount Q.n H ≤ 1 := by
  by_contra hc
  obtain ⟨H₁, a, ℓ, H₂, e₁, hd, hc₁⟩ := degCount_first Q.n H (by omega)
  have h₂ : 1 ≤ degCount Q.n H₂ := by omega
  subst e₁
  obtain ⟨H₃, a', ℓ', H₄, rfl, hd', -⟩ := degCount_first Q.n H₂ h₂
  obtain ⟨hl, hm⟩ := hd
  obtain ⟨hl', hm'⟩ := hd'
  subst hl hl'
  set G := H₁ ++ HostItem.run a 3 :: (H₃ ++ HostItem.run a' 3 :: H₄) with hG
  have hG' : G = (H₁ ++ HostItem.run a 3 :: H₃) ++ HostItem.run a' 3 :: H₄ := by
    rw [hG]; simp
  have p1 := DownMath.pts_append_run Q.n H₁ (H₃ ++ HostItem.run a' 3 :: H₄) a 3
    (k := 1) (by omega)
  have p2 := DownMath.pts_append_run Q.n (H₁ ++ HostItem.run a 3 :: H₃) H₄ a' 3
    (k := 1) (by omega)
  rw [← hG] at p1; rw [← hG'] at p2
  have l1 := DownMath.pts_append_run_length Q.n H₁ (H₃ ++ HostItem.run a' 3 :: H₄) a 3
  have l2 := DownMath.pts_append_run_length Q.n (H₁ ++ HostItem.run a 3 :: H₃) H₄ a' 3
  rw [← hG] at l1; rw [← hG'] at l2
  have l3 : (H₁.pts Q.n).length + 4 ≤ ((H₁ ++ HostItem.run a 3 :: H₃).pts Q.n).length := by
    rw [DownMath.pts_append, DownMath.pts_cons, List.length_append, List.length_append,
      DownMath.run_pts_length]; omega
  have v1 := DownMath.host_poly_vtx Q G (i := (H₁.pts Q.n).length + 1) (by omega)
  have v2 := DownMath.host_poly_vtx Q G
    (i := ((H₁ ++ HostItem.run a 3 :: H₃).pts Q.n).length + 1) (by omega)
  rw [p1, hm] at v1
  rw [p2, hm'] at v2
  have := hS.2.1 _ _ (by rw [DownMath.host_poly_n]; omega) (by rw [DownMath.host_poly_n]; omega)
    (v1.trans v2.symm)
  omega

/-! ## The number of leaves -/

theorem runLeaves_length_le {n C p a ℓ : ℕ} (hC : 1 ≤ C) (hℓ : ℓ ≤ 2 * C) :
    (runLeaves n C p a ℓ).length ≤ 3 := by
  unfold runLeaves
  split_ifs with h3 hw
  · simp
  · have := chunks_length hC (ℓ - 2) (p + 1) ((a + 1) % n)
    have h : (chunks C (p + 1) ((a + 1) % n) (ℓ - 2)).length * C < 4 * C := by omega
    have := Nat.lt_of_mul_lt_mul_right h
    omega
  · rw [List.length_append]
    have h1 := chunks_length hC (n - 1 - (a + 1) % n) (p + 1) ((a + 1) % n)
    have h2 := chunks_length hC (ℓ - 2 - (n - (a + 1) % n)) (p + 1 + (n - (a + 1) % n)) 0
    have h : ((chunks C (p + 1) ((a + 1) % n) (n - 1 - (a + 1) % n)).length +
        (chunks C (p + 1 + (n - (a + 1) % n)) 0 (ℓ - 2 - (n - (a + 1) % n))).length) * C <
        4 * C := by rw [Nat.add_mul]; omega
    have := Nat.lt_of_mul_lt_mul_right h
    omega

/-- **At most three leaves per run** of at most `2 C` edges. -/
theorem hostLeaves_length_le {n C : ℕ} (hC : 1 ≤ C) : ∀ (H : Host) (p : ℕ),
    (∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * C) → (hostLeaves n C p H).length ≤ 3 * H.length
  | [], _, _ => by simp [hostLeaves]
  | .pt x :: H, p, h => by
    rw [hostLeaves, List.length_cons]
    have := hostLeaves_length_le (n := n) hC H (p + 1)
      fun a ℓ hm => h a ℓ (List.mem_cons_of_mem _ hm)
    omega
  | .run a ℓ :: H, p, h => by
    rw [hostLeaves, List.length_append, List.length_cons]
    have h1 := runLeaves_length_le (n := n) (p := p) (a := a) hC (h a ℓ (List.mem_cons_self ..))
    have := hostLeaves_length_le (n := n) hC H (p + ℓ + 1)
      fun a ℓ hm => h a ℓ (List.mem_cons_of_mem _ hm)
    omega

end

end DrvG

end Chazelle.Core
