module

public import Chazelle.Ears.Basic
public import Chazelle.Existence.Diagonal

/-!
# Existence of ears

Every simple polygon with at least four vertices has an ear (`exists_ear`).

The route follows the "ears in every chain" argument: for every interior diagonal `(s, L)` of
`P` some vertex strictly inside the chain `s, …, s + L` is the apex of an ear
(`exists_ear_in_arc`).  Strong induction on the number of vertices: if `L = 2` the apex is
`s + 1`; otherwise the arc `A = P.arc s L` has at least four vertices, so it has an interior
diagonal, and the induction hypothesis applied to that diagonal of `A` and to its complement
gives ear apexes of `A` strictly inside the two chains of that diagonal.  Two such apexes are
never adjacent in `A`, so they cannot both be endpoints `0`, `L` of the closing chord, and an
ear of `A` at an apex `k` with `0 < k < L` lifts to an ear of `P` at `s + k`
(`isEar_of_arc`): its chord avoids the boundary of `A` by assumption and the boundary of the
complementary arc because the filled regions of the two arcs meet only on the chord.
-/

namespace Chazelle.Ears

@[expose] public section

open Chazelle.Jordan
open Chazelle.Existence

variable (P : Polygon)

/-- A diagonal `(s, 2)` with its chord inside `P` is an ear at `(s + 1) % n`. -/
theorem isEar_of_diagonal_two {s : ℕ} (hd : IsDiagonal P s 2)
    (hin : Chazelle.segment (P.vtx (s % P.n)) (P.vtx ((s + 2) % P.n)) ⊆ P.filled) :
    IsEar P ((s + 1) % P.n) := by
  have hn : 0 < P.n := by have := hd.2.1; omega
  refine ⟨?_, ?_⟩
  · rw [prevIdx_succ_mod P hn, isDiagonal_mod_iff]; exact hd
  · rw [prevIdx_succ_mod P hn, mod_add_one_mod]; exact hin

/-- The filled region of an arc of an interior diagonal lies in the filled region of `P`. -/
theorem filled_arc_subset {s L : ℕ} (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : Chazelle.segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled) :
    (P.arc s L).filled ⊆ P.filled := by
  rw [filled_eq_union_arcs P s L hP hd hin]; exact Set.subset_union_left

/-- **Lifting an ear from an arc.**  Let `(s, L)` be an interior diagonal of `P` and `A = P.arc s L`.
An ear of `A` at an apex `k` with `0 < k < L` is an ear of `P` at `(s + k) % n`. -/
theorem isEar_of_arc {s L : ℕ} (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : Chazelle.segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled)
    {k : ℕ} (hk0 : 0 < k) (hkL : k < L) (he : IsEar (P.arc s L) k) :
    IsEar P ((s + k) % P.n) := by
  have hLn : L + 2 ≤ P.n := hd.2.1
  have hn : 0 < P.n := by omega
  have hL : L ≤ P.n := by omega
  have hAn : (P.arc s L).n = L + 1 := n_arc P s L
  have h4 : 4 ≤ (P.arc s L).n := he.1.2.1
  have hprev : prevIdx (P.arc s L) k = k - 1 := by
    rw [prevIdx_eq _ (by omega)]; simp [Nat.pos_iff_ne_zero.1 hk0]
  have e1 : (P.arc s L).vtx (prevIdx (P.arc s L) k) = P.vtx ((s + (k - 1)) % P.n) := by
    rw [hprev, vtx_arc P s L (by omega)]
  have e2 : (P.arc s L).vtx ((k + 1) % (P.arc s L).n) = P.vtx ((s + (k - 1) + 2) % P.n) := by
    rw [hAn, Nat.mod_eq_of_lt (by omega), vtx_arc P s L (by omega)]
    congr 2; omega
  -- the ear chord of `A`, avoiding the boundary of `A` and lying in `A.filled`
  have hch := he.1.2.2
  rw [hprev, hAn, Nat.mod_eq_of_lt (by omega : k - 1 < L + 1),
    Nat.mod_eq_of_lt (by omega : k - 1 + 2 < L + 1), vtx_arc P s L (by omega),
    vtx_arc P s L (by omega), ← Nat.add_assoc] at hch
  have hsub := he.2
  rw [e1, e2] at hsub
  have hkey : IsEar P ((s + (k - 1) + 1) % P.n) := by
    apply isEar_of_diagonal_two
    · refine ⟨le_rfl, by omega, ?_⟩
      intro p hp hp1 hp2 hpB
      have hpA : p ∉ (P.arc s L).boundary := hch p hp hp1 hp2
      rcases boundary_subset_arcs P s L hL hn hpB with h | h
      · exact hpA h
      · have hpf : p ∈ Chazelle.segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) :=
          filled_arcs_meet_on_chord P s L hP hd hin p (hsub hp) (Jordan.boundary_subset_filled _ h)
        rw [segment_comm] at hpf
        exact hpA (chord_subset_boundary_arc P s L hpf)
    · exact hsub.trans (filled_arc_subset P hP hd hin)
  rw [show s + (k - 1) + 1 = s + k by omega] at hkey
  exact hkey

/-- **Two apexes strictly inside opposite chains of a diagonal are never adjacent.**  Index
arithmetic modulo `N = L + 1`: for a diagonal `(s', L')` of a polygon with `N` vertices, and
apexes `s' + k₁` (`0 < k₁ < L'`) and `s' + L' + k₂` (`0 < k₂ < N - L'`), not both apexes lie in
`{0, L}`. -/
theorem apex_not_both_endpoints {N L s' L' k₁ k₂ : ℕ} (hN : N = L + 1)
    (hk₁0 : 0 < k₁) (hk₁ : k₁ < L') (hk₂0 : 0 < k₂) (hk₂ : k₂ < N - L') (hL' : L' + 2 ≤ N) :
    (0 < (s' + k₁) % N ∧ (s' + k₁) % N < L) ∨
      (0 < (s' + (L' + k₂)) % N ∧ (s' + (L' + k₂)) % N < L) := by
  have hN0 : 0 < N := by omega
  have ha₁ : (s' + k₁) % N < N := Nat.mod_lt _ hN0
  have ha₂ : (s' + (L' + k₂)) % N < N := Nat.mod_lt _ hN0
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have c₁ : (s' + k₁) % N = 0 ∨ (s' + k₁) % N = L := by omega
  have c₂ : (s' + (L' + k₂)) % N = 0 ∨ (s' + (L' + k₂)) % N = L := by omega
  rcases c₁ with c₁ | c₁ <;> rcases c₂ with c₂ | c₂
  · -- equal apexes
    have := rot_index_inj (n := N) (s := s') (i := k₁) (j := L' + k₂) (by omega) (by omega)
      (by rw [c₁, c₂])
    omega
  · -- `a₁ = 0` is the successor of `a₂ = L`
    have e : (s' + (L' + k₂ + 1)) % N = (s' + k₁) % N := by
      rw [← mod_add_one_mod, c₂, c₁, hN, Nat.mod_self]
    rcases Nat.lt_or_ge (L' + k₂ + 1) N with h | h
    · have := rot_index_inj (n := N) (s := s') h (by omega) e
      omega
    · have hEq : L' + k₂ + 1 = N := by omega
      rw [hEq, Nat.add_mod_right] at e
      have := rot_index_inj (n := N) (s := s') (i := 0) (j := k₁) hN0 (by omega)
        (by rw [Nat.add_zero]; exact e)
      omega
  · -- `a₂ = 0` is the successor of `a₁ = L`
    have e : (s' + (k₁ + 1)) % N = (s' + (L' + k₂)) % N := by
      rw [← mod_add_one_mod, c₁, c₂, hN, Nat.mod_self]
    have := rot_index_inj (n := N) (s := s') (i := k₁ + 1) (j := L' + k₂) (by omega) (by omega) e
    omega
  · -- equal apexes
    have := rot_index_inj (n := N) (s := s') (i := k₁) (j := L' + k₂) (by omega) (by omega)
      (by rw [c₁, c₂])
    omega

/-- **Ears in every chain** (auxiliary form, for the strong induction on the number of
vertices).  For every interior diagonal `(s, L)` of a simple polygon with `m` vertices, some
vertex strictly inside the chain `s, …, s + L` is the apex of an ear. -/
theorem exists_ear_in_arc_aux (m : ℕ) : ∀ Q : Polygon, Q.n = m → Q.Simple → ∀ s L : ℕ,
    IsDiagonal Q s L → Chazelle.segment (Q.vtx (s % Q.n)) (Q.vtx ((s + L) % Q.n)) ⊆ Q.filled →
    ∃ k, 0 < k ∧ k < L ∧ IsEar Q ((s + k) % Q.n) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Q hQm hQ s L hd hin
  rcases eq_or_lt_of_le hd.1 with hL2 | hL3
  · -- `L = 2`: the apex is `s + 1`
    subst hL2
    exact ⟨1, one_pos, one_lt_two, isEar_of_diagonal_two Q hd hin⟩
  · -- `L ≥ 3`: cut the arc along a diagonal
    set A := Q.arc s L with hAdef
    have hA : A.Simple := simple_arc Q s L hQ hd
    have hAn : A.n = L + 1 := n_arc Q s L
    have hA4 : 4 ≤ A.n := by omega
    have hAm : A.n < m := by have := hd.2.1; omega
    obtain ⟨s', L', hd', hin'⟩ := exists_diagonal hA hA4
    obtain ⟨k₁, hk₁0, hk₁, he₁⟩ := ih A.n hAm A rfl hA s' L' hd' hin'
    have hd'' := isDiagonal_compl A s' L' hd'
    have hL'n : L' ≤ A.n := by have := hd'.2.1; omega
    have hin'' : Chazelle.segment (A.vtx ((s' + L') % A.n % A.n))
        (A.vtx (((s' + L') % A.n + (A.n - L')) % A.n)) ⊆ A.filled := by
      rw [Nat.mod_mod, compl_arc_last_index A s' L' hL'n, segment_comm]; exact hin'
    obtain ⟨k₂, hk₂0, hk₂, he₂⟩ := ih A.n hAm A rfl hA _ _ hd'' hin''
    rw [compl_arc_index, Nat.add_assoc] at he₂
    rcases apex_not_both_endpoints hAn hk₁0 hk₁ hk₂0 hk₂ hd'.2.1 with ⟨h0, hL⟩ | ⟨h0, hL⟩
    · exact ⟨_, h0, hL, isEar_of_arc Q hQ hd hin h0 hL he₁⟩
    · exact ⟨_, h0, hL, isEar_of_arc Q hQ hd hin h0 hL he₂⟩

/-- **Ears in every chain.**  For every interior diagonal `(s, L)` of a simple polygon `P`,
some vertex `(s + k) % n` with `0 < k < L` (strictly inside the chain `s, …, s + L`) is the
apex of an ear. -/
theorem exists_ear_in_arc {s L : ℕ} (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : Chazelle.segment (P.vtx (s % P.n)) (P.vtx ((s + L) % P.n)) ⊆ P.filled) :
    ∃ k, 0 < k ∧ k < L ∧ IsEar P ((s + k) % P.n) :=
  exists_ear_in_arc_aux P.n P rfl hP s L hd hin

end

end Chazelle.Ears
