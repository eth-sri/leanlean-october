module

public import RequestProject.DavisChamberGluing

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

omit [Fintype V] in
theorem inChamber_rep (p : Sph A) : InChamber p.rep p := by
  rw [InChamber, inv_mul_cancel]; exact Subgroup.one_mem _

theorem mem_shorter_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, RACG.clen A y < RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  refine ⟨fun ⟨y, hlt, hy⟩ => (mem_earlier_chamber_iff hp).1 ⟨y, fun hxy => by rw [hxy] at hlt; omega, le_of_lt hlt, hy⟩,
    fun ⟨s, hs⟩ => ?_⟩
  obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
  obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A (T := (p.spx : Set V)) (Finset.mem_coe.2 hsσ)
    ((mem_rdescFinset A).1 hsd)
  refine ⟨x * gen A s, h3, ?_⟩
  rw [InChamber, show p.rep⁻¹ * (x * gen A s) = (p.rep⁻¹ * x) * (x⁻¹ * (x * gen A s)) by group]
  exact Subgroup.mul_mem _ hp h1

def Upto (n : ℕ) (p : Sph A) : Prop := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InChamber y p

omit [Fintype V] in
theorem upto_up {n : ℕ} {p q : Sph A} (hpq : p ≤ q) : Upto n p → Upto n q
  | ⟨y, hy, hyp⟩ => ⟨y, hy, inChamber_of_le hpq hyp⟩

omit [Fintype V] in
theorem upto_zero_iff (p : Sph A) : Upto 0 p ↔ InChamber 1 p :=
  ⟨fun ⟨y, hy, hyp⟩ => (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 hy) ▸ hyp,
   fun h => ⟨1, by simp, h⟩⟩

theorem level_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x = n}.Finite := by
  refine Set.Finite.subset ((List.finite_length_le V n).image (cword A)) fun x (hx : RACG.clen A x = n) => ?_
  obtain ⟨l, hl, hlx⟩ := exists_cword A x
  exact ⟨l, by simpa [← hx, ← hlx, clen_cword A hl] using le_rfl, hlx⟩

theorem nullIn_upto (A : CommRel V) (n : ℕ) :
    NullIn (Upto (A := A) n) ∧ ConnectedIn (Upto (A := A) n) := by
  induction n with
  | zero =>
      exact ⟨nullIn_congr (fun p => (upto_zero_iff p).symm) (nullIn_chamber 1),
        connectedIn_congr (fun p => (upto_zero_iff p).symm) (connectedIn_chamber 1)⟩
  | succ n ih =>
      have hins : ∀ (S : Set (CayGroup A)), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
          NullIn (fun p : Sph A => Upto n p ∨ ∃ y ∈ S, InChamber y p) ∧
            ConnectedIn (fun p : Sph A => Upto n p ∨ ∃ y ∈ S, InChamber y p) := by
        intro S hS
        induction S, hS using Set.Finite.induction_on with
        | empty =>
            exact fun _ => ⟨nullIn_congr (fun p => by simp [Upto]) ih.1,
              connectedIn_congr (fun p => by simp [Upto]) ih.2⟩
        | @insert x S hxS _ ihS =>
            intro hlen
            obtain ⟨hprevNull, hprevConn⟩ := ihS fun y hy => hlen y (Set.mem_insert_of_mem _ hy)
            have hxlen : RACG.clen A x = n + 1 := hlen x (Set.mem_insert _ _)
            have hx1 : x ≠ 1 := fun h => by rw [h] at hxlen; simp at hxlen
            let Prev : Sph A → Prop := fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p
            obtain ⟨hN, hC⟩ := nullIn_union_chamber hx1 Prev
              (by rintro p q hpq (h | ⟨y, hy, hyp⟩); exacts [.inl (upto_up hpq h), .inr ⟨y, hy, inChamber_of_le hpq hyp⟩])
              hprevNull hprevConn fun p =>
                ⟨by rintro ⟨⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩, hpx⟩
                    · exact ⟨hpx, (mem_shorter_chamber_iff hpx).1 ⟨y, by omega, hyp⟩⟩
                    · exact ⟨hpx, (mem_earlier_chamber_iff hpx).1
                        ⟨y, fun hxy => hxS (hxy ▸ hyS), by rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen], hyp⟩⟩,
                 fun ⟨hpx, hne⟩ =>
                    let ⟨y, hylt, hyp⟩ := (mem_shorter_chamber_iff hpx).2 hne
                    ⟨.inl ⟨y, by omega, hyp⟩, hpx⟩⟩
            have hiff (p : Sph A) : (Prev p ∨ InChamber x p) ↔ (Upto n p ∨ ∃ y ∈ insert x S, InChamber y p) :=
              ⟨by rintro ((h | ⟨y, hy, hyp⟩) | h)
                  exacts [.inl h, .inr ⟨y, Set.mem_insert_of_mem _ hy, hyp⟩, .inr ⟨x, Set.mem_insert _ _, h⟩],
               by rintro (h | ⟨y, hy, hyp⟩)
                  · exact .inl (.inl h)
                  · rcases Set.mem_insert_iff.1 hy with rfl | hy
                    exacts [.inr hyp, .inl (.inr ⟨y, hy, hyp⟩)]⟩
            exact ⟨nullIn_congr hiff hN, connectedIn_congr hiff hC⟩
      obtain ⟨hN, hC⟩ := hins {x : CayGroup A | RACG.clen A x = n + 1} (level_finite A (n + 1)) fun _ hy => hy
      have hiff (p : Sph A) :
          (Upto n p ∨ ∃ y ∈ {x : CayGroup A | RACG.clen A x = n + 1}, InChamber y p) ↔ Upto (n + 1) p :=
        ⟨by rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩); exacts [⟨y, by omega, hyp⟩, ⟨y, le_of_eq hy, hyp⟩],
         fun ⟨y, hy, hyp⟩ => (Nat.lt_or_ge (RACG.clen A y) (n + 1)).elim
            (fun h => .inl ⟨y, by omega, hyp⟩) fun h => .inr ⟨y, le_antisymm hy h, hyp⟩⟩
      exact ⟨nullIn_congr hiff hN, connectedIn_congr hiff hC⟩

theorem simplyConnected_davis (A : CommRel V) : SimplyConnected (orderCx (Sph A)) := by
  intro v l hp
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      let bnd := ((e :: t).map fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep).sum
      have hin : PathIn (Upto (A := A) bnd) (e :: t) := fun e' he' => by
        have hle := List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map_of_mem (f := fun e : (orderCx (Sph A)).E × Bool => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep) he')
        exact ⟨⟨(e'.1.1.1).rep, by omega, inChamber_rep _⟩, ⟨(e'.1.1.2).rep, by omega, inChamber_rep _⟩⟩
      have hv : Upto bnd v := by
        obtain ⟨hstart, -⟩ := hp
        obtain ⟨he, -⟩ := pathIn_of_cons hin
        rcases e with ⟨_, false | true⟩ <;> rw [hstart] <;> [exact he.2; exact he.1]
      exact (nullIn_upto A bnd).1 v (e :: t) hv hp hin

theorem isConnected_davis (A : CommRel V) : IsConnected (orderCx (Sph A)) := by
  intro p q
  obtain ⟨l, hl, -⟩ := (nullIn_upto A (RACG.clen A p.rep + RACG.clen A q.rep)).2 p q
    ⟨p.rep, by omega, inChamber_rep _⟩ ⟨q.rep, by omega, inChamber_rep _⟩
  exact ⟨l, hl⟩
