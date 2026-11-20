module

public import Mathlib

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Set Algebra

/-- Extend the graph of a positive additive state on an order unit. A maximal
positive graph can be extended in every direction bounded by the unit: the
allowable values form an interval cut out by integer multiples. -/
private theorem positive_graph {G : Type*} [AddCommGroup G] (C : AddSubmonoid G) (u : G)
    (hu : ∀ n : ℤ, n • u ∈ C → 0 ≤ n) :
    ∃ A : AddSubgroup (G × ℝ), (u,1) ∈ A ∧ (∀ p ∈ A, p.1 ∈ C → 0 ≤ p.2) ∧
      ∀ x (m n : ℕ), m • u + x ∈ C → n • u - x ∈ C → ∃ t, (x,t) ∈ A := by
  let P := {A : AddSubgroup (G × ℝ) | ∀ p ∈ A, p.1 ∈ C → 0 ≤ p.2}
  obtain ⟨A, hunit, hA⟩ := zorn_le_nonempty₀ P (by
    intro c hc hc' a ha
    refine ⟨sSup c, ?_, fun _ => le_sSup⟩
    intro p hp
    obtain ⟨s, hs, hp⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨a, ha⟩ hc'.directedOn).mp hp
    grind) (AddSubgroup.zmultiples (u,1)) (by
      rintro p ⟨n, rfl⟩ hn
      simp_all)
  have h1 := hunit (AddSubgroup.mem_zmultiples _)
  refine ⟨A, h1, hA.prop, ?_⟩
  intro x m N hx hN
  let cut (y : G) (sg : ℝ) := {v : ℝ | ∃ p ∈ A, ∃ n : ℕ, p.1 + (n+1) • y ∈ C ∧ sg*p.2/(n+1) = v}
  obtain ⟨t, hL, hU⟩ := exists_between_of_forall_le (s := cut x (-1)) (t := cut (-x) 1)
    ⟨_, m • (u,1), A.nsmul_mem h1 m, 0, by simpa using hx, rfl⟩
    ⟨_, N • (u,1), A.nsmul_mem h1 N, 0, by simpa [sub_eq_add_neg] using hN, rfl⟩ (by
      rintro _ ⟨p,hp,n,hp',rfl⟩ _ ⟨q,hq,m,hq',rfl⟩
      have hc := C.add_mem (C.nsmul_mem hp' (m+1)) (C.nsmul_mem hq' (n+1))
      rw [nsmul_add, nsmul_add, smul_neg, smul_neg, smul_comm (m+1) (n+1)] at hc
      have he : (m+1) • p.1 + (n+1) • q.1 ∈ C := by simpa [add_add_add_comm] using hc
      have h := hA.prop _ (A.add_mem (A.nsmul_mem hp (m+1)) (A.nsmul_mem hq (n+1))) he
      change 0 ≤ (m+1) • p.2 + (n+1) • q.2 at h
      simp only [nsmul_eq_mul, Nat.cast_succ] at h
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr; linarith)
  refine ⟨t, AddSubgroup.zmultiples_le.mp (le_sup_right.trans
    (hA.le_of_ge ?_ le_sup_left))⟩
  intro p hp
  obtain ⟨q,hq,_,⟨n,rfl⟩,rfl⟩ := AddSubgroup.mem_sup.mp hp
  change q.1 + n • x ∈ C → 0 ≤ q.2 + n • t
  rcases n with (_|n)|n
  · simpa using hA.prop q hq
  · simp only [Int.ofNat_eq_natCast, natCast_zsmul]; intro hc
    have h := hL ⟨q,hq,n,hc,rfl⟩
    rw [div_le_iff₀ (by positivity)] at h
    grind
  · simp only [Int.negSucc_eq, ← Int.natCast_succ, neg_zsmul, natCast_zsmul]
    intro hc
    have h := hU ⟨q,hq,n,by simpa using hc,rfl⟩
    rw [le_div_iff₀ (by positivity)] at h
    grind

/-- A supporting logarithmic price on an ordered resource monoid. The
extra direction `d-k` enforces the detector, while normalization at `u`
excludes a gain even when the detector is used zero times. -/
theorem log_price {S : Type*} [AddCommMonoid S] [Preorder S] [AddLeftMono S] (u d k : S)
    (bounds : ∀ x, ∃ m n : ℕ, 0 ≤ m • u + x ∧ x ≤ n • u)
    (no : ∀ (c : S) (m n : ℕ), ¬ c + (m+1) • u + n • d ≤ c + n • k) :
    ∃ f : S →+o ℝ, f u = 1 ∧ f k ≤ f d := by
  let η : S →+ GrothendieckAddGroup S := GrothendieckAddGroup.of
  let C : AddSubmonoid (GrothendieckAddGroup S) := {
    carrier := {v | ∃ a b : S, ∃ n : ℕ, a + n • d ≤ b + n • k ∧ v = η b - η a}
    zero_mem' := ⟨0,0,0,by simp,by simp⟩
    add_mem' := by
      rintro _ _ ⟨a,b,s,hab,rfl⟩ ⟨c,e,t,hce,rfl⟩
      refine ⟨a+c,b+e,s+t,?_,by simp; abel⟩
      simpa [add_smul, add_add_add_comm] using add_le_add hab hce }
  have ord {a b : S} (h : a ≤ b) : η b - η a ∈ C := ⟨a,b,0,by simpa,rfl⟩
  obtain ⟨A, h1, hp, hex⟩ := positive_graph C (η u) (by
    rintro (n|n) ⟨a,b,s,hab,h⟩
    · simp
    exfalso
    change -(↑(n+1):ℤ) • η u = _ at h
    rw [neg_zsmul, natCast_zsmul] at h
    have he : η ((n+1) • u + b) = η a := by
      rw [map_add,map_nsmul,← sub_eq_zero,add_sub_assoc,← h]; simp
    obtain ⟨e,he⟩ := (AddLocalization.addMonoidOf ⊤).exists_of_eq he
    apply no (e+b) n s
    have := add_le_add_right hab (e:S)
    grind only [= add_assoc, = add_comm])
  have ex (x : S) : ∃ t, (η x,t) ∈ A := by
    obtain ⟨m,n,hm,hn⟩ := bounds x
    exact hex _ m n (by simpa using ord hm) (by simpa using ord hn)
  choose f hf using ex
  have cmp {p q : GrothendieckAddGroup S × ℝ} (ha : p ∈ A) (hb : q ∈ A)
      (h : q.1 - p.1 ∈ C) := sub_nonneg.mp (hp _ (A.sub_mem hb ha) h)
  have eqv {p q : GrothendieckAddGroup S × ℝ} (ha : p ∈ A) (hb : q ∈ A)
      (h : p.1 = q.1) := le_antisymm (cmp ha hb (by simp_all)) (cmp hb ha (by simp_all))
  exact ⟨{toFun := f, monotone' := fun _ _ h => cmp (hf _) (hf _) (ord h),
          map_zero' := eqv (hf 0) A.zero_mem (map_zero η),
          map_add' := fun x y => eqv (hf _) (A.add_mem (hf x) (hf y)) (map_add η x y)},
    eqv (hf u) h1 rfl, cmp (hf k) (hf d) ⟨k,d,1,by simp [add_comm],rfl⟩⟩

end OAI.MatrixMultiplication.AuxiliarySeparation
