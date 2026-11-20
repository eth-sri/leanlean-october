module
public import AnalyticESC.Conjugation.Composite
public import AnalyticESC.Conjugation.Zeros

@[expose] public section
/-! # Common coordinates and periodic projections -/
namespace AnalyticESC
open Set

lemma conj_iff {M : ℕ} {F : Fin M → ℝ → ℝ} : ConjSelfSimilar F ↔
    ∃ g, IsAnalyticCoord g ∧ ∀ i, Linearizes g (F i) := by
  constructor
  · rintro ⟨g,h,l,b,H⟩; exact ⟨g,h,fun i => ⟨l i,b i,H i⟩⟩
  · rintro ⟨g,h,H⟩; choose l b hb using H; exact ⟨g,h,l,b,hb⟩

namespace IFS
variable {N : ℕ} (Φ : IFS N)

theorem conjSelfSimilar_iff (hnd : ¬ ∃ x, Φ.attractor = {x}) : ConjSelfSimilar Φ.realMap ↔
    ∀ i j : Address N, ∀ x : I, Φ.P i x = Φ.P j x := by
  rw [conj_iff]; constructor
  · rintro ⟨g,hg,h⟩ i j x
    have hr : Regular g := ⟨hg.1,fun z hz h0 => hnd ((Φ.exists_attractor_eq_singleton_iff
      (Nat.zero_lt_of_lt (i 0).isLt)).mpr ⟨z,hz,fun k => Φ.fixes_critical (a := [k]) (by simp) hg (h k) hz h0⟩)⟩
    have e (w) := Φ.match_of_rec (by simp) Φ.head_rec hr (fun w => h (w 0)) w
    exact (e i x.2).symm.trans (e j x.2)
  · intro h
    by_cases hn : Nonempty (Fin N)
    · obtain ⟨k⟩ := hn
      obtain ⟨g,hr,e⟩ := Φ.coord_for fun _ => k
      refine ⟨g,hr.coord,fun i => (Φ.linearizes_iff_match (by simp) (Φ.head_rec fun _ => i) hr).mpr ?_⟩
      exact fun x hx => (e hx).trans (h _ _ ⟨x,hx⟩)
    · exact ⟨id,⟨analyticOnNhd_id,Function.injective_id.injOn⟩,fun i => (hn ⟨i⟩).elim⟩

/-- A regular linearization of a word also linearizes any commuting word:
composing its coordinate with that word gives another linearization of the first. -/
private lemma pair_iff {m} (hm : 0 < m) (i j : Block N m) :
    ConjSelfSimilar ![Φ.R (.ofFn i),Φ.R (.ofFn j)] ↔ EqOn (Φ.periodProj hm i) (Φ.periodProj hm j) I := by
  rw [conj_iff]
  obtain ⟨G,hr,e⟩ := Φ.coord_for (periodic hm (i ∘ Fin.rev))
  have hi := (Φ.linearizes_period hr hm i).mpr e
  constructor
  · rintro ⟨g,hg,H⟩
    by_cases h : Regular g
    · exact ((Φ.linearizes_period h hm i).mp (H 0)).symm.trans ((Φ.linearizes_period h hm j).mp (H 1))
    obtain ⟨z,hz,hd⟩ : ∃ z ∈ I, deriv g z = 0 := by by_contra! hn; exact h ⟨hg.1,hn⟩
    have fix {w : Block N m} (l : Linearizes g (Φ.R (.ofFn w))) := Φ.fixes_critical (by simpa using hm.ne') hg l hz hd
    have comm := comp_comm_of_conj hg.2 (Φ.re_comp_mem_I _) (Φ.re_comp_mem_I _) (H 0) (H 1) hz (fix (H 0)) (fix (H 1))
    have hr' := Φ.regular_comp hr (.ofFn j)
    have hi' : Linearizes (G ∘ Φ.R (.ofFn j)) (Φ.R (.ofFn i)) := by
      obtain ⟨l,b,l₀,lb,h⟩ := hi
      exact ⟨l,b,l₀,lb,fun x hx => by simpa only [Function.comp_apply,comm x hx] using h _ (Φ.re_comp_mem_I (.ofFn j) hx)⟩
    have hj := (Φ.linearizes_iff_D hr (by simpa using hm.ne')).mpr (((Φ.linearizes_period hr' hm i).mp hi').trans e.symm)
    exact e.symm.trans ((Φ.linearizes_period hr hm j).mp hj)
  · intro eq; exact ⟨G,hr.coord,Fin.forall_fin_two.mpr ⟨hi,(Φ.linearizes_period hr hm j).mpr (e.trans eq)⟩⟩

theorem subConjSelfSimilar_iff : (∃ m, ∃ i j : Block N m, i ≠ j ∧ ConjSelfSimilar ![Φ.R (.ofFn i),Φ.R (.ofFn j)]) ↔
    ∃ m hm, ∃ i j : Block N m, i ≠ j ∧ ∀ x : I, Φ.P (periodic hm i) x = Φ.P (periodic hm j) x := by
  have rev {m : ℕ} (i : Block N m) : (i ∘ Fin.rev) ∘ Fin.rev = i := funext fun _ => by simp
  have inj {m : ℕ} {i j : Block N m} (h : i ≠ j) : i ∘ Fin.rev ≠ j ∘ Fin.rev := by grind
  constructor
  · rintro ⟨m,i,j,hij,H⟩
    have hm := depth_pos hij
    exact ⟨m,hm,_,_,inj hij,fun x => (Φ.pair_iff hm i j).mp H x.2⟩
  · rintro ⟨m,hm,i,j,hij,H⟩
    refine ⟨m,_,_,inj hij,(Φ.pair_iff hm _ _).mpr fun x hx => ?_⟩
    simpa only [periodProj,rev] using H ⟨x,hx⟩

end IFS
end AnalyticESC
