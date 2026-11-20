module

public import ThreeSumApsp.Lang.Frames

@[expose] public section

namespace Light

/-- Insert the two counters of a rectangular traversal into a frame. -/
abbrev rectLoc (loc : ℕ → ℤ) (r c : ℕ) (i j : ℤ) : ℕ → ℤ :=
  Function.update (Function.update loc r i) c j

/-- A rectangular traversal with fixed bounds and arbitrary scratch locals. The invariant `I`
tracks the locals and memory at each point of the traversal. -/
theorem Ends.forRect {β : Type} {lim : Limits} {P : Program} {d n m r c x y b T : ℕ}
    {s : Stmt} {μ : ℕ → ℤ} {Q : State → Prop} (L : β → ℕ → ℤ) (I : ℕ → ℕ → β → (ℕ → ℤ) → Prop) (a : β)
    (start : I 0 0 a μ) (hn : (n : ℤ) ≤ lim.word) (hm : (m : ℤ) ≤ lim.word)
    (hX : ∀ t, L t x = n) (hY : ∀ t, L t y = m)
    (step : ∀ i j (t : β) ν, i < n → j < m → I i j t ν →
      Ends lim P d s ⟨rectLoc (L t) r c i j, ν⟩ b fun σ =>
        ∃ t', σ.loc = rectLoc (L t') r c i j ∧ I i (j + 1) t' σ.mem)
    (row : ∀ i t ν, i < n → I i m t ν → I (i + 1) 0 t ν)
    (done : ∀ t j ν, I n 0 t ν → Q ⟨rectLoc (L t) r c n j, ν⟩)
    (hrc : r ≠ c := by decide) (hxr : x ≠ r := by decide) (hxc : x ≠ c := by decide)
    (hyr : y ≠ r := by decide) (hyc : y ≠ c := by decide)
    (hT : n * (m * (b + 8) + 14) + 6 ≤ T := by light_time) :
    Ends lim P d (.for r (v x) (.for c (v y) s)) ⟨L a, μ⟩ T Q := by
  let loc (i : ℕ) (j : ℤ) (t : β) := rectLoc (L t) r c i j
  have bx i j t ν : (v x).Gives lim ⟨loc i j t, ν⟩ n := by
    aesop
  have by' i j t ν : (v y).Gives lim ⟨loc i j t, ν⟩ m := by
    aesop
  refine Ends.forShape (fun i (t : β × ℤ) ν => ⟨loc i t.2 t.1, ν⟩) (fun i t => I i 0 t.1) n
    (m * (b + 8) + 6) (a, L a c) start ?_ (fun t => done t.1 t.2)
    (first := by simp [loc, rectLoc, Function.update_of_ne hrc.symm])
    (bound := fun i t ν _ _ => bx i t.2 t.1 ν)
    (counter := by grind)
    (next := by intros; simp [loc, rectLoc, Function.update_comm hrc.symm]) hn ((le_of_eq (by simp only [Expr.cost]; ring)).trans hT)
  rintro i ⟨t, j⟩ ν hi hI
  refine Ends.forShape (fun k t ν => ⟨loc i k t, ν⟩) (I i) m b t hI ?_ ?_
    (first := by simp [loc, rectLoc]) (bound := fun k t ν _ _ => by' i k t ν)
    (counter := by intros; simp [loc, rectLoc])
    (next := by intros; simp [loc, rectLoc]) hm (by light_time)
  · intro k t ν hk h
    refine (step i k t ν hi hk h).mono le_rfl ?_
    rintro ⟨_, _⟩ ⟨t', rfl, h'⟩
    exact ⟨t', _, rfl, h'⟩
  aesop


end Light
