module

public import ImprovedExponents.AllEdges.Chain

@[expose] public section

namespace ImprovedExponents.AllEdges
open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The decision host simply tests whether any of the output flags is set. -/
private def decideBody (p : ℕ) : Stmt :=
  .set 6 (v 0 *' v 0) ;;
  .call p [v 0, v 1, v 2, v 3, v 4, v 5, v 5 +' v 6] 0 ;;
  .set 0 (k 0) ;;
  .for 7 (v 6) (.ite (M (v 5 +' v 7) =' k 1) (.set 0 (k 1)) .skip)

private theorem any_flag {x : TriInst} {μ} {f} (hn : 1 ≤ x.n)
    (seg : Seg μ f (aeFlags x.n x.AB x.BC x.AC)) :
    (∃ t < x.n * x.n, μ (f + t) = 1) ↔ (triOf x.n x.AB x.BC x.AC).HasZeroTriangle := by
  have read (t : ℕ) (ht : t < x.n * x.n) := seg.getD  (by simpa using ht) 0
  constructor
  · rintro ⟨t, ht, h⟩
    rw [read t ht, aeFlags_getD _ _ _ ht, flag_eq_one_iff] at h
    obtain ⟨c, hc, h⟩ := h
    refine ⟨⟨_, (Nat.div_lt_iff_lt_mul hn).2 ht⟩, ⟨_, Nat.mod_lt t hn⟩, ⟨c,hc⟩, ?_⟩
    simpa [TriangleInstance.IsZeroTriangle, TriangleInstance.S, triOf, Nat.div_add_mod'] using h
  · rintro ⟨a,b,c,h⟩
    have ht : a.val * x.n + b.val < x.n * x.n := by nlinarith [a.isLt, b.isLt]
    refine ⟨_, ht, ?_⟩
    rw [read _ ht, aeFlags_getD_eq_bit_scanHit _ _ _ a.isLt b.isLt, ← flag_eq_bit, flag_eq_one_iff]
    simp [scanHit]
    exact ⟨_, c.isLt, h⟩

private def decNeed (need : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(need n U).word + 1, n * n + (need n U).cells, (need n U).depth + 1⟩

private theorem decisionHost : IsHost aeTask etTask (fun T n U => T n U + 32 * (n*n + 1)) decNeed := by
  constructor
  · intro P p T need h
    refine ⟨[decideBody p], P.length, decideBody p, by simp, ?_⟩
    intro R lim d x μ fr pre ok
    change TriInst at x
    change x.Pre μ fr at pre
    change (decNeed need x.n x.U).Ok lim fr d at ok
    let y : AeInst := ⟨x.n,x.U,x.ab,x.bc,x.ac,fr,x.AB,x.BC,x.AC⟩
    have py : y.Pre μ (fr + x.n*x.n) :=
      { pre.mono (by omega) with
        belowOut := le_rfl, apartAB := Or.inl pre.belowAB, apartBC := Or.inl pre.belowBC,
        apartAC := Or.inl pre.belowAC }
    have ok' : (need x.n x.U).Ok lim (fr + x.n*x.n) (d+1) :=
      ok.mono (by simp [decNeed]) (by simp [decNeed, Nat.add_assoc]) (by simp [decNeed]; omega)
    have meets := h.meets ([decideBody p] ++ R) y (fr + x.n*x.n) py ok'
    have hdepth := ok.depth
    have hword := ok.space
    have hsp := le_trans (Nat.le_add_right ..) ok'.cells
    have hn : (x.n*x.n : ℕ) = x.n * x.n := Nat.cast_mul ..
    simp [decNeed] at hdepth
    rw [List.append_assoc]
    change Ends _ _ _ _ ⟨frame [x.n,x.U,x.ab,x.bc,x.ac,fr], μ⟩ (T x.n x.U + 32*(x.n*x.n+1)) _
    light_set (x.n*x.n) using hn
    light_call meets using aeTask, etTask, y, hn with r ν ⟨seg,hk⟩
    simp [aeTask, y] at *
    light_set 0
    let hit (j : ℕ) := ∃ t < j, ν (fr + t) = 1
    let loc (j : ℕ) := frame [flag (hit j), x.U,x.ab,x.bc,x.ac,fr,(x.n*x.n),j]
    have step (j : ℕ) : hit (j+1) ↔ hit j ∨ ν (fr+j) = 1 := by
      grind
    refine Ends.for (fun j σ => σ = ⟨loc j,ν⟩) (x.n*x.n) 12 ?_ ?_ ?_ ?_ (by omega) ?_
    · simp [loc, flag, hit, update_frame_setLocal]
    · rintro j _ hj _ rfl
      refine Ends.iteLast (fun yes => ?_) (fun no => Ends.skip ?_) (by light_side [loc])
      · have eq : ν (fr+j) = 1 := by assumption
        refine Ends.setTo 1 ?_
        simp [loc, update_frame_setLocal, flag, step, eq]
      · have ne : ν (fr+j) ≠ 1 := by assumption
        simp [loc, update_frame_setLocal, step, ne]
    · rintro _ _ rfl
      exact ⟨flag_congr (any_flag pre.n_pos seg), fun i hi => hk i ⟨by omega, Or.inl hi⟩⟩
    · intros; subst_vars; simp [loc]
    · light_time
  · intro r hr
    unfold decNeed
    poly_need [hr.word, hr.cells, hr.depth]

/-- A single all-edges certificate also pays for the final quadratic pass of the decision solver. -/
theorem decision_of_allEdges {δ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ 1) :
    ExplicitFrom lightModel δ 1 := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  refine ⟨max 3 n₀, K + 64, fun n u => T n u + 32 * (n^2 + 1),
    decisionHost.solvedIn hT (fun Tn ht n U u hn hU hu => ?_), fun n κ u hn hκ hu => ?_⟩
  · grind
  have h3 := (le_max_left _ _).trans hn
  have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast by omega
  have hpow : n^2 ≤ (n:ℝ)^(3-δ) := by
    rw [← Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_le h1; grind
  have hem : n^2 ≤ κ * (n^(3-δ) * Real.log n ^ 1) := by
    calc n^2 = 1 * ((n:ℝ)^2 * 1) := by ring
      _ ≤ _ := by gcongr; simpa using Real.one_le_log_natCast_of_three_le h3
  nlinarith [hb n κ u ((le_max_right _ _).trans hn) hκ hu, one_le_pow₀ h1 (n := 2)]

end ImprovedExponents.AllEdges
