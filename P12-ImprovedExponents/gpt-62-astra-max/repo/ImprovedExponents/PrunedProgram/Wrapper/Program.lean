module

public import ImprovedExponents.PrunedProgram.Shared.Stage
public import ImprovedExponents.PrunedProgram.Pre.Preprocessing
public import ImprovedExponents.PrunedProgram.Query.Query
public import ImprovedExponents.PrunedProgram.Wrapper.Task
public import ImprovedExponents.Pipeline.RegimeRS

@[expose] public section

/-! The pruned solver, assembled from precisely the routines it calls. -/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4

open Light.Sec2 in
/-- The thin-product program. Padding keeps the subroutines at their library indices. -/
def programP (G : RatParams) (r s : ℕ) : Program :=
  [.skip, .skip, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
   digitsBody, coefBody, bandArrayBody, encStepBody] ++ List.replicate 16 .skip ++
  [thinBruteBody] ++ List.replicate 12 .skip ++ BoxTable.procs ++
  [.skip, queryAtBody, .skip, .skip, copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody,
   .skip, query31Body] ++ List.replicate 6 .skip ++
  [ceilMulBody G.a G.b, ceilMulBody G.p G.q, powLtBody, testRSBody r s, .skip,
   encodePBody pEncStep Proc.encodeP, encodeBandsPBody, sharedPBody, preCorePBody,
   pre31PBody G, offline32PBody, allBody Proc.testRS Proc.offline32P]

private theorem hasTiles (G : RatParams) (r s : ℕ) : BoxTable.Has (programP G r s) := by
  intro i hi; interval_cases i <;> rfl

/-! ## The entries -/

/-- **The pruned shared stage**, in `programP G r s`, with upstream's constant. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (shared_base58)
theorem sharedP_programP (G : RatParams) (r s : ℕ) (lim : Limits) (std : Std lim) :
    Sec2.SharedSpecP lim (programP G r s) cShared30 := by
  apply Sec2.sharedP_entry std rfl rfl rfl rfl rfl _
    (by decide) le_rfl
  exact ⟨Sec2.pow_entry std rfl (by decide), Sec2.binom_entry std rfl (by decide),
    Sec2.sqrt_entry rfl (by decide), Sec2.coef_entry std rfl (by decide), Sec2.subsets_entry std rfl (by decide),
    Sec2.counters_entry std rfl (by decide), Sec2.digits_entry std rfl (by decide)⟩

/-- **The pruned preprocessing of Theorem 30**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (preCore_base58)
theorem preCoreP_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, PreCoreSpecP lim (programP G r s) cShared30 := by
  intro lim p t hmL aX aY b0 X Y U μ ht hlim
  exact preCoreP_of_tiles (hasTiles G r s) rfl
    (sharedP_programP G r s lim hlim.std) p t hmL aX aY b0 X Y U μ ht hlim

/-- **A query at a given place of the memory**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (queryAt_base58)
theorem queryAtP_programP (G : RatParams) (r s : ℕ) : ∀ lim, QueryAtSpecP lim (programP G r s) :=
  queryAtSpecP_all (hasTiles G r s) rfl

/-- **The pruned preprocessing with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (pre31_program31)
theorem pre31P_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, PreSpec31P lim (programP G r s) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have copy := copy_ok (P := programP G r s) rfl std
  have fill := fill_ok (P := programP G r s) rfl std
  exact pre31P_meets G rfl ⟨log4_meets rfl std, ceilMul_meets G.hb rfl,
    ceilMul_meets G.hq rfl, padX_meets rfl copy fill std, copy, fill, preCoreP_programP G r s lim⟩
    N D₀ aX aY fr X Y U μ hin

/-- **A query with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (query31_program31)
theorem query31P_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, QuerySpec31P lim (programP G r s) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  exact query31P_meets G rfl (queryAtP_programP G r s lim) (ipAt_meets rfl hin.lim.std)
    N D₀ aX aY fr X Y U μ I J hin

/-- **The pruned offline routine**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (offline32_program31)
theorem offline32P_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, OfflineSpec32P lim (programP G r s) cShared30 G :=
  fun lim => offline32P_meets rfl (pre31P_programP G r s lim)
    (query31P_programP G r s lim)

/-- A program that begins with `programP G r s` holds offline32P with its specification at the
parameters `G`, for all limits. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offlineSpec32_of_program31)
theorem offlineSpec32P_of_programP {P } {G } {r s }
    (h : ∃ Q, P = programP G r s ++ Q) (lim : Limits) : OfflineSpec32P lim P cShared30 G := by
  obtain ⟨Q, rfl⟩ := h
  exact (offline32P_programP G r s lim).append Q

/-! ## The routine -/

/-- **The pruned offline routine** at the parameters `G`, as an `OfflineRoutine`: it is specified
on the instances where the hypotheses of Theorem 30 hold from the threshold on, in the programs
that begin with `programP G r s`.  Its time is `tOffline32P cShared30 G`; its needs are those of
upstream's routine, since the pruned shared stage has the same layout and forms the same
numbers. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offline32Routine)
def offline32PRoutine (G : RatParams) (r s : ℕ) : OfflineRoutine where
  Ok N D := G.m₀ ≤ logFour D → Hyp30 (parOf G N D) (switchOf31 G D)
  proc := Proc.offline32P
  body := offline32PBody
  aux P := ∃ Q, P = programP G r s ++ Q
  aux_append _ Q := fun ⟨R, h⟩ => ⟨R ++ Q, by grind⟩
  time := tOffline32P cShared30 G
  time_mono N D _ _ hw := tOffline32P_mono cShared30 G N D hw
  need := offline32Need G
  need_poly := offline32Need_poly G
  meets haux _ hpre hfit ok :=
    offline32P_meets_thinTask (offlineSpec32P_of_programP haux _) hpre hfit ok

/-- `programP G r s` holds offline32P, the procedures it calls, and the solver of all instances
that calls it after the test `D^r ≤ N^s`. -/
theorem offline32PRoutine_programP (G : RatParams) (r s : ℕ) :
    (programP G r s)[Proc.offline32P]? = some offline32PBody ∧
      (offline32PRoutine G r s).aux (programP G r s) ∧
      (programP G r s)[Proc.allP]? = some (allBody Proc.testRS Proc.offline32P) :=
  by tauto

end ImprovedExponents
