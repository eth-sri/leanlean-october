module

public import Mathlib.Tactic
public import ImprovedExponents.PrunedProgram.Shared.Stage
public import ImprovedExponents.PrunedProgram.Pre.Preprocessing
public import ImprovedExponents.PrunedProgram.Query.Query
public import ImprovedExponents.PrunedProgram.Wrapper.Task
public import ImprovedExponents.Pipeline.RegimeRS

@[expose] public section

/-!
# The pruned thin-product solver as a program, and as an offline routine

`programP G r s` is `programRS G r s` (upstream's `program31 G` with the regime test `D^r ≤ N^s`)
followed by the seven procedures of the pruned solver: the encoder with a budget of symbols `P₀`,
the encodings of all bands, the shared stage, the preprocessing of Theorem 30, the preprocessing
and the offline routine with rational parameters, and the solver of all instances
(`ImprovedExponents.PrunedProgram.Procs`).  Every other procedure — the band arrays, the slices,
the tiles, the queries, the padding — is upstream's and keeps its number.

The entries are assembled as upstream's are (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/
Program.lean`, `Theorem30/Program.lean`): the shared stage from `sharedP_entry`, the
preprocessing from `preCoreP_of_base58`, the queries from `queryAtP_of_base58`, and the routine
`offline32P` from `pre31P_meets`, `query31P_meets` and `offline32P_meets`, all with the constant
`cShared30` of upstream's shared stage.  `offline32PRoutine G r s` packages the routine for the
generic solver of `ImprovedExponents.Pipeline.ThinClaim`.

Adapted from upstream (Apache-2.0).
-/

namespace ImprovedExponents

open Light Light.Sec3 Light.Sec4

/-- The bodies of the procedures number 77 to 83. -/
def procsP G :=
  [Sec2.encodePBody Sec2.pEncStep 77, Sec2.encodeBandsPBody, Sec2.sharedPBody,
    preCorePBody, pre31PBody G, offline32PBody, allBody 75 82]

/-- The pruned solver: `programRS G r s` followed by the seven new procedures. -/
def programP G r s := programRS G r s ++ procsP G

/-- `programRS G r s` has 77 procedures. -/
theorem length_programRS G r s : (programRS G r s).length = 77 := rfl

/-- The new procedures stand at their numbers. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean (program31_at)
theorem programP_at G r s n {body} (hn : 77 ≤ n := by norm_num)
    (h : (procsP G)[n - 77]? = some body := by rfl) : (programP G r s)[n]? = some body := by
  grind [length_programRS, programP]

/-- A procedure of `program31 G` is one of `programP G r s`, with the same number. -/
theorem programP_at_low G r s {n : ℕ} {body}
    (h : (program31 G)[n]? = some body) : (programP G r s)[n]? = some body := by
  grind [programP, programRS]

/-- The pruned solver begins with `base58`. -/
theorem programP_eq_base58 G r s :
    programP G r s = base58 ++
      procs31 G ++ [powLtBody, testRSBody r s, .skip] ++ procsP G := rfl

/-! ## The entries -/

/-- **The pruned shared stage**, in `programP G r s`, with upstream's constant. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (shared_base58)
theorem sharedP_programP G r s lim (std : Std lim) :
    Sec2.SharedSpecP lim (programP G r s) cShared30 := by
  have  := (by rfl : programP G r s = Sec2.program5 ++ [Stmt.skip, Sec2.thinBruteBody, Stmt.skip] ++ List.replicate 11 Stmt.skip ++ procs40 ++ [Stmt.skip, queryAtBody, Stmt.skip, Stmt.skip] ++ procs31 G ++ [powLtBody, testRSBody r s, Stmt.skip] ++ procsP G)
  refine Sec2.sharedP_entry std (programP_at G r s 79)
    (programP_at G r s 78) ?_ ?_ (programP_at G r s 77)
    (c := Sec2.cShared5) ?_ (by decide) le_rfl
  · aesop
  · aesop
  · grind [Sec2.sharedCallees_of_prefix]

/-- **The pruned preprocessing of Theorem 30**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (preCore_base58)
theorem preCoreP_programP G r s :
    ∀ lim, PreCoreSpecP lim (programP G r s) cShared30 := by
  intro lim p t hmL aX aY b0 X Y U μ ht hlim
  exact preCoreP_of_base58 (programP_eq_base58 G r s) (programP_at G r s 80)
    (sharedP_programP G r s lim hlim.std) p t hmL aX aY b0 X Y U μ ht hlim

/-- **The pruned preprocessing with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (pre31_program31)
theorem pre31P_programP G r s :
    ∀ lim, PreSpec31P lim (programP G r s) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have hcopy :=
    copy_ok (programP_at_low G r s (program31_at G 58)) std
  have hfill :=
    fill_ok (programP_at_low G r s (program31_at G 59)) std
  have hlog :=
    log4_meets (programP_at_low G r s (program31_at G 60)) std
  have hlev : CeilMulSpec lim (programP G r s) 72 G.a G.b :=
    ceilMul_meets G.hb (programP_at_low G r s (program31_at G 72))
  have hswi : CeilMulSpec lim (programP G r s) 73 G.p G.q :=
    ceilMul_meets G.hq (programP_at_low G r s (program31_at G 73))
  have hpad :=
    padX_meets (programP_at_low G r s (program31_at G 62)) hcopy hfill std
  exact pre31P_meets G (programP_at G r s 81)
    ⟨hlog, hlev, hswi, hpad, hcopy, hfill, preCoreP_programP G r s lim⟩ N D₀ aX aY fr X Y U μ hin

/-- **A query with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (query31_program31)
theorem query31P_programP G r s :
    ∀ lim, QuerySpec31P lim (programP G r s) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip :=
    ipAt_meets (programP_at_low G r s (program31_at G 63)) hin.lim.std
  exact query31P_meets G (programP_at_low G r s (program31_at G 65))
    (queryAtP_of_base58 (programP_eq_base58 G r s) : QueryAtSpecP lim (programP G r s)) hip N D₀ aX aY fr X Y U μ I J hin

/-- **The pruned offline routine**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (offline32_program31)
def offline32P_programP G r s :=
  fun lim => offline32P_meets (programP_at G r s 82) (pre31P_programP G r s lim)
    (query31P_programP G r s lim)

/-- A program that begins with `programP G r s` holds offline32P with its specification at the
parameters `G`, for all limits. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offlineSpec32_of_program31)
theorem offlineSpec32P_of_programP {P} {G} {r s}
    (h : ∃ Q, P = programP G r s ++ Q) lim : OfflineSpec32P lim P cShared30 G := by
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
  proc := 82
  body := offline32PBody
  aux P := ∃ Q, P = programP G r s ++ Q
  aux_append _ Q := fun ⟨R, h⟩ => ⟨R ++ Q, by rw [h, List.append_assoc]⟩
  time := tOffline32P cShared30 G
  time_mono N D _ _ hw := tOffline32P_mono cShared30 G N D hw
  need := offline32Need G
  need_poly := offline32Need_poly G
  meets haux _ hpre hfit ok :=
    offline32P_meets_thinTask (offlineSpec32P_of_programP haux _) hpre hfit ok

/-- `programP G r s` holds offline32P, the procedures it calls, and the solver of all instances
that calls it after the test `D^r ≤ N^s`. -/
theorem offline32PRoutine_programP G r s :
    (programP G r s)[82]? = some offline32PBody ∧
      (offline32PRoutine G r s).aux (programP G r s) ∧
      (programP G r s)[83]? = some (allBody 75 82) :=
  ⟨programP_at G r s 82, ⟨[], (List.append_nil _).symm⟩,
    programP_at G r s 83⟩

end ImprovedExponents
