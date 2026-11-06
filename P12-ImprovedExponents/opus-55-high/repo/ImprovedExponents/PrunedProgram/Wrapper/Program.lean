
import ImprovedExponents.PrunedProgram.Shared.Stage
import ImprovedExponents.PrunedProgram.Pre.Preprocessing
import ImprovedExponents.PrunedProgram.Query.Query
import ImprovedExponents.PrunedProgram.Wrapper.Task
import ImprovedExponents.Pipeline.RegimeRS


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

open Light Light.Sec4

/-- The bodies of the procedures number 77 to 83. -/
def procsP (G : RatParams) : List Stmt :=
  [Sec2.encodePBody Sec2.pEncStep Proc.encodeP, Sec2.encodeBandsPBody, Sec2.sharedPBody,
    preCorePBody, pre31PBody G, offline32PBody, allBody Proc.testRS Proc.offline32P]

/-- The pruned solver: `programRS G r s` followed by the seven new procedures. -/
def programP (G : RatParams) (r s : ℕ) : Program := programRS G r s ++ procsP G


variable (G : RatParams) (r s : ℕ)





/-! ## The entries -/

/-- **The pruned shared stage**, in `programP G r s`, with upstream's constant. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (shared_base58)
theorem sharedP_programP (lim : Limits) (std : Std lim) :
    Sec2.SharedSpecP lim (programP G r s) cShared30 := by
  refine Sec2.sharedP_entry std (by rfl)
    (by rfl) ?_ ?_ (by rfl) ?_ (by decide) le_rfl
  · rfl
  · rfl
  · exact Sec2.sharedCallees_of_prefix _ lim std

/-- **The pruned preprocessing of Theorem 30**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (preCore_base58)
theorem preCoreP_programP :
    ∀ lim, PreCoreSpecP lim (programP G r s) cShared30 := by
  intro lim p t hmL aX aY b0 X Y U μ ht hlim
  exact preCoreP_of_base58 (by rfl) (by rfl)
    (sharedP_programP G r s lim hlim.std) p t hmL aX aY b0 X Y U μ ht hlim

/-- **A query at a given place of the memory**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (queryAt_base58)
theorem queryAtP_programP : ∀ lim, QueryAtSpecP lim (programP G r s) :=
  fun _ => queryAtP_of_base58 (by rfl)

/-- **The pruned preprocessing with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (pre31_program31)
theorem pre31P_programP :
    ∀ lim, PreSpec31P lim (programP G r s) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have hcopy : CopySpec lim (programP G r s) :=
    copy_ok (by rfl) std
  have hfill : FillSpec lim (programP G r s) :=
    fill_ok (by rfl) std
  have hlog : Log4Spec lim (programP G r s) :=
    log4_meets (by rfl) std
  have hlev : CeilMulSpec lim (programP G r s) Proc.levels31 G.a G.b :=
    ceilMul_meets G.hb (by rfl)
  have hswi : CeilMulSpec lim (programP G r s) Proc.switch31 G.p G.q :=
    ceilMul_meets G.hq (by rfl)
  exact pre31P_meets G (by rfl)
    ⟨hlog, hlev, hswi, padX_meets (by rfl) hcopy hfill std, hcopy, hfill, preCoreP_programP G r s lim⟩ N D₀ aX aY fr X Y U μ hin

/-- **A query with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (query31_program31)
theorem query31P_programP :
    ∀ lim, QuerySpec31P lim (programP G r s) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip : IpAtSpec lim (programP G r s) :=
    ipAt_meets (by rfl) hin.lim.std
  exact query31P_meets G (by rfl)
    (queryAtP_programP G r s lim) hip N D₀ aX aY fr X Y U μ I J hin

/-- **The pruned offline routine**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (offline32_program31)
theorem offline32P_programP :
    ∀ lim, OfflineSpec32P lim (programP G r s) cShared30 G :=
  fun lim => offline32P_meets (by rfl) (pre31P_programP G r s lim)
    (query31P_programP G r s lim)

/-- A program that begins with `programP G r s` holds offline32P with its specification at the
parameters `G`, for all limits. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offlineSpec32_of_program31)
theorem offlineSpec32P_of_programP {P : Program} {G : RatParams} {r s : ℕ}
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
def offline32PRoutine (G : RatParams) (r s : ℕ) : OfflineRoutine := ⟨fun N D => G.m₀ ≤ logFour D → Hyp30 (parOf G N D) (switchOf31 G D), Proc.offline32P, offline32PBody, fun P => ∃ Q, P = programP G r s ++ Q, fun _ Q => fun ⟨R, h⟩ => ⟨R ++ Q, by rw [h, List.append_assoc]⟩, tOffline32P cShared30 G, fun N D _ _ hw => tOffline32P_mono cShared30 G N D hw, offline32Need G, offline32Need_poly G, fun haux _ hpre hfit ok => offline32P_meets_thinTask (offlineSpec32P_of_programP haux _) hpre hfit ok⟩

/-- `programP G r s` holds offline32P, the procedures it calls, and the solver of all instances
that calls it after the test `D^r ≤ N^s`. -/
theorem offline32PRoutine_programP :
    (programP G r s)[Proc.offline32P]? = some offline32PBody ∧
      (offline32PRoutine G r s).aux (programP G r s) ∧
      (programP G r s)[Proc.allP]? = some (allBody Proc.testRS Proc.offline32P) :=
  by tauto
