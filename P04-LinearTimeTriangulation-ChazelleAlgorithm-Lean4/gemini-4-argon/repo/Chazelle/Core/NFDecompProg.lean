module

public import Chazelle.Core.NFDecompRam

/-!
# Tree decomposition (WP-C), part 12: the program text

The statements of the decomposition (register map and memory layout in `NFDecompRam`):
`setupS` (constants, field bases), `allocS` (the allocator raised to the end of the new
layout, one word per step), `initS` (all fields cleared, sizes `1`, the root
visited and active with the root slot), `bfsS` (the search), `roundsS` (the rounds: `p1S` sizes,
`p2S` tops and candidates, `cpS` chord pass, `rootS` root step, `rpS` region pass), `fcS` (the
node table) and `hdrS` (the header); `decompStmt` is their sequence.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Setup -/

/-- Constants, the input header, the field bases, and room for the new header. -/
def setupS : Stmt := block [
  .constN 60010 0, .constN 60011 1, .constN 60012 2,
  .loadN 60014 60001,
  .addN 60030 60001 60012, .loadN 60013 60030,
  .addN 60030 60030 60011, .loadN 60015 60030,
  .addN 60030 60030 60012, .loadN 60016 60030,
  .addN 60030 60030 60012, .loadN 60017 60030,
  .copyN 60018 9999,
  .subN 60019 60013 60011,
  .constN 60031 12, .addN 60100 60018 60031,
  .addN 60101 60100 60013, .addN 60102 60101 60013, .addN 60103 60102 60013,
  .addN 60104 60103 60013, .addN 60105 60104 60013, .addN 60106 60105 60013,
  .addN 60107 60106 60013, .addN 60108 60107 60013, .addN 60109 60108 60013,
  .addN 60110 60109 60013, .addN 60111 60110 60013, .addN 60112 60111 60013,
  .addN 60113 60112 60013, .addN 60114 60113 60013, .addN 60115 60114 60013,
  .addN 60116 60115 60013, .addN 60117 60116 60013, .addN 60118 60117 60013,
  .addN 60119 60118 60013,
  .addN 60086 60119 60014, .addN 60086 60086 60014, .addN 60086 60086 60014]

/-- Raise the allocator to `DB + 3 K` (target in `60086`), one word per iteration. -/
def allocS : Stmt := .whileLtN 9999 60086 (.instr (.addN 9999 9999 60011))

/-! ## Initialisation -/

/-- Clear entry `i` of the fields read before they are written: `vis`, `rem`, `pend` (`0`) and
`size` (`1`). -/
def initBody : Stmt := block [
  .addN 60030 60102 60020, .storeN 60030 60010, .addN 60030 60107 60020, .storeN 60030 60011,
  .addN 60030 60111 60020, .storeN 60030 60010, .addN 60030 60112 60020, .storeN 60030 60010,
  .addN 60020 60020 60011]

/-- The root: first in the queue (`ord`), visited (`vis`), active (`act`), with the root slot
(`side = 2`). -/
def rootInit : Stmt := block [
  .addN 60030 60101 60010, .storeN 60030 60010,
  .addN 60030 60102 60010, .storeN 60030 60011, .addN 60030 60113 60010, .storeN 60030 60011,
  .addN 60030 60115 60010, .storeN 60030 60012]

/-- **Initialisation.** -/
def initS : Stmt :=
  .seq (.instr (.constN 60020 0)) (.seq (.whileLtN 60020 60013 initBody) rootInit)

/-! ## The search -/

/-- Read chord `i = list[t]` of the current region and its endpoints `u`, `d`. -/
def bfsRead : Stmt := block [
  .addN 60030 60028 60021, .addN 60030 60017 60030, .loadN 60032 60030,
  .addN 60033 60032 60032, .addN 60033 60033 60033, .addN 60033 60033 60032,
  .addN 60033 60015 60033, .addN 60033 60033 60012, .addN 60033 60033 60011, .loadN 60034 60033,
  .addN 60033 60033 60011, .loadN 60035 60033]

/-- Discover `s` (in `60036`) through chord `i` (`60032`) from `r` (`60029`). -/
def bfsNew : Stmt := block [
  .addN 60030 60102 60036, .storeN 60030 60011,
  .addN 60030 60101 60026, .storeN 60030 60036,
  .addN 60030 60103 60036, .storeN 60030 60029,
  .addN 60030 60104 60036, .storeN 60030 60032,
  .addN 60030 60105 60036, .storeN 60030 60037,
  .addN 60030 60106 60032, .storeN 60030 60036,
  .addN 60026 60026 60011]

/-- The scan of one chord of the current region. -/
def bfsInner : Stmt :=
  .seq bfsRead (.seq (ifEqN 60034 60029 (block [.copyN 60036 60035, .copyN 60037 60011])
      (block [.copyN 60036 60034, .copyN 60037 60010]))
    (.seq (ldF 60038 2 60036) (.seq (ifEqN 60038 60011 .skip bfsNew)
      (.instr (.addN 60021 60021 60011)))))

/-- Dequeue a region and locate its exit-chord list. -/
def bfsDeq : Stmt := block [
  .addN 60030 60101 60025, .loadN 60029 60030,
  .addN 60025 60025 60011,
  .addN 60033 60029 60029, .addN 60033 60033 60033, .addN 60033 60033 60029,
  .addN 60033 60016 60033, .addN 60033 60033 60012, .loadN 60027 60033,
  .addN 60033 60033 60011, .loadN 60028 60033,
  .constN 60021 0]

/-- One step of the search. -/
def bfsOuter : Stmt := .seq bfsDeq (.whileLtN 60021 60027 bfsInner)

/-- **The search.** -/
def bfsS : Stmt := .seq (block [.constN 60025 0, .constN 60026 1]) (.whileLtN 60025 60026 bfsOuter)

/-! ## Pass 1: sizes -/

/-- Add the size of `r` (in `60040`) into its parent's. -/
def p1Add : Stmt := block [
  .addN 60030 60103 60040, .loadN 60043 60030,
  .addN 60030 60107 60040, .loadN 60044 60030,
  .addN 60031 60107 60043, .loadN 60045 60031,
  .addN 60045 60045 60044, .storeN 60031 60045]

/-- One step of the size pass. -/
def p1Body : Stmt :=
  .seq (block [.subN 60039 60019 60020, .addN 60030 60101 60039, .loadN 60040 60030])
    (.seq (.ifLtN 60010 60040
        (.seq (ldF 60041 4 60040) (.seq (ldF 60042 11 60041) (ifEqN 60042 60011 .skip p1Add)))
        .skip)
      (.instr (.addN 60020 60020 60011)))

/-- **The size pass.** -/
def p1S : Stmt := .seq (.instr (.constN 60020 0)) (.whileLtN 60020 60013 p1Body)

/-! ## Pass 2: tops and cut candidates -/

/-- `r` (in `60040`) is a top. -/
def topBr : Stmt := block [
  .addN 60030 60108 60040, .storeN 60030 60040,
  .addN 60030 60109 60040, .storeN 60030 60040,
  .addN 60030 60110 60040, .storeN 60030 60010]

/-- `r` (in `60040`) is no top: its top is its parent's; update the best candidate. -/
def ntBr : Stmt :=
  .seq (block [
      .addN 60030 60103 60040, .loadN 60043 60030,
      .addN 60030 60108 60043, .loadN 60046 60030,
      .addN 60030 60108 60040, .storeN 60030 60046,
      .addN 60030 60107 60040, .loadN 60044 60030,
      .addN 60030 60107 60046, .loadN 60047 60030,
      .subN 60048 60047 60044])
    (.seq (.ifLtN 60044 60048 (.instr (.copyN 60049 60044)) (.instr (.copyN 60049 60048)))
      (.seq (ldF 60050 10 60046)
        (.ifLtN 60050 60049
          (block [.addN 60030 60110 60046, .storeN 60030 60049,
            .addN 60030 60109 60046, .storeN 60030 60040]) .skip)))

/-- One step of the top pass. -/
def p2Body : Stmt :=
  .seq (block [.addN 60030 60101 60020, .loadN 60040 60030])
    (.seq (.ifLtN 60010 60040
        (.seq (ldF 60041 4 60040) (.seq (ldF 60042 11 60041) (ifEqN 60042 60011 topBr ntBr)))
        topBr)
      (.instr (.addN 60020 60020 60011)))

/-- **The top pass.** -/
def p2S : Stmt := .seq (.instr (.constN 60020 0)) (.whileLtN 60020 60013 p2Body)

/-! ## The chord pass -/

/-- `d := code (nreg x)`: `2 x + 1` if `best x = x`, else `2 pch (best x)`. -/
def codeS (d x : ℕ) : Stmt :=
  .seq (ldF 60051 9 x)
    (ifEqN 60051 x (block [.addN d x x, .addN d d 60011])
      (.seq (ldF 60052 4 60051) (.instr (.addN d 60052 60052))))

/-- Fill the two slots of the chord `e` (in `60020`) cut in the previous round. -/
def fillS : Stmt :=
  .seq (ldF 60053 6 60020) (.seq (ldF 60054 3 60053) (.seq (ldF 60055 8 60054)
    (.seq (ldF 60056 5 60053)
      (.seq (ifEqN 60056 60011 (block [.copyN 60057 60053, .copyN 60058 60055])
          (block [.copyN 60057 60055, .copyN 60058 60053]))
        (.seq (codeS 60059 60057) (.seq (codeS 60060 60058)
          (.seq (stF 17 60020 60059) (.seq (stF 18 60020 60060) (stF 12 60020 60010)))))))))

/-- Cut chord `e` (in `60020`) in the component of `t` (in `60055`). -/
def doS : Stmt :=
  .seq (stF 11 60020 60011) (.seq (stF 12 60020 60011) (.seq (ldF 60061 15 60055)
    (.seq (ifEqN 60061 60012 (.instr (.addN 60062 60020 60020))
        (.seq (ldF 60063 14 60055) (.instr (.addN 60062 60063 60063))))
      (stF 16 60020 60062))))

/-- Is chord `e` (in `60020`) chosen? -/
def chkS : Stmt :=
  .seq (ldF 60053 6 60020) (.seq (ldF 60055 8 60053) (.seq (ldF 60064 13 60055)
    (ifEqN 60064 60011 (.seq (ldF 60065 9 60055) (ifEqN 60065 60053 doS .skip)) .skip)))

/-- One step of the chord pass. -/
def cpBody : Stmt :=
  .seq (ldF 60066 12 60020)
    (.seq (ifEqN 60066 60011 fillS (.seq (ldF 60067 11 60020) (ifEqN 60067 60011 .skip chkS)))
      (.instr (.addN 60020 60020 60011)))

/-- **The chord pass.** -/
def cpS : Stmt := .seq (.instr (.constN 60020 0)) (.whileLtN 60020 60014 cpBody)

/-! ## The root step -/

/-- **The root step**: in the first round, the root code is the code of the root component. -/
def rootS : Stmt :=
  .seq (ldF 60068 13 60010)
    (ifEqN 60068 60011 (.seq (ldF 60069 15 60010)
        (ifEqN 60069 60012 (.seq (codeS 60070 60010) (.instr (.copyN 60024 60070))) .skip)) .skip)

/-! ## The region pass -/

/-- A singleton component finishes: its leaf gets its parent. -/
def singS : Stmt :=
  .seq (stF 13 60020 60010) (.seq (ldF 60071 15 60020)
    (.seq (ifEqN 60071 60012 (block [.addN 60072 60020 60020, .addN 60072 60072 60011])
        (.seq (ldF 60073 14 60020) (.instr (.addN 60072 60073 60073))))
      (.seq (stF 0 60020 60072) (.instr (.addN 60023 60023 60011)))))

/-- A cut component records its new pending slot (best candidate in `60075`). -/
def cutS : Stmt :=
  .seq (ldF 60074 4 60075) (.seq (stF 14 60020 60074) (.seq (ldF 60076 5 60075)
    (ifEqN 60076 60011 (stF 15 60020 60011) (stF 15 60020 60010))))

/-- Region `r` (in `60020`) is a top. -/
def topR : Stmt :=
  .seq (ldF 60077 13 60020)
    (ifEqN 60077 60011 (.seq (ldF 60075 9 60020) (ifEqN 60075 60020 singS cutS)) .skip)

/-- Region `r` (in `60020`) is no top: it becomes one if its parent chord was just cut. -/
def ntR : Stmt :=
  .seq (ldF 60078 4 60020) (.seq (ldF 60079 12 60078)
    (ifEqN 60079 60011 (.seq (stF 13 60020 60011) (.seq (stF 14 60020 60078)
        (.seq (ldF 60080 5 60020) (ifEqN 60080 60011 (stF 15 60020 60010) (stF 15 60020 60011)))))
      .skip))

/-- One step of the region pass. -/
def rpBody : Stmt :=
  .seq (stF 7 60020 60011) (.seq (ldF 60081 8 60020)
    (.seq (ifEqN 60081 60020 topR ntR) (.instr (.addN 60020 60020 60011))))

/-- **The region pass.** -/
def rpS : Stmt := .seq (.instr (.constN 60020 0)) (.whileLtN 60020 60013 rpBody)

/-! ## The rounds -/

/-- **One round.** -/
def roundBody : Stmt :=
  .seq p1S (.seq p2S (.seq cpS (.seq rootS (.seq rpS (.instr (.addN 60022 60022 60011))))))

/-- **The rounds**, while fewer than `R` leaves are finished. -/
def roundsS : Stmt :=
  .seq (block [.constN 60022 0, .constN 60023 0, .constN 60024 0]) (.whileLtN 60023 60013 roundBody)

/-! ## The node table and the header -/

/-- Copy node `k` (in `60020`) to `DB + 3 k`. -/
def fcBody : Stmt :=
  .seq (block [.addN 60082 60020 60020, .addN 60082 60082 60020, .addN 60082 60119 60082])
    (.seq (ldF 60083 16 60020) (.seq (.instr (.storeN 60082 60083))
      (.seq (.instr (.addN 60082 60082 60011)) (.seq (ldF 60083 17 60020)
        (.seq (.instr (.storeN 60082 60083)) (.seq (.instr (.addN 60082 60082 60011))
          (.seq (ldF 60083 18 60020) (.seq (.instr (.storeN 60082 60083))
            (.instr (.addN 60020 60020 60011))))))))))

/-- **The node table.** -/
def fcS : Stmt := .seq (.instr (.constN 60020 0)) (.whileLtN 60020 60014 fcBody)

/-- **The header** of the new normal form at `A`, and the output handle. -/
def hdrS : Stmt := block [
  .copyN 60030 60018, .storeN 60030 60014,
  .addN 60031 60001 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60030 60030 60011, .storeN 60030 60013,
  .addN 60031 60031 60012, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60030 60030 60011, .storeN 60030 60119,
  .addN 60030 60030 60011, .storeN 60030 60024,
  .addN 60030 60030 60011, .storeN 60030 60100,
  .addN 60030 60030 60011, .storeN 60030 60014,
  .copyN 60003 60018]

/-- **The decomposition program.** -/
def decompStmt : Stmt :=
  .seq setupS (.seq allocS (.seq initS (.seq bfsS (.seq roundsS (.seq fcS hdrS)))))

end

end Chazelle.Core.DecR
