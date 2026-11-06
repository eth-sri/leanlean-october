module

public import Chazelle.Core.NFBuildWtRam
public import Chazelle.Core.NFBuildEvCmp

/-!
# WP-C (BuildNF), RAM part 8: the program of the main pass

The main pass reads the sorted codes `E` (at `r43104 = SE`, cursor `r43103 = SE + m`) once, with
a stack of chord indices plus one (`r44006 = ST`, size `r43101`):

* `curS`: the code `c = E[m]`, its walk position (`r42110`, `r42111`), parity (`r42112`), chord
  `x` (`r43113`) and `x + 1` (`r43114`);
* `topS dst`: the region index of the label (`0` for an empty stack, else the top);
* `stepS`: pop if the top is `x + 1`, else write the chord record of `x` at `CT + 5 x`
  (`r44001 = CT`; `up`/`dn` from the parity and the label `r43115`) and push `x + 1`;
* `gapS`: if the key strictly increases from `E[m]` to `E[m + 1]` (`halfS`), or at the last
  position (the wrap, end `E[0]`), `arcS` writes the arc record at `AT + 5 A` (`r44002 = AT`,
  count `r43102`: region `r43117`, both ends) and its weight at `WT + A` (`r44007 = WT`), with the
  parameter test `pzR` and `wtS`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The current code, its record and its chord. -/
def curS : Stmt :=
  .seq (.instr (.loadN 43110 43103))
    (.seq (loadRec 43110 43111 42110)
      (block [.addN 43111 43111 42102, .loadN 43113 43111, .addN 43114 43113 43011]))

/-- The region index of the label into `dst`. -/
def topS (dst : ℕ) : Stmt :=
  .ifLtN 43010 43101 (block [.addN 43116 44006 43101, .subN 43116 43116 43011, .loadN dst 43116])
    (.instr (.constN dst 0))

/-- The chord record of `x = r43113` at `CT + 5 x`. -/
def chordS : Stmt :=
  .seq (block [.addN 43130 43113 43113, .addN 43130 43130 43113, .addN 43130 43130 43001,
      .loadN 43131 43130, .addN 43130 43130 43011, .loadN 43132 43130, .addN 43130 43130 43011,
      .loadN 43133 43130,
      .addN 43134 43113 43113, .addN 43134 43134 43134, .addN 43134 43134 43113,
      .addN 43134 43134 44001,
      .storeN 43134 43131, .addN 43134 43134 43011, .storeN 43134 43132,
      .addN 43134 43134 43011, .storeN 43134 43133, .addN 43134 43134 43011])
    (.ifLtN 42112 43011
      (block [.storeN 43134 43115, .addN 43134 43134 43011, .storeN 43134 43114])
      (block [.storeN 43134 43114, .addN 43134 43134 43011, .storeN 43134 43115]))

/-- Push `x + 1` after writing the chord record. -/
def pushS : Stmt :=
  .seq chordS (block [.addN 43116 44006 43101, .storeN 43116 43114, .addN 43101 43101 43011])

/-- Pop. -/
def popS : Stmt := .instr (.subN 43101 43101 43011)

/-- One step of the stack pass. -/
def stepS : Stmt := .ifLtN 43115 43114 pushS (.ifLtN 43114 43115 pushS popS)

/-- The arc record at `AT + 5 A` and its weight at `WT + A`. -/
def arcS : Stmt :=
  .seq (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
      .addN 43150 43150 44002,
      .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
      .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
      .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
      .copyN 41110 42113, .copyN 41111 42114])
    (.seq pzR (.seq wtS
      (block [.addN 43151 44007 43102, .storeN 43151 43121, .addN 43102 43102 43011])))

/-- The gap test and the arc. -/
def gapS : Stmt :=
  .seq (.instr (.addN 43106 43100 43011))
    (.ifLtN 43106 42001
      (.seq (block [.addN 43140 43103 43011, .loadN 43141 43140])
        (.seq (loadRec 43141 43142 42113)
          (.seq (halfS 42110 42111 42113 42114 42116 42117)
            (.ifLtN 42117 43011 (.seq (.instr (.constN 43120 1)) arcS) .skip))))
      (.seq (.instr (.loadN 43141 43104))
        (.seq (loadRec 43141 43142 42113) (.seq (.instr (.constN 43120 0)) arcS))))

/-- The body of the main pass. -/
def passBody : Stmt :=
  .seq curS (.seq (topS 43115) (.seq stepS (.seq (topS 43117) (.seq gapS
    (block [.addN 43100 43100 43011, .addN 43103 43103 43011])))))

/-- **The main pass.** -/
def passLoop : Stmt := .whileLtN 43100 42001 passBody

end

end BuildRam

end Chazelle.Core
