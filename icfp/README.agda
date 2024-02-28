module README where

-- Chapter 3.2 All-or-Nothing Counters
import AllOrNothing
-- Chapter 3.3 Application Counters
import Application
-- Chapter 3.4 All in One (completeness results)
import AllInOne

-- Chapter 3.4 (Full Calculus)
import STLC.Decl
import STLC.Decl.Properties

-- Chapter 3.5 (Annotatability)
import STLC.Annotatability

-- Chapter 4.3
import STLC.Algo
import STLC.Algo.Properties
import STLC.Algo.Decidable

-- Chapter 4.4
import STLC.Soundness
import STLC.Completeness

-- Chapter 5.1 Syntax
import Record.Common

-- Chapter 5.2 QTAS
import Record.Decl
import Record.Decl.Properties

-- Chapter 5.3 Algo
import Record.Algo
import Record.Algo.Properties

-- Chapter 5.4
-- soundness and completeness
import Record.Soundness
import Record.Completeness
-- annotatability
import Record.Annotatability.Elaboration

-- type soundness
-- perservation after erasure
import TypeSound.Main
-- preservation and progress of TAS
import TypeSound.Target

-- determinism of typing and subtyping
import Record.Algo.Uniqueness
-- decidability of typing and subtyping
import Record.Algo.Decidable

-- decidability of QTAS
import Record.Dec
