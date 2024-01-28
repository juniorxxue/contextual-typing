module Everything where

import Traditional.Prelude
import Traditional.Common
import Traditional.Properties
import Traditional.Decl
import Traditional.Decl.Properties
import Traditional.Algo
import Traditional.Algo.Properties
import Traditional.Completeness
import Traditional.Soundness

import STLC.Prelude
import STLC.Common
import STLC.Properties
import STLC.Decl
import STLC.Decl.Properties
import STLC.Algo
import STLC.Algo.Properties
import STLC.Completeness
import STLC.Soundness

import Intersection.Prelude
import Intersection.Common
import Intersection.Properties
import Intersection.Decl
import Intersection.Decl.Properties
import Intersection.Algo
import Intersection.Algo.Properties
import Intersection.Completeness
import Intersection.Soundness

import Record.Prelude
import Record.Common
import Record.Properties
import Record.Decl
import Record.Decl.Properties
import Record.Algo
import Record.Algo.Properties
import Record.Completeness
import Record.Soundness

-- elaboration semantics
import TypeSound.Elaboration.STLC.Common
import TypeSound.Elaboration.STLC.Source
import TypeSound.Elaboration.STLC.Target
import TypeSound.Elaboration.STLC.Main

import TypeSound.Elaboration.Intersection.Common
import TypeSound.Elaboration.Intersection.Source
import TypeSound.Elaboration.Intersection.Target
import TypeSound.Elaboration.Intersection.Main

import TypeSound.Elaboration.Overloading.Common
import TypeSound.Elaboration.Overloading.Source
import TypeSound.Elaboration.Overloading.Target
import TypeSound.Elaboration.Overloading.Main

-- operational semantics
import TypeSound.Operation.STLC

-- our typing is complete over Let arguments go first
-- and traditional bidirectional typing (with two application rules)
import Complete.Prelude
import Complete.LetArg
import Complete.Trad

----------------------------------------------------------------------
--+                                                                +--
--+                      Warning: Unfinished!                      +--
--+                                                                +--
----------------------------------------------------------------------

-- import TypeSound.Operation.Intersection
import Poly.Prelude
import Poly.Main
