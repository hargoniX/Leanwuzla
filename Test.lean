/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Test.Bitwuzla
import Test.Model
import Test.ParserLCtx
-- `Test.Parser` exercises the legacy `Leanwuzla.Parser`. It cannot be imported
-- here together with the `Leanwuzla.ParserLCtx`-based tests, because the two
-- parsers declare the same names; build it separately via
-- `lake build Test.Parser`.
