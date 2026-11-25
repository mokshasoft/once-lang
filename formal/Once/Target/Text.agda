------------------------------------------------------------------------
-- Once.Target.Text — a file's text, joined in one pass.
--
-- ★ D487: Agda's `String` is strict text, so `a ++ b` copies both. A file built line by line as
-- `line ++ rest` copies the rest at every line: quadratic in the file's size (65% of a large
-- image's compile was that copying; docs/performance-patterns.md B7). A file is its list of
-- pieces, joined once: `toList` each piece, append the lists (linear), `fromList` the result.
------------------------------------------------------------------------

module Once.Target.Text where

open import Data.List using (List; concatMap)
open import Data.String using (String; toList; fromList)

join : List String → String
join ss = fromList (concatMap toList ss)
