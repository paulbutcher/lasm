/- examples/ui/bench's views satisfy the content model (scripts/ui/lean-tests.mjs). -/
import Main
import LasmUICheck
open Lasm.UI

#guard [({} : Model), update .run {}, update (.select 1) (update .run {})].all fun m => (validate (view m)).isOk
