/- examples/ui/counter's views satisfy the content model (scripts/ui/lean-tests.mjs). -/
import Main
import LasmUICheck
open Lasm.UI

#guard [0, 1, 3].all fun n => (validate (view n)).isOk
