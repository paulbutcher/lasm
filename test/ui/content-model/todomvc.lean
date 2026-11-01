/- examples/ui/todomvc's views satisfy the content model (scripts/ui/lean-tests.mjs). -/
import Main
import LasmUICheck
open Lasm.UI Todo

def items : List Item := [{ id := 0, title := "a", completed := false }, { id := 1, title := "b", completed := true }]

#guard [({} : Model), { todos := items }, { todos := items, editing := some (0, "a") },
  { todos := items, filter := .completed }].all fun m => (validate (view m)).isOk
