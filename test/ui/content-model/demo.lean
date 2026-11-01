/- examples/ui/demo's views satisfy the content model (scripts/ui/lean-tests.mjs). -/
import Main
import LasmUICheck
open Lasm.UI

#guard [Page.home, .about, .item 3 none, .item 3 (some "x"), .notFound].all fun page =>
  (validate (view { page })).isOk &&
    (validate (view { page, http := "x", delayed := "y", ticking := true, name := "n", received := "r" })).isOk
#guard (validate (view { page := .home, ssr := true })).isOk
