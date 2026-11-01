/-
`Lasm.UI.validate` (packages/lasm-ui-check): views checked against the content
models of lean-html-model, while Lean elaborates this file
(scripts/ui/lean-tests.mjs): each `#guard` must hold.
-/
import Lasm.UI
import LasmUICheck
open Lasm.UI

inductive Msg where
  | inc
  | dec

def problem (v : Html Msg) : String :=
  match validate v with
  | .ok () => "ok"
  | .error p => toString p

def ok (v : Html Msg) : Bool := (validate v).isOk

-- Valid views: nesting, order, whitespace, SVG and MathML, transparent `a`.
#guard ok (html! <main class="counter">
          <button onClick={Msg.dec}>-</button>
          <output>{(3 : Nat)}</output>
          <button onClick={Msg.inc}>+</button>
        </main>)
#guard ok (html! <ul>
          <li>a</li>
          <li><p>b</p></li>
        </ul>)
#guard ok (html! <table><caption>c</caption><thead><tr><th>h</th></tr></thead><tbody><tr><td>1</td></tr></tbody></table>)
#guard ok (html! <dl><dt>k</dt><dd>v</dd><dt>k</dt><dt>k</dt><dd>v</dd><dd>v</dd></dl>)
#guard ok (html! <dl><div><dt>k</dt><dd>v</dd></div><div><dt>k</dt><dd>v</dd></div></dl>)
#guard ok (html! <p>Area: <svg viewBox="0 0 2 2"><circle r="1" /></svg> <math><mfrac><mn>1</mn><mn>2</mn></mfrac></math></p>)
#guard ok (html! <div><a href="/"><p>A block link</p></a><p><a href="/">An inline link</a></p></div>)
#guard ok (html! <my-card><p>Custom elements are transparent</p></my-card>)
#guard ok (div [] [ul [] [], text ""])
-- The function DSL, and splices of any kind.
#guard ok (ul [] ([1, 2].map fun i => li [] [text (toString i)]))

-- Invalid views: the element at fault and why.
#guard problem (html! <p><div>x</div></p>) == "<p>[1] > <div>[1]: <div> is not allowed here"
#guard problem (html! <ul>text</ul>) == "<ul>[1]: <ul> does not allow text \"text\" here (child 1)"
#guard problem (html! <div><li>x</li></div>) == "<div>[1] > <li>[1]: <li> is not allowed here"
#guard problem (html! <table><tbody></tbody><thead></thead></table>)
  == "<table>[1]: <table> does not allow <thead> here (child 2)"
#guard problem (html! <dl><dd>v</dd></dl>) == "<dl>[1]: <dl> does not allow <dd> here (child 1)"
-- A `dl`'s groups are either all in `div`s or none are.
#guard problem (html! <dl><dt>k</dt><dd>v</dd><div><dt>k</dt><dd>v</dd></div></dl>)
  == "<dl>[1]: <dl> does not allow <div> here (child 3)"
#guard problem (html! <p><math><mfrac><mn>1</mn></mfrac></math></p>)
  == "<p>[1] > <math>[1] > <mfrac>[1]: <mfrac> needs more children than these"
#guard problem (html! <div><svg><g>text</g></svg></div>)
  == "<div>[1] > <svg>[1] > <g>[1]: <g> does not allow text \"text\" here (child 1)"
#guard problem (node "blink" [] []) == "<blink>[1]: <blink> is not an HTML element"

-- `textContent` replaces the children, and `innerHTML`'s markup is not checked.
#guard ok (ul [stringProp "innerHTML" "<li>x</li>"] [])
#guard problem (ul [stringProp "textContent" "x"] []) == "<ul>[1]: <ul> does not allow text \"x\" here (child 1)"

-- The typed tree is the view: its erasure has the view's tags and text, in a `<div>`.
partial def treeShape : HtmlModel.Web.Tree Unit → String
  | .text s | .verbatim _ s => s
  | .elem e _ _ ch => s!"<{HtmlModel.Web.vocab.name e}>{String.join (ch.map treeShape)}</>"
  | .unchecked _ name _ _ ch => s!"<{name}>{String.join (ch.map treeShape)}</>"

partial def viewShape : Html Msg → String
  | .text s => s
  | .elem _ tag _ _ ch => s!"<{tag}>{String.join (ch.map viewShape)}</>"

def roundTrips (v : Html Msg) : Bool :=
  match toHtmlModel v with
  | .ok n => treeShape n.erase == s!"<div>{viewShape v}</>"
  | .error _ => false

#guard roundTrips (html! <ul> <li>a</li> <li><p>b</p></li> </ul>)
#guard roundTrips (ul [] ((List.range 50).map fun i => li [] [text (toString i)]))
#guard roundTrips (html! <table><caption>c</caption><tbody><tr><td>1</td></tr><tr><td>2</td></tr></tbody></table>)
#guard roundTrips (html! <p>Area: <svg viewBox="0 0 2 2"><circle r="1" /></svg> <math><mfrac><mn>1</mn><mn>2</mn></mfrac></math></p>)
#guard roundTrips (html! <dl><dt>k</dt><dt>k</dt><dd>v</dd><dd>v</dd></dl>)

-- Inside other containers than an app's `<div>`.
#guard (toHtmlModelIn [(html! <li>x</li> : Html Msg)] (.html .ul) (.html .flow)).toOption.isSome
#guard (toHtmlModelIn [(html! <p>x</p> : Html Msg)] (.html .ul) (.html .flow)).toOption.isNone
