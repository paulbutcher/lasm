/-
Content-model checking for `Html Msg` views with lean-html-model
(https://github.com/paulbutcher/lean-html-model): every element's children
are checked against the HTML Living Standard's content model for it, SVG 2's
and MathML Core's included, as far as its direct children go.

    #guard (validate (html! <p><div></div></p> : Html Msg)).isOk == false

A view is placed into lean-html-model's typed tree, choosing each element's
category from its parent and its children as `html!` would; a view that cannot
be placed is reported with the path to the element at fault. Placing it proves
it valid: `toHtmlModel` returns a typed node, whose erasure satisfies
`HtmlModel.Tree.Valid` (`toHtmlModel_valid`).

Attributes, keys and handlers are not checked, nor are rules on descendants
rather than children (no interactive content inside `a`) or rules that depend
on attributes. An element with an `innerHTML` property is checked where it
stands but not inside; one with `textContent` is checked as holding that text.
-/
import HtmlModel
import Lasm.UI.Html

namespace Lasm.UI.ContentModel

open HtmlModel HtmlModel.Web Regular

/-- A view that does not satisfy the content model: the element at fault, as the
path of tags from the outermost (each with its position among its siblings,
from 1), and why. -/
structure Problem where
  path : List String
  message : String
  deriving Repr, BEq

instance : ToString Problem where
  toString p := s!"{" > ".intercalate p.path}: {p.message}"

/-- A node placed in the typed tree, with the category it was placed as. -/
abbrev Placed := (c : Cat) × Web.Node Unit c

def namespaceOf : Ns → Namespace
  | .html => .html
  | .svg => .svg
  | .mathml => .mathml

def nsTitle : Ns → String
  | .html => "HTML"
  | .svg => "SVG"
  | .mathml => "MathML"

/-- The element a tag names in a namespace. `svg` and `math` are found from HTML
too, as the function DSL may create them there. -/
def elemOf? : Ns → String → Option Elem
  | .html, "svg" => some (.svg .svg)
  | .html, "math" => some (.mathml .math)
  | .html, tag =>
    match HtmlModel.Html.Elem.ofName? tag with
    | some e => some (.html e)
    | none => if h : isCustomElementName tag = true then some (.custom tag h) else none
  | .svg, tag => (Svg.Elem.ofName? tag).map .svg
  | .mathml, tag => (Mathml.Elem.ofName? tag).map .mathml

def describe : Html Msg → String
  | .text s => if isWhitespace s then "whitespace" else s!"text {repr s}"
  | .elem _ tag .. => s!"<{tag}>"

def step (tag : String) (i : Nat) : String := s!"<{tag}>[{i + 1}]"

/-- What an element's children are in the DOM. -/
inductive Content where
  /-- Those of the view. -/
  | view
  /-- The text of a `textContent` property, which replaces them. -/
  | text (s : String)
  /-- The markup of an `innerHTML` property, which replaces them and is not checked. -/
  | markup

/-- An element's content: the last `textContent` or `innerHTML` property wins, as
in the DOM. -/
def contentOf (attrs : List (Attr Msg)) : Content :=
  attrs.foldl (init := .view) fun acc a =>
    match a with
    | .prop "innerHTML" (.str _) => .markup
    | .prop "textContent" (.str s) => .text s
    | _ => acc

/-- Text as a placed node: inter-element whitespace if it is all whitespace. -/
def placeText (s : String) : Placed :=
  if h : isWhitespace s = true then ⟨_, Web.ws s h⟩ else ⟨_, .text s⟩

/-- The least of the categories placed, which widens to every other, or else the first. -/
def least (placed : List Placed) : Option Placed :=
  (placed.find? fun p => placed.all fun q => vocab.widens p.1 q.1).orElse fun _ => placed.head?

/-- The least of these categories, or else the first. -/
def least' (cats : List Cat) : Option Cat :=
  (cats.find? fun c => cats.all (vocab.widens c)).orElse fun _ => cats.head?

/-- Why `e` as `c` rejects children of these categories. -/
def rejectionMessage (tag : String) (children : List (Html Msg)) (kids : List Placed) (e : Elem)
    (c : Cat) : String :=
  match vocab.rejection e c (kids.map fun k => .one k.1) with
  | some (.unexpected i _) =>
    let child := (children[i]?.map describe).getD "a child"
    s!"<{tag}> does not allow {child} here (child {i + 1})"
  | _ => s!"<{tag}> needs more children than these"

/-- Children as segments, consecutive children of one category (the rows of a
table, the items of a list) as one segment of one or more. -/
def runs : List Placed → List ((k : SegK Cat) × Seg vocab.sig Unit k)
  | [] => []
  | ⟨c, n⟩ :: ps => go c n [] ps
where
  close (c : Cat) (first : Web.Node Unit c) (more : List (Web.Node Unit c)) :
      (k : SegK Cat) × Seg vocab.sig Unit k :=
    if more.isEmpty then ⟨.one c, .one first⟩ else ⟨.many1 c, .many1 first (Nodes.ofList more.reverse)⟩
  go (c : Cat) (first : Web.Node Unit c) (more : List (Web.Node Unit c)) :
      List Placed → List ((k : SegK Cat) × Seg vocab.sig Unit k)
    | [] => [close c first more]
    | ⟨d, m⟩ :: ps => if h : d = c then go c first ((h ▸ m) :: more) ps else close c first more :: go d m [] ps

/-- `e` as category `c`, holding the placed children `kids` (`children` in the
view), if its content model admits them. Runs of children of one category are
checked first as segments of one or more, which their content model admitting
implies it admits them, in time that does not grow with their length; then, if
that fails (`mfrac` takes exactly two expressions), one by one. -/
def admit (e : Elem) (c : Cat) (tag : String) (path : List String) (children : List (Html Msg))
    (kids : List Placed) : Except Problem Placed :=
  if hc : c ∈ vocab.cats e then
    let coarse := runs kids
    if ok : vocab.Admits e c (coarse.map (·.1)) then
      pure ⟨c, Web.elem e c () (Segs.ofList coarse) hc ok⟩
    else if ok : vocab.Admits e c (kids.map fun k => .one k.1) then
      pure ⟨c, Web.elem e c () (Segs.ofList (kids.map fun k => ⟨.one k.1, .one k.2⟩)) hc
        (by simpa [Function.comp_def] using ok)⟩
    else throw ⟨path, rejectionMessage tag children kids e c⟩
  else throw ⟨path, s!"<{tag}> is not allowed here"⟩

/-- The categories `e` may take inside a parent whose content model is `parent`. -/
def fitting (e : Elem) (parent : Regex Cat) : List Cat :=
  (vocab.cats e).filter fun c => parent.letters.any (vocab.widens c)

/-- The first success, preferring the least category, or else the first failure. -/
def choose (tag : String) (path : List String) (attempts : List (Except Problem Placed)) :
    Except Problem Placed :=
  match least (attempts.filterMap Except.toOption), attempts.head? with
  | some p, _ => pure p
  | none, some (.error p) => throw p
  | none, _ => throw ⟨path, s!"<{tag}> is not allowed here"⟩

mutual
/-- Places `h`, at `path` (outermost first), inside a parent whose content
model is `parent`. -/
def place (parent : Regex Cat) (path : List String) : Html Msg → Except Problem Placed
  | .text s => pure (placeText s)
  | .elem ns tag _ attrs children => do
    let some e := elemOf? ns tag
      | throw ⟨path, s!"<{tag}> is not an {nsTitle ns} element"⟩
    let fits := fitting e parent
    if fits.isEmpty then throw ⟨path, s!"<{tag}> is not allowed here"⟩
    match contentOf attrs with
    | .view => choose tag path (fits.map fun c => do
        admit e c tag path children (← placeAll (vocab.spec e c).grammar path 0 children))
    | .text s => choose tag path (fits.map fun c => admit e c tag path ([.text s] : List (Html Msg)) [placeText s])
    | .markup =>
      let some c := least' fits | throw ⟨path, s!"<{tag}> is not allowed here"⟩
      if hname : (namespaceOf ns).validName tag = true then
        pure ⟨c, Web.unchecked (namespaceOf ns) tag c () .nil hname⟩
      else throw ⟨path, s!"<{tag}> is not a valid element name"⟩

/-- Places `children`, the `i`th child onwards, of the element at `path`. -/
def placeAll (parent : Regex Cat) (path : List String) (i : Nat) :
    List (Html Msg) → Except Problem (List Placed)
  | [] => pure []
  | h :: hs => do
    let here := match h with
      | .elem _ tag .. => path ++ [step tag i]
      | .text _ => path
    pure ((← place parent here h) :: (← placeAll parent path (i + 1) hs))
end

end Lasm.UI.ContentModel

namespace Lasm.UI

open HtmlModel HtmlModel.Web ContentModel

/-- `views` as lean-html-model's typed children of element `e` placed as
category `c`, checked against its content model: by default a `<div>` holding
flow content, as an app's mount point is. -/
def toHtmlModelIn (views : List (Html Msg)) (e : Elem := .html .div) (c : Cat := .html .flow)
    : Except Problem (Web.Node Unit c) := do
  let tag := vocab.name e
  let ⟨c', n⟩ ← admit e c tag [] views (← placeAll (vocab.spec e c).grammar [] 0 views)
  if h : c' = c then pure (h ▸ n) else throw ⟨[], s!"<{tag}> is not allowed here"⟩

/-- `view` as lean-html-model's typed tree, inside an app's mount point (a
`<div>`), or the problem that keeps it from being one. -/
def toHtmlModel (view : Html Msg) : Except Problem (Web.Node Unit (.html .flow)) :=
  toHtmlModelIn [view]

/-- Checks `view` against the content model, inside an app's mount point. -/
def validate (view : Html Msg) : Except Problem Unit :=
  (toHtmlModel view).map fun _ => ()

/-- A view `toHtmlModel` accepts is valid: its erasure satisfies lean-html-model's
`Tree.Valid`, stated on the erased tree alone. -/
theorem toHtmlModel_valid {view : Html Msg} {n : Web.Node Unit (.html .flow)}
    (_ : toHtmlModel view = .ok n) : n.erase.Valid :=
  n.valid_erase

end Lasm.UI
