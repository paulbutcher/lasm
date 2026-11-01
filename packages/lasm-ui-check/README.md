# lasm-ui-check: content-model checking for Lasm.UI views

`Lasm.UI.validate` checks an `Html Msg` view against the content models of the
HTML Living Standard, SVG 2 and MathML Core, using
[lean-html-model](https://github.com/paulbutcher/lean-html-model): a `<div>` in
a `<p>`, text directly in a `<ul>`, a `<thead>` after a `<tbody>`, an `<li>`
outside a list, or an `<mfrac>` with one child is reported with the path to the
element at fault.

```lean
import Lasm.UI
import LasmUICheck
open Lasm.UI

#guard (validate (view initialModel)).isOk

#eval validate (html! <p><div>x</div></p> : Html Unit)
-- .error <p>[1] > <div>[1]: <div> is not allowed here
```

Such a view is not only invalid HTML: the browser's parser repairs it, so the
page a server renders (`Lasm.UI.render`) parses to a different DOM than the
view, and hydration replaces the nodes that do not match.

It works on any view (`html!`, the function DSL, `Html.map`ped components)
after it is built, so it checks what a model actually produces: run it in
`#guard`s and tests over the models you care about. It is not used at run time.

## Install

A Lake package, built with Lasm's Lean (whose library provides `Lasm.UI`): add
it to the `lakefile.toml` of an app that `lasm build`s with Lake.

```toml
[[require]]
name = "lasm-ui-check"
git = "https://github.com/Millillion/lasm"
subDir = "packages/lasm-ui-check"
rev = "main"
```

Lake fetches lean-html-model 0.4.1 and lean-regular 0.2.1 with it. A single-file
app without a `lakefile` cannot use it.

## API

| | |
| --- | --- |
| `validate (view : Html Msg) : Except ContentModel.Problem Unit` | `view` inside an app's mount point, a `<div>` holding flow content |
| `toHtmlModel (view) : Except Problem (HtmlModel.Web.Node Unit (.html .flow))` | the same, returning lean-html-model's typed node |
| `toHtmlModelIn (views) (e := .html .div) (c := .html .flow)` | children of another element `e`, placed as category `c` |
| `ContentModel.Problem` | `path` (tags from the outermost, each with its position among its siblings) and `message`; `toString` joins them |

`toHtmlModel_valid`: the erasure of the node `toHtmlModel` returns satisfies
lean-html-model's `Tree.Valid`, which is stated on the erased tree alone. It
follows from lean-html-model's `Node.valid_erase`, since the node is built with
a proof for every element that its content model admits its children.

## What is checked

- Every element's direct children, in order and number, against its content
  model, each element's category chosen from its parent and its children (`a`
  holds flow or phrasing content as its context allows, a `div` in a `dl` is a
  group of terms and descriptions). Inter-element whitespace is ignored where
  the content model is not phrasing content.
- Element names: an unknown HTML, SVG or MathML element is reported. A name with
  a `-` is a custom element, whose content model is the standard's transparent
  one.
- An element with a `textContent` property is checked as holding that text, and
  one with `innerHTML` where it stands but not inside, since its markup is not
  part of the view.

Not checked: attributes, rules on descendants rather than children (no
interactive content inside `a`), and rules that depend on attributes (`link`
and `meta` in the body), none of which lean-html-model models.
