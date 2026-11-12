// Layout for docs/headline.typ, which scripts/trusted.sh generates.
// Everything here is presentation: the content comes from the generator.

// Lean highlighting. The grammar's source and licence are at the top of
// lean4.sublime-syntax. scripts/trusted.sh --check compiles a probe through
// this function and fails if the code comes out in one colour. Inline code
// scales with the text around it; code blocks have a fixed size.
#let lean-code(body) = {
  set raw(syntaxes: "lean4.sublime-syntax")
  show raw: set text(font: "DejaVu Sans Mono", size: 0.86em)
  show raw.where(block: true): set text(size: 8pt)
  show raw.where(block: true): block.with(
    fill: luma(247), inset: (x: 4pt, y: 3pt), radius: 2pt, width: 100%, breakable: true)
  body
}

#let grey(body) = text(size: 7.5pt, fill: luma(100), body)

#let doc(body) = {
  set document(title: "What mise proves")
  set page(paper: "a4", margin: (x: 1.7cm, y: 1.7cm), numbering: "1")
  set text(size: 9.5pt, lang: "en", region: "gb")
  set par(justify: false, spacing: 0.6em, leading: 0.5em)
  set list(spacing: 0.4em, indent: 0.2em)
  set enum(spacing: 0.4em)
  show: lean-code
  show link: set text(fill: rgb("#1f4e9c"))
  set heading(numbering: none)
  show heading.where(level: 1): set text(size: 12pt)
  show heading.where(level: 1): set block(above: 1.2em, below: 0.6em)
  show heading.where(level: 2): set text(size: 10.5pt)
  show heading.where(level: 2): set block(above: 1em, below: 0.3em)
  align(center, text(size: 16pt, weight: "bold")[What `mise` proves])
  v(-0.4em)
  align(center, grey[Generated from the Lean sources by `scripts/trusted.sh`.])
  body
}

#let how-to-read = [
  The English under each statement is written by `test/MiseTest/Gloss.lean` from the elaborated statement, with each definition's `Gloss:` template; a linked phrase leads to its definition. Parentheses mark an argument that contains a connective, and templates leave out `sem`, the meaning of commands.
]

#let intro(body) = {
  body
  how-to-read
  outline(depth: 1, indent: auto)
}

#let part-sub(body) = block(above: 0.45em, below: 0.3em, text(weight: "bold", body + ":"))
#let line-par(body) = block(above: 0.3em, below: 0.3em, body)
#let english(body) = block(
  above: 0.5em, inset: (left: 7pt), stroke: (left: 1.2pt + luma(200)), body)

#let theorem-heading(name, file, line) = {
  heading(level: 2, raw(name))
  block(above: 0.2em, below: 0.4em, sticky: true, grey(raw(file + ":" + str(line))))
}

#let defs-intro = [
  The definitions a core statement names, and the ones they name in turn, in import order. The printer and the parser are shown but not expanded.
]

#let file-heading(file) = block(
  above: 1em, below: 0.4em, sticky: true, text(size: 8.5pt, weight: "bold", fill: luma(70), raw(file)))

// One definition: name and location on one line, then the docstring and the
// templates, kept on the page of the code that follows.
#let def-head(name, lbl, file, a, b, glosses, body) = block(
  above: 0.8em, below: 0.3em, sticky: true, width: 100%)[
  #box[#strong(raw(name))#label(lbl)] #h(0.3em) #grey(raw(file + ":" + str(a) + "–" + str(b)))
  #v(0.25em, weak: true)
  #body
  #if glosses.len() > 0 [
    #v(0.25em, weak: true)
    #grey(glosses.map(((k, t)) => [#raw(k + ":") #raw(t)]).join(h(1em)))
  ]
]

#let no-doc = text(fill: red)[No docstring.]

#let omitted(n, total, names) = block(above: 1em)[
  #strong[Not shown.] The other #n of the #total trusted declarations, which the ones above use: #names. `docs/trusted.md` lists all of them with their sources; the printer and parser among them are covered by the round trip in `meaning` and by `test/stage3-diff.sh` against Ninja.
]

#let other-theorem(name, file, line, body) = block(above: 0.7em)[
  #strong(raw(name)) #h(0.3em) #grey(raw(file + ":" + str(line)))
  #v(0.25em, weak: true)
  #body
]

#let warnings-intro = [Names in a statement with no `Gloss:` template, shown in Lean notation.]

#let omits-intro = [Arguments a template leaves out of the English.]
