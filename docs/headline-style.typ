// Layout for docs/headline.typ, which scripts/trusted.sh generates.
// Everything here is presentation: the content comes from the generator.

// Lean highlighting. The grammar's source and licence are at the top of
// lean4.sublime-syntax. scripts/trusted.sh --check compiles a probe through
// this function and fails if the code comes out in one colour.
#let lean-code(body) = {
  set raw(syntaxes: "lean4.sublime-syntax")
  show raw: set text(font: "DejaVu Sans Mono", size: 8.5pt)
  show raw.where(block: true): block.with(
    fill: luma(247), inset: 6pt, radius: 2pt, width: 100%, breakable: true)
  body
}

#let doc(body) = {
  set document(title: "What mise proves")
  set page(paper: "a4", margin: (x: 2.2cm, y: 2.4cm), numbering: "1")
  set text(size: 10pt, lang: "en", region: "gb")
  set par(justify: false)
  show: lean-code
  show link: set text(fill: rgb("#1f4e9c"))
  set heading(numbering: none)
  show heading.where(level: 1): it => { pagebreak(weak: true); it; v(0.4em) }
  align(center, text(size: 18pt, weight: "bold")[What `mise` proves])
  align(center, text(size: 9pt)[Generated from the Lean sources by `scripts/trusted.sh`.])
  v(1em)
  outline(depth: 2, indent: auto)
  body
}

#let how-to-read = block(inset: (left: 0pt))[
  Each theorem below shows its docstring, its statement as it appears in the source, and an English translation. A program, `test/MiseTest/Gloss.lean`, writes the translation from the elaborated statement: fixed phrases for the logical connectives, and for each named definition the template on the `Gloss:` line of its docstring. The templates are listed with the definitions. A name without a template appears in Lean notation and is listed under Warnings. Parenthesised groups in the translation mark the extent of each argument.
]

#let part(body) = block(above: 0.9em, below: 0.4em, text(weight: "bold", size: 9pt, body))
#let part-sub(body) = block(above: 0.5em, below: 0.3em, text(style: "italic", body))
#let english(body) = block(inset: (left: 8pt), stroke: (left: 1.5pt + luma(200)), body)

#let theorem-heading(name, file, line) = {
  heading(level: 2, raw(name))
  text(size: 8.5pt, fill: luma(90), raw(file + ":" + str(line)))
}

#let def-heading(name, lbl, file, a, b) = [
  #heading(level: 3, outlined: false, raw(name)) #label(lbl)
  #text(size: 8.5pt, fill: luma(90), raw(file + ":" + str(a) + "–" + str(b)))
]

#let no-doc = text(fill: red)[No docstring.]

#let template(kind, t) = block(above: 0.6em)[
  #text(weight: "bold", size: 9pt, kind + ":") #raw(t)
]

#let uses(body) = block(above: 0.4em, text(size: 9pt)[Uses: #body.])

#let trusted-intro(n, lines) = [
  The definitions the statements rest on: every `Mise` constant a statement mentions, followed through definitions and inductive types but not into proofs. Lean's core library is not listed. There are #n declarations, #lines lines in all. Each file uses only the ones before it.
]

#let warnings-intro = [
  These names appear in a statement but have no `Gloss:` template, so the translation shows them in Lean notation.
]

#let omits-intro = [
  These arguments are left out of a template, so the translation does not mention them.
]
