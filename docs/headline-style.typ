// Layout for docs/headline.typ, which scripts/trusted.sh generates.
// Everything here is presentation: the content comes from the generator.

// Fonts: Libertinus Serif, which typst embeds, for text and headings, and
// Iosevka Extended for code. The Iosevka files in docs/fonts are subsets made
// by scripts/subset-fonts.sh; scripts/trusted.sh passes that directory to
// typst with --font-path.

// Lean highlighting. The grammar's source and licence are at the top of
// lean4.sublime-syntax. scripts/trusted.sh --check compiles a probe through
// this function and fails if the code comes out in one colour. Inline code
// is 0.8 of the size of the text around it, since typst scales raw text by
// 0.8 under any size set here; code blocks have a fixed size.
#let code-box = block.with(
  fill: luma(247), inset: (x: 5pt, y: 4pt), radius: 2pt, width: 100%, breakable: true,
  above: 0.8em, below: 0.8em)

#let lean-code(body) = {
  set raw(syntaxes: "lean4.sublime-syntax")
  show raw: set text(font: "Iosevka Extended", size: 1em)
  show raw.where(block: true): set text(size: 8pt)
  show raw.where(block: true): code-box
  body
}

// A theorem statement whose names link to their definitions. Each part is a
// piece of the source and the label of the definition it names, or `none`.
// Each piece is highlighted on its own; the pieces split only at names.
// The pieces are inline raw, so they take an absolute size to match the code
// blocks; a size relative to the text would be scaled by 0.8.
#let lean-linked(..parts) = code-box({
  set text(size: 8pt)
  show raw: set text(size: 8pt)
  show link: underline.with(stroke: 0.4pt + luma(150), offset: 1.6pt)
  for (piece, target) in parts.pos() {
    let code = raw(piece, lang: "lean")
    if target == none { code } else { link(label(target), code) }
  }
})

#let body-size = 9.5pt

// Code at a fixed size, for names in headings.
#let code-at(size, body) = {
  show raw: set text(size: size)
  body
}

#let grey(body) = text(size: 7.5pt, fill: luma(100), body)

#let doc(body) = {
  set document(title: "What mise proves")
  set page(paper: "a4", margin: (x: 1.7cm, y: 1.7cm), numbering: "1")
  set text(font: "Libertinus Serif", size: body-size, lang: "en", region: "gb")
  set par(justify: false, spacing: 1.1em, leading: 0.65em)
  set list(spacing: 0.65em, indent: 0.4em)
  set enum(spacing: 0.65em)
  show: lean-code
  show link: set text(fill: rgb("#1f4e9c"))
  set heading(numbering: "1.1.")
  show heading.where(level: 1): set text(size: 13pt)
  show heading.where(level: 1): set block(above: 2.2em, below: 1em)
  show heading.where(level: 2): set text(size: 1.1 * body-size)
  // The size is set here, not in the heading's body, so the contents list
  // shows theorem names at the size of the text around them.
  show heading.where(level: 2): it => code-at(1.1 * body-size, it)
  show heading.where(level: 2): set block(above: 2em, below: 0.4em)
  show heading.where(level: 3): set text(size: body-size)
  show heading.where(level: 3): set block(above: 1.6em, below: 0.45em)
  align(center, text(size: 16pt, weight: "bold")[What `mise` proves])
  v(-0.2em)
  align(center, grey[Generated from the Lean sources by `scripts/trusted.sh`.])
  body
}

#let intro(body) = {
  body
  outline(depth: 2, indent: auto)
}

#let part-sub(body) = block(above: 1em, below: 0.5em, text(weight: "bold", body + ":"))
#let line-par(body) = block(above: 0.6em, below: 0.6em, body)
#let english(body) = block(
  above: 0.9em, below: 0.9em, inset: (left: 8pt, y: 2pt), stroke: (left: 1.2pt + luma(200)), body)

// A source location, linked to the lines on GitHub.
#let source(url, body) = link(url, raw(body))

#let theorem-heading(name, file, line, url) = {
  heading(level: 2, raw(name))
  block(above: 0.3em, below: 0.8em, sticky: true, grey(source(url, file + ":" + str(line))))
}

#let defs-intro = [
  This part shows the definitions that a core statement names, and the definitions that those name in turn, file by file in import order. The printer and the parser appear, but the definitions they use do not.
]

// A file of definitions: a numbered subsection, listed in the contents.
#let file-heading(file) = heading(level: 2, raw(file))

// One definition: a numbered heading, left out of the contents, with the name
// and location on one line. Then the docstring without its `Gloss:` lines,
// kept on the page of the code that follows.
#let def-head(name, lbl, file, a, b, url, body) = {
  [#heading(level: 3, outlined: false)[#raw(name) #h(0.3em) #text(weight: "regular", grey(source(url, file + ":" + str(a) + "–" + str(b))))]#label(lbl)]
  block(above: 0.45em, below: 0.5em, sticky: true, width: 100%)[
  #body
  ]
}

#let no-doc = text(fill: red)[No docstring.]

#let warnings-intro = [These names appear in a statement but have no `Gloss:` template, so the English shows them in Lean notation.]

#let omits-intro = [Templates leave these explicit arguments, other than `sem`, out of the English.]
