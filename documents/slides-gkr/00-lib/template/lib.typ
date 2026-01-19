// This theme is inspired by https://github.com/matze/mtheme
// The Polylux-port was originally performed by https://github.com/Enivex

#import "@preview/polylux:0.4.0": *
#import "@preview/gruvy:2.1.0": gruvbox, theme-colors, colors

#let theme = theme-colors.light.hard;

#let bright = theme.muted.green
#let brighter = theme.strong.aqua

#let slide-title-header = toolbox.next-heading(h => {
  show: toolbox.full-width-block.with(fill: theme.strong.blue, inset: 1em)
  set align(horizon)
  set text(fill: page.fill, size: 1.2em)
  strong(h)
})

#let the-footer(content) = {
  set text(size: 0.8em)
  show: pad.with(.8em)
  set align(bottom)
  context text(fill: text.fill.lighten(40%), content)
  h(1fr)
  [ #toolbox.slide-number / #toolbox.last-slide-number ]
}

#let outline = toolbox.all-sections((sections, _current) => {
  enum(tight: false, ..sections)
})

#let progress-bar = toolbox.progress-ratio( ratio => {
  set grid.cell(inset: (y: .03em))
  grid(
    columns: (ratio * 100%, 1fr),
    grid.cell(fill: bright)[],
    grid.cell(fill: brighter)[],
  )
})

#let new-section(name) = slide({
  set page(header: none, footer: none)
  show: pad.with(20%)
  set text(size: 1.5em)
  name
  toolbox.register-section(name)
  progress-bar
})

#let focus(body) = context {
  set page(header: none, footer: none, fill: theme.strong.blue, margin: 2em)
  set text(fill: theme.bg1, size: 1.5em)
  set align(center)
  body
}

#let divider = line(length: 100%, stroke: .1em + bright)

#let setup(
  footer: none,
  text-font: "Fira Sans",
  math-font: "Fira Math",
  code-font: "Fira Code",
  text-size: 23pt,
  body,
) = {
  set page(
    paper: "presentation-4-3",
    fill: theme.bg0,
    margin: (top: 3em, left: 3em, right: 3em, rest: 1em),
    footer: the-footer(footer),
    header: slide-title-header,
  )
  set text(
    font: text-font,
    weight: "light", // looks nice but does not match Fira Math
    size: text-size,
    fill: theme.fg0, // dark teal
  )
  set strong(delta: 100)
  show math.equation: set text(font: math-font)
  show raw: set text(font: code-font)
  set align(horizon)
  show emph: it => text(fill: brighter, style: "italic", it.body)
  show heading.where(level: 1): _ => none

  body
}
