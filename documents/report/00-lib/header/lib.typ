#import "@preview/gruvy:2.1.0": gruvbox, theme-colors, colors
#import "@preview/theorion:0.4.1": *
#import "@preview/zebraw:0.6.0": *
#import cosmos.clouds: *
#import cosmos.clouds: render-fn as render-fn2

#let theme = theme-colors.light.hard;
#let remark = remark.with(fill: theme.muted.blue)
#let tip-box = tip-box.with(fill: theme.strong.green)
#let caution-box = caution-box.with(fill: theme.muted.red)
#let warning-box = warning-box.with(fill: theme.muted.yellow)
#let theorem = theorem.with(fill: theme.muted.blue.lighten(80%))
#let lemma = lemma.with(fill: theme-colors.dark.soft.strong.blue.lighten(80%))
#let corollary = corollary.with(fill: theme-colors.dark.soft.muted.aqua.lighten(80%))
#let (example-counter, example-box, example, show-example) = make-frame(
  "definition",
  theorion-i18n-map.at("example"),
  counter: none,
  render: render-fn2.with(fill: theme.bg0.lighten(30%)),
)
#let todo-box = note-box.with(
  fill: theme.strong.aqua,
  title: "To-Do",
  icon-name: "pencil",
)
#let remark = remark.with(
  fill: theme.strong.aqua,
)

#set text(lang: "en")

#show: show-theorion
#show: zebraw.with(
    background-color: theme.bg0,
    lang-color: theme-colors.dark.soft.strong.blue,
)
#show: gruvbox.with(
    theme-color: theme,
    accent: theme.strong.blue,
    hl: theme.muted.yellow,
    print: true,
)
#show ref: set text(fill: theme.fg1)

// Math
#let meq = math.eq.quest;
#let wildcard = underline("  ")
#let prover = math.cal("P")
#let verifier = math.cal("V")
#let circuit = math.cal("C")
#let Oc = math.cal("O")
#let Xc = math.cal("X")
#let bits = math.bb("B")
#let Fb = math.bb("F")
#let inrand = $attach(in, br: R)$
#let vec(body) = $bold(body)$
#let innerprod(A, B) = $chevron.l #A, #B chevron.r$
#let hadamard = $dot.o$

