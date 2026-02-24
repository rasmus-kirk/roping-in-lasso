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
#let slop-box = note-box.with(
  fill: theme.strong.aqua,
  title: "SlopBox",
  icon-name: "dependabot",
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
#let prover = math.scr("P")
#let verifier = math.scr("V")
#let circuit = math.scr("C")
#let Ac = math.scr("A")
#let Oc = math.scr("O")
#let Xc = math.scr("X")
#let Rc = math.scr("R")
#let Ec = math.scr("E")
#let iff = text(style: "oblique", "iff")
#let bits = math.bb("B")
#let Fb = math.bb("F")
#let Eb = math.bb("E")
#let Nb = math.bb("N")
#let nats = math.bb("N")
#let Nat = math.bb("N")
#let Bool = math.bb("B")
#let inrand = $attach(in, br: R)$
#let vec(body) = $bold(body)$
#let innerprod(A, B) = $chevron.l #A, #B chevron.r$
#let hadamard = $dot.o$

