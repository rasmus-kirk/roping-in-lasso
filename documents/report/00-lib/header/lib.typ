#import "@preview/gruvy:2.1.0": gruvbox, theme-colors, colors
#import "@preview/theorion:0.4.1": *
#import "@preview/zebraw:0.6.0": *
#import "@preview/lovelace:0.3.0": *
#import cosmos.clouds: *
#import cosmos.clouds: render-fn as render-fn2

#let theme = theme-colors.light.hard;
#let remark = remark.with(fill: theme.muted.blue)
#let tip-box = tip-box.with(fill: theme.strong.green)
#let caution-box = caution-box.with(fill: theme.muted.red)
#let warning-box = warning-box.with(fill: theme.muted.yellow)
#let definition = definition.with(fill: theme.muted.aqua.lighten(85%))
#let theorem = theorem.with(fill: theme.muted.blue.lighten(80%))
#let lemma = lemma.with(fill: theme-colors.dark.soft.strong.blue.lighten(80%))
#let corollary = corollary.with(fill: theme-colors.dark.soft.muted.aqua.lighten(80%))
#let (example-counter, example-box, example, show-example) = make-frame(
  "definition",
  theorion-i18n-map.at("example"),
  inherited-levels: 2,
  render: render-fn2.with(fill: theme.bg0.lighten(30%)),
)
#let (corollary-counter, corollary-box, corollary, show-corollary) = make-frame(
  "corollary",
  "corollary",  // supplement, string or dictionary like `(en: "corollary")`, or `theorion-i18n-map.at("corollary")` for built-in i18n support
  inherited-levels: 2,  // useful when you need a new counter
  inherited-from: heading,  // heading or just another counter
  render: render-fn2.with(fill: theme-colors.dark.soft.muted.aqua.lighten(80%)),
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

#set text(
  font: "New Computer Modern"
)

#show math.equation: set text(font: "Fira Math")
#show math.equation: set text(font: "New Computer Modern Math")
#set math.mat(delim: "[")

#let pad_bitstring(length, bits) = {
  let bitstring = str(bits)
  let diff = length - bitstring.len()

  if diff > 0 {
    // Multiply the "0" string by the difference to create the padding
    bitstring = ("0" * diff) + bitstring
  }

  bitstring
}
#let b(
  l: 2,
  fill: color.rgb("#fbf1c7"),
  bits
) = box(
  fill: fill,
  inset: 2pt,
  radius: 2pt,
  baseline: 2pt,
  [#text(font: "FiraCode Nerd Font", size: 8.8pt, pad_bitstring(l, bits));]
)

#let pseudocode(title: none, args: (), content) = {
  let header = if args.len() > 0 {
    let temp = args
      .enumerate()
      .map(it => $#it.at(1)$ )
      .join(", ")

    $#smallcaps(title)\(#temp)$
  } else if title != none {
    $#smallcaps(title)$
  } else {
    none
  }

  align(center)[
    #box(
      block(
        fill: theme.bg0.lighten(30%),
        inset: 1em,
        stroke: stroke(paint: theme.fg4),
        radius: 4pt,
        pseudocode-list(
          line-numbering: "1:",
          booktabs: title != none,
          stroke: 1pt + theme.fg4.lighten(30%),
          booktabs-stroke: 2pt + theme.fg2,
          title: header,
          content
        )
      )
    )
  ]
}

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
// #let Eb = math.bb("E")
#let Nb = math.bb("N")
#let nats = math.bb("N")
#let Nat = math.bb("N")
#let Bool = math.bb("B")
#let inrand = $attach(in, br: R)$
#let vec(body) = $bold(body)$
#let innerprod(A, B) = $chevron.l #A, #B chevron.r$
#let hadamard = $dot.o$

#let Init = "Init"
#let WS = "WS"
#let RS = "RS"
#let Audit = "Audit"
#let val = "val"
#let mem = "mem"
#let row = "row"
#let col = "col"
#let nz = "nz"
#let eq = $tilde("eq")$
#let readTS = "read_ts"
#let writeTS = "write_ts"
#let auditTS = "audit_ts"
#let toBits = "toBits"
#let toInt = "toInt"
#let TODO = text(weight: "bold", size: 1.2em,  "TODO")
#let ts = $t s$

#let RAM = "RAM"
#let poly = math.op("poly")
#let negl = math.op("negl")
#let CMCommit = smallcaps("CM.Commit")
#let PC = "PC"
#let PCCheck = smallcaps("PC.Check")
#let PCSetup = smallcaps("PC.Setup")
#let PCCommit = smallcaps("PC.Commit")
#let PCOpen = smallcaps("PC.Open")
#let EvalProof = $bold(#smallcaps("EvalProof"))$
#let Commit = $bold(#smallcaps("Commit"))$
#let Instance = $bold(#smallcaps("Instance"))$
#let pp = "pp"
#let ppPC = $"pp"_"PC"$



