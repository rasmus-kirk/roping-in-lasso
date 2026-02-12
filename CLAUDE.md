# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working
with code in this repository.

## Project Overview

"Roping in Lasso" is an educational project documenting the Lasso/Jolt
zero-knowledge proof systems. It consists of a comprehensive technical report
written in Typst. The repository builds a static website hosting the report,
contract, and slides as PDFs.

## Build System

All builds use **Nix Flakes**. There is no Makefile, npm, or standalone cargo build — everything goes through Nix.

### Build Commands (from repo root `/data/personal/rust/lasso/`)

```bash
nix build                # Default: builds the full website with all PDFs
nix build .#report       # Build just the technical report PDF
nix build .#slidesGkr    # Build just the GKR slides PDF
```

### Development Shells

```bash
nix develop .#report     # Typst dev shell (tinymist, typstyle, harper)
```

### Nix Formatting

```bash
nix fmt      # Formats .nix files using Alejandra
```

## Repository Structure

```
documents/                 # Typst documents
├── report/                # Main technical report
│   ├── main.typ           # Entry point — includes all chapters
│   ├── 00-lib/            # Typst template, custom functions, styling
│   ├── 01-introduction/
│   ├── 02-prerequisites/
│   ├── 03-gkr/
│   ├── 04-specialized-gkr/
│   ├── 05-offline-memory-checking/
│   └── refs.bib           # Bibliography
├── slides-gkr/            # GKR presentation (Polylux/Metropolis)
├── contract/              # Project contract document
└── default.nix            # Typst build/devshell config

flake.nix                  # Top-level Nix orchestrator
```

## Architecture Notes

- **Typst report** uses the `ilm` template from `00-lib/` with Theorion for theorem environments. Chapters are numbered directories with a `00-*.typ` entry file each.
- **Website** is built via `website-builder` (a Nix flake input) that combines the README into an index page and hosts the generated PDFs. Deployed to GitHub Pages via CI on push to `main` or `release*` branches.
- **Typst packages** used: gruvy, zebraw, fletcher, xarrow, theorion, oxifmt, diatypst, algo, polylux, metropolis-polylux — all pinned in `documents/default.nix`.
