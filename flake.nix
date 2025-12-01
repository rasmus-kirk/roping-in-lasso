{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/master";
    # Provides helpers for Rust toolchains
    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";
    # The website builder
    website-builder.url = "github:rasmus-kirk/website-builder";
    website-builder.inputs.nixpkgs.follows = "nixpkgs";
    # Better Nix/Typst integration
    press.url = "github:RossSmyth/press";
    press.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, website-builder, press, ...}:
    let
      documentsF = pkgs: pkgs.callPackage ./documents { self = self; };
      rustF = pkgs: pkgs.callPackage ./code { self = self; };
      websiteF = pkgs: website-builder.lib {
        pkgs = pkgs;
        src = ./.;
        timestamp = self.lastModified;
        headerTitle = "From Bulletproofs to Lasso";
        includedDirs = [
          (pkgs.runCommand "report" {} ''
            mkdir -p $out
            cp -a ${(documentsF pkgs).packages.report} $out/report.pdf
          '')
          (pkgs.runCommand "contract" {} ''
            mkdir -p $out
            cp -a ${(documentsF pkgs).packages.contract} $out/contract.pdf
          '')
        ];
        standalonePages = [{
          title = "From Bulletproofs to Lasso";
          inputFile = ./README.md;
          outputFile = "index.html";
        }];
        navbar = [
          {
            title = "Home";
            location = "/";
          }
          {
            title = "Report";
            location = "/report/report.pdf";
          }
          {
            title = "Report";
            location = "/contract/contract.pdf";
          }
          {
            title = "Github";
            location = "https://github.com/rasmus-kirk/from-bulletproofs-to-lasso";
          }
        ];
      };
      allSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs allSystems (system: f {
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import press) ];
        };
      });
    in
    {
      formatter = forAllSystems ({pkgs}: pkgs.alejandra);

      devShells = forAllSystems ({ pkgs } : {
        rust = (rustF pkgs).devShells.default;
        report = (documentsF pkgs).devShells.default;
      });

      packages = forAllSystems ({ pkgs }: rec {
        website = (websiteF pkgs).package;
        rust = (rustF pkgs).packages;
        report = (documentsF pkgs).packages.report;
        default = website;
      });
    };
}
