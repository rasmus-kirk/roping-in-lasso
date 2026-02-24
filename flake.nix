{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/master";
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
      websiteF = pkgs: website-builder.lib {
        pkgs = pkgs;
        src = ./.;
        timestamp = self.lastModified;
        headerTitle = "Roping in Lasso";
        includedDirs = [
          (pkgs.runCommand "report" {} ''
            mkdir -p $out
            cp -a ${(documentsF pkgs).packages.report} $out/report.pdf
          '')
          (pkgs.runCommand "contract" {} ''
            mkdir -p $out
            cp -a ${(documentsF pkgs).packages.contract} $out/contract.pdf
          '')
          (pkgs.runCommand "slides" {} ''
            mkdir -p $out
            cp -a ${(documentsF pkgs).packages.slidesGkr} $out/slides-gkr.pdf
          '')
        ];
        standalonePages = let
          cutLines = n: file: pkgs.runCommand "trimmed-${builtins.baseNameOf file}" {} ''
            # tail -n +K starts output at line K
            # To skip n lines, we start at n + 1
            ${pkgs.coreutils}/bin/tail -n +${toString (n + 1)} "${file}" > $out
          '';
        in [{
          pageTitle = "Roping in Lasso";
          inputFile = cutLines 2 ./README.md;
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
            title = "Contract";
            location = "/contract/contract.pdf";
          }
          {
            title = "GKR Slides";
            location = "/slides/slides-gkr.pdf";
          }
          {
            title = "Github";
            location = "https://github.com/rasmus-kirk/roping-in-lasso";
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
        report = (documentsF pkgs).devShells.default;
      });

      packages = forAllSystems ({ pkgs }: rec {
        website = (websiteF pkgs).package;
        loop = (websiteF pkgs).loop;
        report = (documentsF pkgs).packages.report;
        slidesGkr = (documentsF pkgs).packages.slidesGkr;
        default = website;
      });
    };
}
