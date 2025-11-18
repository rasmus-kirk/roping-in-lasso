{
  self,
  system,
  pkgs,
}:
  let report = pkgs.buildTypstDocument {
    name = "report";
    src = ./.;
    typstEnv = p: with p; [
      gruvy_2_1_0
      zebraw_0_5_5
      fletcher_0_5_8
      xarrow_0_3_1
      theorion_0_4_0
      oxifmt_0_2_1 # Nixpkgs support for typst is sort of janky
    ];
    creationTimestamp = self.lastModified;
    fonts = [
      pkgs.roboto
    ];
  };
  # harper = pkgs.rustPlatform.buildRustPackage rec {
  #   pname = "harper-test-program";
  #   version = "0.34.1";

  #   src = pkgs.fetchFromGitHub {
  #     owner = "Automattic";
  #     repo = "harper";
  #     rev = "v${version}";
  #     hash = "sha256-fBAPJhB+x8cIFs6rp1nDvrtVkAKx2wuFCO7FwHOwLRM=";
  #   };

  #   cargoHash = "sha256-XVC2xgUwazYXVp5sx6kA+aopd9m38XlbgsLnb0D92kg=";

  #   meta = {
  #     mainProgram = "harper-cli";
  #   };
  # };
in {
  packages.default = report; 

  devShells.default = pkgs.mkShellNoCC {
    inputsFrom = [ report ];
    packages = [
      pkgs.tinymist
      pkgs.typstyle
      pkgs.harper
      # harper
    ];
  };
}
