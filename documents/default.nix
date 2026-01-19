{
  self,
  system,
  pkgs,
}:
  let
    typstPkgs = p: with p; [
      gruvy_2_1_0
      zebraw_0_6_0
      fletcher_0_5_8
      xarrow_0_3_1
      theorion_0_4_1
      oxifmt_0_2_1 # Nixpkgs support for typst is sort of janky
      diatypst_0_8_0
      polylux_0_4_0
      metropolis-polylux_0_1_0
    ];
    report = pkgs.buildTypstDocument {
      name = "report";
      src = ./report;
      typstEnv = typstPkgs;
      creationTimestamp = self.lastModified;
      fonts = [ pkgs.roboto ];
    };
    contract = pkgs.buildTypstDocument {
      name = "contract";
      src = ./contract;
      creationTimestamp = self.lastModified;
      fonts = [ pkgs.roboto ];
    };
    slidesGkr = pkgs.buildTypstDocument {
      name = "slides-gkr";
      src = ./slides-gkr;
      typstEnv = typstPkgs;
      creationTimestamp = self.lastModified;
      fonts = [ pkgs.roboto ];
    };
in {
  packages.report= report; 
  packages.contract = contract; 
  packages.slidesGkr= slidesGkr; 

  devShells.default = pkgs.mkShellNoCC {
    inputsFrom = [ report ];
    packages = [
      pkgs.tinymist
      pkgs.typstyle
      pkgs.harper
    ];
  };
}
