{ repoRoot, inputs, pkgs, lib, system }:

let
  modules = [{ }];

  cabalProject = pkgs.haskell-nix.cabalProject' {
    inherit modules;
    src = ../.;
    name = "plutarch-onchain-lib";
    compiler-nix-name = "ghc966";
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.CHaP;
    };
    shell.withHoogle = false;
  };

  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;
    shellArgs = repoRoot.nix.shell;
  };

in
project
