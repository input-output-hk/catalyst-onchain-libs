{ repoRoot, inputs, pkgs, lib, system }:

let
  sha256map = {
    "https://github.com/Plutonomicon/plutarch-plutus"."8cc0a4ca3ed494a79fe019c72173b369cd26cb84" = "sha256-zQ0qv9e3Gy6Myn8wx+geJtCL5L2qJlpruSbWmrgyLOE=";
  };

  modules = [{ }];

  cabalProject = pkgs.haskell-nix.cabalProject' {
    inherit modules sha256map;
    src = ../.;
    name = "plutarch-onchain-lib";
    compiler-nix-name = "ghc966";
    # index-state = "2024-10-16T00:00:00Z";
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
