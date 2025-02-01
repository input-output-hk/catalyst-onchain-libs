{ repoRoot, inputs, pkgs, lib, system }:

let
  sha256map = {
    "https://github.com/Plutonomicon/plutarch-plutus"."fd7d1c1fc173542f952f19272554027183659dd6" = "sha256-lU2JF9KYvzEPfVLHdLkrM1hTTuc9NYi2hQPFnLDm2d8=";
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
