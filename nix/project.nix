{ repoRoot, inputs, pkgs, lib, system }:

let
  sha256map = {
    "https://github.com/Plutonomicon/plutarch-plutus"."0a548108f9d83e4830a1a3ae1e58e61856c1bc42" = "sha256-n+L9BM4nb0KtmBme5fSBzjB1s0AYMwB383Kz6UbEXEY=";
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
