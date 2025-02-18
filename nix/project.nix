{ repoRoot, inputs, pkgs, lib, system }:

let
  sha256map = {
    "https://github.com/Plutonomicon/plutarch-plutus"."7002ce59642daa3fff9c720cf3076844ac81ac26" = "sha256-9FR+VOUCyA0/0oHqV/m6fUXBprD9AIgrUZU0jD3f9hQ=";
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
