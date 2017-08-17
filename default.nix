{ pkgs ? import <nixpkgs> {}, compiler ? "ghc802" }:
let
  haskellPackages =
    pkgs.haskell.packages.${compiler};
in haskellPackages.callPackage
  ./lambdapi.nix
  {
    lens = haskellPackages.lens_4_15_3;
    containers = haskellPackages.containers_0_5_10_2;
    trifecta = haskellPackages.trifecta_1_7;
  }
