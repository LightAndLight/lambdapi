{ mkDerivation, base, bound, containers, deriving-compat, lens, mtl
, parsers, stdenv, transformers, trifecta
}:
mkDerivation {
  pname = "lambdapi";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base bound containers deriving-compat lens mtl parsers transformers
    trifecta
  ];
  license = stdenv.lib.licenses.bsd3;
}
