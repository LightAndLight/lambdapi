{ mkDerivation, base, bound, deriving-compat, parsers
, recursion-schemes, stdenv, transformers, trifecta
}:
mkDerivation {
  pname = "lambdapi";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base bound deriving-compat parsers recursion-schemes transformers
    trifecta
  ];
  license = stdenv.lib.licenses.bsd3;
}
