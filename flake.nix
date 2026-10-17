{
  description = "CTrees: a cousin of Interaction Trees, dubbed Choice Trees, with native support for non-determinism.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
    coinduction-repo = {
      url = "github:damien-pous/coinduction/v1.22";
      flake = false;
    };
    relation-algebra-repo = {
      url = "github:damien-pous/relation-algebra/v1.9.1";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter, coinduction-repo, relation-algebra-repo }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        rocqPkgs = pkgs.rocqPackages_9_2;
        coqPkgs = pkgs.coqPackages_9_2;
        rocq = rocqPkgs.rocq-core;

        coinduction = rocqPkgs.callPackage
          ( { rocq, stdenv }:
            rocqPkgs.mkRocqDerivation {
              owner = "damien-pous";
              pname = "coinduction";
              version = "1.22";
              src = coinduction-repo;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq coqPkgs.coq dune_3 stdlib rocq-core findlib ];
              propagatedBuildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ rocq ];
            }) { inherit rocq; } ;

        relation-algebra = rocqPkgs.callPackage
          ( { rocq, stdenv }:
            rocqPkgs.mkRocqDerivation {
              owner = "damien-pous";
              pname = "relation-algebra";
              version = "1.9.1";
              src = relation-algebra-repo;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq coqPkgs.coq dune_3 stdlib rocq-core findlib ];
              propagatedBuildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ rocq ];
            }) { inherit rocq; } ;
      in rec {
        packages = {
          default =rocqPkgs.callPackage
          ( { rocq, stdenv }:
            rocqPkgs.mkRocqDerivation {
              owner = "vellvm";
              pname = "ctrees";
              version = "ctrees:dev";
              opam-name = "rocq-ctree";
              useDune = true;
              src = ./.;
              preBuild = "dune build rocq-ctree.opam && cp _build/default/rocq-ctree.opam .";

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq coqPkgs.coq dune_3 ITree coinduction relation-algebra stdlib equations ExtLib zarith findlib ];
              propagatedBuildInputs = [ rocq ];

            }) { inherit rocq; };
        };

        defaultPackage = packages.default;

        app.default = flake-utils.lib.mkApp { drv = packages.default; };

        devShells = {
          default = pkgs.mkShell {
            inputsFrom = [ packages.default];
            buildInputs = [ ];
            shellHook = ''
              unset COQPATH
            '';
          };
        };

        devShell = devShells.default;
      });
}
