{
  description = "CTrees: a cousin of Interaction Trees, dubbed Choice Trees, with native support for non-determinism.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
    coinduction-repo = {
      url = "github:damien-pous/coinduction";
      flake = false;
    };
    relation-algebra-repo = {
      url = "github:damien-pous/relation-algebra";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter, coinduction-repo, relation-algebra-repo }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        rocq = pkgs.rocq-core;
        rocqPkgs = pkgs.rocqPackages_9_0;
        coqPkgs = pkgs.coqPackages_9_0;

        coinduction = rocqPkgs.callPackage
          ( { rocq, stdenv }:
            rocqPkgs.mkRocqDerivation {
              owner = "damien-pous";
              pname = "coinduction";
              version = "coinduction:master";
              src = coinduction-repo;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq pkgs.coq dune_3 stdlib rocq-core findlib ];
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
              version = "relation-algebra:master";
              src = relation-algebra-repo;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq pkgs.coq dune_3 stdlib rocq-core findlib ];
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
              opam-name = "coq-ctree";
              useDune = true;
              src = ./.;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq pkgs.coq dune_3 ITree coinduction relation-algebra stdlib equations ExtLib zarith findlib ];
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
