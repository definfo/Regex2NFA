{
  description = "A Nix-flake-based Coq development environment using opam";

  inputs.nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/0.1.*.tar.gz";

  outputs =
    { self, nixpkgs }:
    let
      supportedSystems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forEachSupportedSystem =
        f:
        nixpkgs.lib.genAttrs supportedSystems (
          system:
          f {
            pkgs = import nixpkgs {
              inherit system;
              config.allowUnfree = true;
            };
          }
        );
    in
    {
      devShells = forEachSupportedSystem (
        { pkgs }:
        {
          default = pkgs.mkShell {
            packages =
              let
                coq = pkgs.coq_8_19;
                callCoqPackage = pkgs.coqPackages_8_19.callPackage;
                sets = callCoqPackage ./sets.nix { };
                fixedpoints = callCoqPackage ./fixedpoints.nix {
                  inherit sets;
                };
                monadlib = callCoqPackage ./monadlib.nix {
                  inherit sets fixedpoints;
                };
                CertiGraph = callCoqPackage ./CertiGraph.nix { };
              in
              [
                coq
                CertiGraph
                monadlib
              ];
          };
        }
      );
    };
}
