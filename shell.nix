{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    pkgs.idris2

    # keep this line if you use bash
    pkgs.bashInteractive
  ];
}
