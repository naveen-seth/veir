{
  description = "Overlay for VeIR's required Lean4 toolchain";

  inputs = {
    upstream = {
      url = "github:lenianiva/lean4-nix/e04ca093bca4c944f587c5e306cb5ff0c2c6ea87";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { upstream, ... }:
    let
      overlay = final: _: {
        lean = (final.callPackage "${upstream}/lib/toolchain.nix" { }).fetchBinaryLean
          (import ./v4.35.0-rc1.nix {
            lean4Nix = upstream;
          });
      };
    in
    upstream // {
      readToolchainFile = _: overlay;
      overlays = (upstream.overlays or { }) // {
        default = overlay;
      };
    };
}
