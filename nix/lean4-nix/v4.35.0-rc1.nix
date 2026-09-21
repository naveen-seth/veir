# Lean 4.35.0-rc1 binary manifest.
{ lean4Nix }:
let
  fallback = import "${lean4Nix}/manifests/v4.33.1.nix";
  tag = "v4.35.0-rc1";
  version = builtins.substring 1 (-1) tag;
  releaseUrl = "https://github.com/leanprover/lean4/releases/download/${tag}/lean-${version}";
in
{
  inherit (fallback) bootstrap buildLeanPackage overlay;

  inherit tag;
  rev = "86c6347c75e39ec18c40e25ed2143b71a6e04a0a";
  toolchain = {
    x86_64-linux = {
      url = "${releaseUrl}-linux.tar.zst";
      hash = "sha256-opl2NAHDubjhm8yib4RDtAriSWLDw93uc7XHIZSHf2U=";
    };
    aarch64-linux = {
      url = "${releaseUrl}-linux_aarch64.tar.zst";
      hash = "sha256-JJGk7Pw/u45i8ioDRI/pDjFcpCAtv3tYobqHUVjYHeg=";
    };
    x86_64-darwin = {
      url = "${releaseUrl}-darwin.tar.zst";
      hash = "sha256-Vq4a5Fxj0O/DSkTbKhIYzC+w59UA4SUdpnXwBxO/KLI=";
    };
    aarch64-darwin = {
      url = "${releaseUrl}-darwin_aarch64.tar.zst";
      hash = "sha256-ZMHZDYcmiuMUM+quxovW1u5mF/SrCHCt7aXebHm+mVs=";
    };
  };
}
