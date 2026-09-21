{
  description = "Verified Intermediate Representation";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    lean4-nix = {
      url = "path:./nix/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, lean4-nix, ... }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
      pkgsFor = system:
        import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
        };
      llvmPackages = pkgs: pkgs.llvmPackages_23;
      executableTargets = [
        "veir-opt"
        "veir-interpret"
        "veir2mir"
        "run-benchmarks"
      ];

      developmentPackages = pkgs: with pkgs; [
        bash
        (llvmPackages pkgs).clang
        gmp
        gnumake
        (llvmPackages pkgs).llvm
        lean.lean-all
        ((llvmPackages pkgs).mlir.overrideAttrs (oldAttrs: {
          # Nixpkgs does not enable MLIR's test dialect. VeIR's PDL tests
          # use that dialect when checking compatibility with mlir-opt.
          cmakeFlags = oldAttrs.cmakeFlags ++ [
            (lib.cmakeBool "MLIR_INCLUDE_TESTS" true)
          ];
        }))
        pkg-config
        uv
      ];

      veirPackages = pkgs:
        let
          lake2nix = pkgs.callPackage lean4-nix.lake { };
          ctreesSource = self + "/lean-ctrees";
          exArraySource = self + "/ExArray";
          exArrayBuildInputs = [
            pkgs.bash
            (llvmPackages pkgs).clang
            pkgs.gmp
            pkgs.pkg-config
          ];
          coinductive = (lake2nix.buildDeps {
            src = ctreesSource;
          }).Coinductive;
          exArray = lake2nix.mkPackage {
            name = "ExArray";
            src = exArraySource;
            lakeDeps = { };
            buildLibrary = true;
            staticLibDeps = exArrayBuildInputs;
            preConfigure = ''
              rm lean-toolchain
              cp "${self}/lean-toolchain" lean-toolchain
              patchShebangs compiler
            '';
          };
          ctrees = lake2nix.mkPackage {
            name = "CTree";
            src = ctreesSource;
            lakeDeps = {
              Coinductive = coinductive;
            };
            buildLibrary = true;
          };
          veirDeps = {
            ExArray = exArray;
            "«lean-ctrees»" = ctrees;
            Coinductive = coinductive;
          };
          veirLibrary = lake2nix.mkPackage {
            name = "Veir";
            src = self;
            lakeDeps = veirDeps;
            buildLibrary = true;
          };
          commonExecutableArgs = {
            src = self;
            lakeDeps = veirDeps;
            lakeArtifacts = veirLibrary;
            installArtifacts = false;
          };
        in
        pkgs.lib.genAttrs executableTargets (
          target:
          lake2nix.mkPackage (commonExecutableArgs // {
            name = target;
            meta.mainProgram = target;
          })
        );

    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          default = pkgs.mkShell {
            packages = developmentPackages pkgs;

            # ExArray uses Clang LTO and therefore needs its compiler wrapper
            # together with LLVM's archiver.
            LEAN_AR = "${(llvmPackages pkgs).llvm}/bin/llvm-ar";
            LEAN_CC = "${self}/ExArray/compiler";
          };
        });

      packages = forAllSystems (system: veirPackages (pkgsFor system));
    };
}
