{
  description = "A template that shows all standard flake outputs";


  inputs.nixpkgs.url = "nixpkgs";


  outputs = all@{ self,  nixpkgs, ... }: 
    let  pkgs = import nixpkgs { system = "x86_64-linux";};
    in {

    # Utilized by `nix flake check`
    # checks.x86_64-linux.test = c-hello.checks.x86_64-linux.test;

    # Utilized by `nix build .`
    # defaultPackage.x86_64-linux = c-hello.defaultPackage.x86_64-linux;

    # Utilized by `nix build`
    # packages.x86_64-linux.hello = c-hello.packages.x86_64-linux.hello;

    # Utilized by `nix run .#<name>`
    # apps.x86_64-linux.hello = {
      # type = "app";
      # program = c-hello.packages.x86_64-linux.hello;
    # };

    # Utilized by `nix bundle -- .#<name>` (should be a .drv input, not program path?)
    # bundlers.x86_64-linux.example = nix-bundle.bundlers.x86_64-linux.toArx;

    # Utilized by `nix bundle -- .#<name>`
    # defaultBundler.x86_64-linux = self.bundlers.x86_64-linux.example;

    # Utilized by `nix run . -- <args?>`
    # defaultApp.x86_64-linux = self.apps.x86_64-linux.hello;

    # Utilized for nixpkgs packages, also utilized by `nix build .#<name>`
    # legacyPackages.x86_64-linux.hello = c-hello.defaultPackage.x86_64-linux;

    # Default overlay, for use in dependent flakes
    overlay = final: prev: { };

    # # Same idea as overlay but a list or attrset of them.
    overlays = { exampleOverlay = self.overlay; };


    # Utilized by `nix develop`
    devShell.x86_64-linux = pkgs.mkShell {
      packages = [
        (pkgs.agda.withPackages (p: [ p.standard-library ]))
        (pkgs.vscode-with-extensions.override {
          vscode = pkgs.vscodium;
          vscodeExtensions = with pkgs.vscode-extensions; [
            bbenoist.nix
          ] ++ 
            pkgs.vscode-utils.extensionsFromVscodeMarketplace [
              {
                name = "agda-mode";
                publisher = "banacorn";
                version = "0.3.11";
                sha256 = "sha256-jnH3oNqvkO/+Oi+8MM1RqooPFrQZMDWLSEnrVLnc5VI=";
              }
            ];
        })
      ];
    };

  };
}
