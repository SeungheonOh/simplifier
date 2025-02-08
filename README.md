# Plutarch Template

This repository provides a basic configuration to bootstrap a Cardano on-chain project using [Plutarch](https://www.github.com/Plutonomicon/plutarch-plutus). For more information about the Plutarch, refer to the [documentation](https://plutonomicon.github.io/plutarch-plutus).

## Getting Started

The template is based on the Nix build system with flakes. To build and develop using this template, you are recommended to use Nix, either by using NixOS or the Nix package manager. For installation and configuration instructions, refer to the [Nix website](https://nixos.org/). Ensure the Nix flake feature is enabled.

With Nix installed and configured, you can enter the development shell by running the `nix develop` command in this repository. Nix will automatically fetch all dependencies required to build the Plutarch project. The initial execution may take some time due to the build process, but subsequent runs will utilize cached packages, significantly reducing build time.

Once inside the development shell, Haskell development utilities such as `ghci`, `cabal`, `hoogle`, and `fourmolu` will be available. The `ghci` and `cabal` tools in the development shell are preconfigured with the necessary dependencies for Plutarch projects. Additionally, this repository provides `pre-commit-hooks` for formatting, linting, and typo-checking the codebase. These hooks can be disabled or customized in `nix/pre-commit.nix`.

## Hackage Repository

This project extensively uses Hackage to import external dependencies such as `plutus-core` and `plutarch`. While this simplifies dependency management, the interaction between haskell-nix and Hackage repositories can sometimes be confusing. Therefore, careful attention is required when modifying them.

### Dependency Management in haskell-nix

When using the development shell, Cabal does not pull dependencies directly from the Hackage repositories listed in `cabal.project` if those repositories are already specified in the haskell-nix configuration (specifically in `inputMap`). Instead, haskell-nix fetches and builds the required packages when building development shell, injecting them into Cabal when the development shell is launched.

If you need to update a Hackage repository included in the haskell-nix configuration, do not run `cabal update`. Instead, run `nix flake update <package_set_name>` and rebuild the development shell. Once Hackage repository is updated and `index-state` correctly configured on both `flake.nix` and `cabal.project`, new versions of packages will be made available for Cabal. For Hackage repositories not included in haskell-nix, dependencies behave as they normally do with Cabal.

### Versioning Constraints

When updating a Hackage repository, ensure versioning requirements are not left un-constrained. Hackage repositories is a set of packages with multiple versions of each package. Updating a Hackage repository merely makes new versions available for Cabal to inspect and resolve dependencies. If your project's Cabal file includes specific version constraints (e.g., `plutus-core == 1.36.0.0`), updating the Hackage repository will not cause issues regarding conflicts in package versioning.

> **Note**: An exception applies to allow rolling version of Plutarch, discussed in the later section.

### TL;DR: Steps to Update a Package

When updating the version of a package, the following steps are usually required:

1. Run `nix flake update`.
2. Update the `index-state` to the correct date that is after introduction of the new version of the package (**in both `flake.nix` and `cabal.project`**).
3. Adjust version constraints in the Cabal file if necessary to target new version.
4. Rebuild the Nix shell.

### "Rolling Version" for Plutarch

For developers who want to experiment with bleeding-edge features, the [Plutarch Hackage repository](https://plutonomicon.github.io/plutarch-plutus/) provides Plutarch packages with a version number of `0`. These packages are automatically updated to the latest commit on the `staging` branch of the Plutarch repository by CI.

Unlike other packages, running `nix flake update` and rebuilding will fetch the latest Plutarch built with source on the `staging` branch. When using `plutarch == 0`, proceed with caution. **This is recommended only for testing new features, not for production scripts.**

By default, this repository will have `plutarch` set to version `0`, but please make sure to acknowledge this default and update to version that suites the requirement the best.
