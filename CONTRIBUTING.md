# Contributing to SSZ Specs

## Quick Start

1. Fork and clone the repository
2. Install dependencies: `uv sync`
3. Make your changes
4. Install `just`: `uv tool install just-bin`
5. Run checks: `just check`
6. Run tests: `just test`
7. Submit a pull request

## Pull Request Guidelines

1. **Create a feature branch**: `git checkout -b feat/your-feature-name`
2. **Write clear commit messages** that explain what and why
3. **Add tests** for any new functionality
4. **Update documentation** as needed
5. **Ensure all checks pass** before submitting

## Code Style

- **Type hints**: Required for all functions and methods
- **Docstrings**: Use Google style for public APIs
- **Line length**: 100 characters (enforced by ruff)
- **Formatting**: Run `just fix` to auto-format

## Testing

- Write tests that mirror the source structure
- Use `pytest.mark.parametrize` for multiple test cases
- Mark slow tests with `@pytest.mark.slow`

## Cutting a Release

Releases are cut from `main` by maintainers, via the `Release` GitHub Actions workflow
(`.github/workflows/release.yaml`):

1. **Bump the version** in a PR: update `version` in both `pyproject.toml` and
   `packages/testing/pyproject.toml` (they must match; the workflow fails on skew)
2. **Merge the PR** and wait for green CI on `main`
3. **Dispatch the workflow**: Actions → Release → Run workflow, on `main` (no inputs;
   the version is read from `pyproject.toml`)
4. **The workflow then runs automatically**: quality gate (`just check` plus the
   coverage gate), generate and package the conformance vectors as a deterministic
   `ssz-test-vectors-vX.Y.Z.tar.gz` with a `.sha256` checksum, build the sdist and
   wheel, create the `vX.Y.Z` git tag and GitHub release with the tarball attached in
   one atomic step, and publish `eth-ssz-specs` to PyPI via trusted publishing
5. **Approve the PyPI publish** if the `pypi` GitHub environment has required reviewers
   configured (the tag and GitHub release already exist at this point)
6. **On failure**: if anything fails before the release job, no tag was created — fix
   the problem on `main` and re-dispatch. The workflow also refuses to reuse an
   existing tag, so a re-dispatch after a successful tag requires a version bump. If
   only the PyPI publish fails after the tag and GitHub release exist, do not
   re-dispatch — use "Re-run failed jobs" on the same workflow run instead

**Version scheme**: plain `X.Y.Z` for final releases. Anything else (e.g. `0.2.0rc1`)
is marked as a prerelease on GitHub. The tag is always `v<version>`.

**What gets published**: only the workspace root package `eth-ssz-specs`. The
`ssz-testing` package under `packages/testing/` is internal tooling and is deliberately
never published to PyPI.

**One-time setup** (before the first release): on PyPI, add a pending trusted publisher
for project `eth-ssz-specs` with owner `leanEthereum`, repository `ssz-specs`, workflow
`release.yaml`, and environment `pypi`; on GitHub, create the `pypi` environment
(Settings → Environments) and optionally add required reviewers. Publishing uses OIDC,
so no tokens or secrets are stored.

**Local debugging**: the release artifacts can be reproduced with two recipes:

```bash
just build                 # Build the sdist and wheel into dist/
just pack-fixtures v0.1.0  # Fill vectors and package the release tarball + checksum
```

`pack-fixtures` needs GNU tar and `sha256sum` for byte-identical tarballs; on macOS,
install them with `brew install gnu-tar coreutils`.

## Questions?

- Check existing [issues](https://github.com/ethereum/ssz-specs/issues)
- Open a new issue for discussion
- See [README.md](README.md) for more details on the project structure and commands
