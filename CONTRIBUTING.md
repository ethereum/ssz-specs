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

1. Open a PR bumping `version` in both `pyproject.toml` and
   `packages/testing/pyproject.toml` (they must match).
2. Merge it, then run Actions → Release → Run workflow on `main`.

The workflow runs the quality gate, packages the vectors, builds the package, tags
`v<version>` with a GitHub release, and publishes `eth-ssz-specs` to PyPI. Versions
other than plain `X.Y.Z` (e.g. `0.2.0rc1`) become GitHub prereleases. `ssz-testing`
is internal and never published.

If anything fails before the release job, no tag was created: fix and re-dispatch. If
only the PyPI publish fails, re-run the failed job on the same run instead.

Before the first release: add a PyPI trusted publisher (project `eth-ssz-specs`, owner
`ethereum`, repository `ssz-specs`, workflow `release.yaml`, environment `pypi`)
and create the `pypi` environment in the GitHub repository settings.

Reproduce the artifacts locally with `just build` and `just pack-fixtures <tag>`
(macOS: `brew install gnu-tar coreutils`).

## Questions?

- Check existing [issues](https://github.com/ethereum/ssz-specs/issues)
- Open a new issue for discussion
- See [README.md](README.md) for more details on the project structure and commands
