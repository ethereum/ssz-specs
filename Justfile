set positional-arguments := true

alias help := default

# List available recipes
default:
    @just --list

# Run all quality checks (lint, format, typecheck, spellcheck, lock)
[group('quality')]
check: lint format-check typecheck spellcheck lock-check

# Lint with ruff (no auto-fix)
[group('quality')]
lint *args:
    uv run --group lint ruff check --no-fix --show-fixes "$@"

# Format code with ruff
[group('quality')]
format *args:
    uv run --group lint ruff format "$@"

# Verify formatting with ruff (no changes)
[group('quality')]
format-check *args:
    uv run --group lint ruff format --check "$@"

# Auto-fix lint and formatting issues
[group('quality')]
fix:
    uv run --group lint ruff check --fix
    uv run --group lint ruff format

# Type check with ty
[group('quality')]
typecheck *args:
    uv run --group lint ty check "$@"

# Spell check source, tests, and packages
[group('quality')]
spellcheck *args:
    uv run --group lint codespell src tests packages README.md --skip="*.lock,*.svg,.git,__pycache__,.pytest_cache" "$@"

# Verify uv.lock is up to date
[group('quality')]
lock-check:
    #!/usr/bin/env bash
    if ! uv lock --check; then
        echo ""
        echo "uv.lock is out of date. To sync:"
        echo "  uv lock"
        echo ""
        echo "Then commit the updated uv.lock."
        exit 1
    fi

# Generate SSZ conformance test vectors under fixtures/
[group('fill')]
fill *args:
    uv run --group test fill --clean "$@"

# Run unit tests in parallel
[group('tests')]
test *args:
    uv run --group test pytest tests -n auto --maxprocesses=10 --durations=10 --dist=worksteal "$@"

# Run unit tests with coverage report (HTML + terminal)
[group('tests')]
test-cov *args:
    uv run --group test pytest --cov --cov-report=html --cov-report=term "$@"

# Run unit tests with coverage gate (fails below 100%)
[group('tests')]
test-cov-gate *args:
    uv run --group test pytest --cov --cov-report=term-missing --cov-fail-under=100 "$@"

# Build the eth-ssz-specs sdist and wheel into dist/
[group('release')]
build:
    uv build

# Fill vectors and package them as a versioned, deterministic release tarball
# (requires GNU tar and sha256sum; on macOS: brew install gnu-tar coreutils)
[group('release')]
pack-fixtures tag: fill
    #!/usr/bin/env bash
    set -euo pipefail
    TAR=tar
    SHA256=sha256sum
    if [ "$(uname)" = "Darwin" ]; then
        command -v gtar >/dev/null || { echo "GNU tar required: brew install gnu-tar" >&2; exit 1; }
        TAR=gtar
        command -v sha256sum >/dev/null || SHA256="shasum -a 256"
    fi
    "$TAR" --sort=name --owner=0 --group=0 --numeric-owner \
        --mtime='@0' --format=gnu \
        --use-compress-program='gzip --no-name' \
        --create --file="ssz-test-vectors-{{tag}}.tar.gz" fixtures
    $SHA256 "ssz-test-vectors-{{tag}}.tar.gz" > "ssz-test-vectors-{{tag}}.tar.gz.sha256"

# Print the command to install shell completions for just recipes
[group('housekeeping')]
shell-completions:
    #!/usr/bin/env bash
    case "$(basename "$SHELL")" in
        bash)
            echo "Run the following commands to install just completions for bash:"
            echo ""
            echo "  mkdir -p ~/.local/share/bash-completion/completions"
            echo "  just --completions bash > ~/.local/share/bash-completion/completions/just"
            ;;
        zsh)
            echo "Run the following commands to install just completions for zsh:"
            echo ""
            echo "  mkdir -p ~/.zsh/completions"
            echo "  just --completions zsh > ~/.zsh/completions/_just"
            echo ""
            echo "Then add to your .zshrc:"
            echo ""
            echo "  fpath=(~/.zsh/completions \$fpath)"
            echo "  autoload -U compinit"
            echo "  compinit"
            ;;
        fish)
            echo "Run the following commands to install just completions for fish:"
            echo ""
            echo "  mkdir -p ~/.config/fish/completions"
            echo "  just --completions fish > ~/.config/fish/completions/just.fish"
            ;;
        *)
            echo "See the link below for instructions for your shell."
            ;;
    esac
    echo ""
    echo "For more details, see https://just.systems/man/en/shell-completion-scripts.html"
