import Lake
open Lake DSL System

package ssz where
  -- An unfinished proof is a warning by default, which would let one ship silently.
  -- An undeclared identifier becomes a silent new variable by default.
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- No third-party dependencies: proofs use Lean's standard logical axioms.

/-- The executable specification, which is what an implementer reads. -/
@[default_target]
lean_lib Ssz

/-- The machine-checked properties of it, which nothing else depends on. -/
@[default_target]
lean_lib SszProofs where
  roots := #[`Ssz.Proofs]

/-- SSZ read straight from encodings, on native kernels printed from Lean programs. -/
@[default_target]
lean_lib SszNative

/-- The proofs that it computes the specification, which nothing else depends on. -/
@[default_target]
lean_lib SszNativeProofs where
  roots := #[`SszNative.Proofs]

lean_lib Conformance

lean_lib Sha256Tests where
  roots := #[`Tests.Hash.Sha256]

lean_lib NativeTests where
  roots := #[`Tests.Native]

@[default_target]
lean_exe conformance where
  root := `Main

@[default_target]
lean_exe regressions where
  root := `Tests

/-- The kernels the Lean programs in `SszNative` print, assembled with the toolchain's compiler. -/
target nativeKernels pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "kernels_x86.S")
  buildLeanO (pkg.buildDir / "native" / "kernels_x86.o") src #["-fPIC"]

/-- The bindings between Lean values and the kernels. -/
target nativeBindings pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "bindings.c")
  buildLeanO (pkg.buildDir / "native" / "bindings.o") src #["-fPIC", "-O2"]

/-- The kernels and their bindings, linked into every executable. -/
extern_lib sszKernels pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "sszKernels")
    #[← nativeKernels.fetch, ← nativeBindings.fetch]

/-- Times the native implementation on beacon-chain workloads: `lake exe bench`. -/
lean_exe bench where
  root := `Bench
