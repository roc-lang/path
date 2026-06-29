# Path

Work in progress package for representing operating system paths in Roc.

Operating system paths are not always valid UTF-8. This package keeps paths in an
OS-specific raw representation: Unix paths store bytes, and Windows paths store
UTF-16 code units. `Path.to_raw` returns either `UnixBytes` or `WindowsU16s`.
Use `Path.display` only for human-facing output; use `Path.to_raw` when passing
paths across a platform boundary.

## Examples

Run an example with:

```bash
roc examples/basic.roc
```

Run the example test module with:

```bash
roc test examples/tests.roc
```

## Bundling

Create a package bundle with:

```bash
scripts/bundle.sh
```

This writes a `.tar.zst` package archive to `dist/`.

## CI Checks

Run the same checks used by CI with:

```bash
ci/all_tests.sh
```

The checks format the package and examples, check and test the package, generate
docs, bundle the package, serve that bundle from localhost, and then check, test,
run, build, and execute every example against the bundled package URL.
