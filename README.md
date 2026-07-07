# Path

Work in progress package for representing operating system paths in Roc.

Operating system paths are not always valid UTF-8. This package supports
OS-specific raw representations and UTF-8 text paths: Unix paths store bytes,
Windows paths store UTF-16 code units, and quoted literals produce UTF-8 paths.
`Path.to_raw` returns `UnixBytes`, `WindowsU16s`, or `Utf8`. Use `Path.display`
only for human-facing output; use `Path.to_raw` when passing paths across a
platform boundary.

## Quoted Literals

`Path` defines `from_quote`, so quoted literals can dispatch to `Path` when the
target type is known.

```roc
import path.Path

config : Path.Path
config = "config.txt"

main_file = Path.join("src", "main.roc")
```

Quoted literals are stored as `Path.utf8` values. Platforms can convert the
`Utf8` raw case to the host-native representation at the boundary.

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
