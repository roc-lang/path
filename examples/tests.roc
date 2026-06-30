app [main!] {
	pf: platform "https://github.com/lukewilliamboswell/roc-platform-template-zig/releases/download/0.9/8GdFEvQYS3TeAZxKvTzCLVdQiomweGtXcdZkXNDEeABq.tar.zst",
	path: "https://github.com/roc-lang/path/releases/download/0.1/8p8iryUUorAFTUDeqYcwc9bFYSwpbVqhYpuHvRAS5Cq4.tar.zst",
}

import pf.Stdout
import path.Path

main! = |_args| {
	Stdout.line!("Run `roc test examples/tests.roc` to exercise the path package examples.")
	Ok({})
}

expect Path.to_raw(Path.unix("src/main.roc")) == UnixBytes(Str.to_utf8("src/main.roc"))

expect Path.to_raw(Path.unix_bytes([97, 255, 98])) == UnixBytes([97, 255, 98])

expect Path.to_str(Path.unix_bytes([97, 255, 98])) == Err(InvalidStr(1))

expect Path.display(Path.unix_bytes([97, 255, 98])) == Str.from_utf8_lossy([97, 255, 98])

expect Path.to_raw(Path.windows("src\\main.roc")) == WindowsU16s([115, 114, 99, 92, 109, 97, 105, 110, 46, 114, 111, 99])

expect Path.filename(Path.unix("src/main.roc")) == Ok(Path.unix("main.roc"))

expect Path.ext(Path.unix("src/main.roc")) == Ok(Path.unix("roc"))
