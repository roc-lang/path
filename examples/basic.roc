app [main!] {
	pf: platform "https://github.com/lukewilliamboswell/roc-platform-template-zig/releases/download/0.9/8GdFEvQYS3TeAZxKvTzCLVdQiomweGtXcdZkXNDEeABq.tar.zst",
	path: "https://github.com/roc-lang/path/releases/download/0.1/8p8iryUUorAFTUDeqYcwc9bFYSwpbVqhYpuHvRAS5Cq4.tar.zst",
}

import pf.Stdout
import path.Path

main! = |_args| {
	file_path = Path.join(Path.unix("src"), "main.roc")
	Stdout.line!(Path.display(file_path))
	Ok({})
}
