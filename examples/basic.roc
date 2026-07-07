app [main!] {
	pf: platform "https://github.com/lukewilliamboswell/roc-platform-template-zig/releases/download/1.0.0/AnZoxzoGPtSGQ15EQh6pBeeaHJ7aizP9MQhK81dES3Uq.tar.zst",
	path: "../package/main.roc",
}

import pf.Stdout
import path.Path

main! : List(Str) => Try({}, [Exit(I32), StdoutErr(Str), ..])
main! = |_args| {
	file_path = Path.join("src", "main.roc")
	Stdout.line!(Path.display(file_path))?
	Ok({})
}
