app [main!] {
	path: "../package/main.roc",
}

import path.Path

main! = |_| {
	file_path = Path.join("src", "main.roc")
	echo!("${Path.display(file_path)}\n")
	Ok({})
}
