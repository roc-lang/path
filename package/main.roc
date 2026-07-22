package
	[
		Path,
	]
	{}

expect Str.inspect(Path.unix("abc")) == "Path.unix(\"abc\")"
expect Str.inspect(Path.unix_bytes([97, 98, 99])) == "Path.unix(\"abc\")"
expect Str.inspect(Path.windows("abc")) == "Path.windows(\"abc\")"
expect Str.inspect(Path.windows_u16s([97, 98, 99])) == "Path.windows(\"abc\")"
expect Str.inspect(Path.utf8("abc")) == "Path.utf8(\"abc\")"
