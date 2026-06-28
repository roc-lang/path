package
	[
		Path,
	]
	{}

expect Str.inspect(Path.unix("abc")) == "<opaque>"
expect Str.inspect(Path.unix_bytes([97, 98, 99])) == "<opaque>"
expect Str.inspect(Path.windows("abc")) == "<opaque>"
expect Str.inspect(Path.windows_u16s([97, 98, 99])) == "<opaque>"
