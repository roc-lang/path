expect Path.unix("abc") == Unix([97, 98, 99])
expect Path.unix_bytes([97, 98, 99]) == Unix([97, 98, 99])
expect Path.windows("abc") == Windows([97, 98, 99])
expect Path.windows_u16s([97, 98, 99]) == Windows([97, 98, 99])

expect Path.to_raw(Path.unix_bytes([97, 255, 98])) == UnixBytes([97, 255, 98])
expect Path.from_raw(WindowsU16s([97, 98, 99])) == Path.windows("abc")

expect Path.to_str(Path.unix("abc")) == Ok("abc")
expect Path.to_str(Path.unix_bytes([97, 255, 98])) == Err(InvalidStr(1))
expect Path.to_str(Path.windows("abc")) == Ok("abc")
expect Path.to_str(Path.windows_u16s([0xD800])) == Err(InvalidStr(0))

expect Path.to_str(Path.windows_u16s([0xD83D, 0xDC26])) == Ok(Str.from_utf8_lossy([0xF0, 0x9F, 0x90, 0xA6]))

expect Path.display(Path.unix_bytes([97, 255, 98])) == Str.from_utf8_lossy([97, 255, 98])
expect Path.display(Path.windows_u16s([0xD800, 97])) == Str.from_utf8_lossy([0xEF, 0xBF, 0xBD, 97])

expect Path.filename(Path.unix("foo/bar.txt")) == Ok(Path.unix("bar.txt"))
expect Path.filename(Path.unix("foo/bar")) == Ok(Path.unix("bar"))
expect Path.filename(Path.unix("foo/bar/")) == Err(IsDirPath)
expect Path.filename(Path.windows("foo\\bar\\")) == Err(IsDirPath)
expect Path.filename(Path.unix("foo/bar..")) == Err(EndsInDots)
expect Path.filename(Path.unix("foo")) == Ok(Path.unix("foo"))
expect Path.filename(Path.unix("")) == Ok(Path.unix(""))

expect Path.ext(Path.unix("foo/bar.txt")) == Ok(Path.unix("txt"))
expect Path.ext(Path.unix("foo/bar.")) == Ok(Path.unix(""))
expect Path.ext(Path.unix("foo/.bar.txt")) == Ok(Path.unix("txt"))
expect Path.ext(Path.unix("foo/bar")) == Ok(Path.unix(""))
expect Path.ext(Path.unix("foo/.bar")) == Ok(Path.unix(""))
expect Path.ext(Path.unix("foo/bar.baz.txt")) == Ok(Path.unix("baz.txt"))
expect Path.ext(Path.unix("foo/.bar.baz.txt")) == Ok(Path.unix("baz.txt"))
expect Path.ext(Path.unix("foo/bar/")) == Err(IsDirPath)
expect Path.ext(Path.unix("foo/bar..")) == Err(EndsInDots)
expect Path.ext(Path.unix("")) == Ok(Path.unix(""))

expect Path.join(Path.unix("foo"), "bar") == Path.unix("foo/bar")
expect Path.join(Path.windows("foo"), "bar") == Path.windows("foo\\bar")

Path :: [
	Unix(List(U8)),
	Windows(List(U16)),
].{

	## Create a Unix path from a Roc string by storing its UTF-8 bytes.
	unix : Str -> Path
	unix = |str| Unix(Str.to_utf8(str))

	## Create a Unix path from raw bytes without validating UTF-8.
	unix_bytes : List(U8) -> Path
	unix_bytes = |bytes| Unix(bytes)

	## Create a Windows path from a Roc string by storing its UTF-16 code units.
	windows : Str -> Path
	windows = |str| Windows(str_to_utf16(str))

	## Create a Windows path from raw UTF-16 code units.
	windows_u16s : List(U16) -> Path
	windows_u16s = |list| Windows(list)

	## Convert a path to a string if its raw representation is valid text.
	to_str : Path -> Try(Str, [InvalidStr(U64)])
	to_str = |path|
		match path {
			Unix(bytes) =>
				match Str.from_utf8(bytes) {
					Ok(str) => Ok(str)
					Err(BadUtf8({ index, problem: _ })) => Err(InvalidStr(index))
				}

			Windows(u16s) => utf16_to_str(u16s)
		}

	## Convert a path to a display string, replacing invalid text with U+FFFD.
	display : Path -> Str
	display = |path|
		match path {
			Unix(bytes) => Str.from_utf8_lossy(bytes)
			Windows(u16s) => Str.from_utf8_lossy(utf16_to_utf8_lossy(u16s))
		}

	## Returns everything after the last directory separator.
	filename : Path -> Try(Path, [IsDirPath, EndsInDots])
	filename = |path|
		match path {
			Unix(bytes) =>
				if ends_with_u8(bytes, '/') {
					Err(IsDirPath)
				} else if ends_with_two_u8(bytes, '.', '.') {
					Err(EndsInDots)
				} else {
					match List.find_last_index(bytes, |byte| byte == '/') {
						Ok(last_sep_index) => Ok(Unix(after_index_u8(bytes, last_sep_index)))
						Err(NotFound) => Ok(path)
					}
				}

			Windows(u16s) =>
				if ends_with_u16(u16s, '/') or ends_with_u16(u16s, '\\') {
					Err(IsDirPath)
				} else if ends_with_two_u16(u16s, '.', '.') {
					Err(EndsInDots)
				} else {
					match List.find_last_index(u16s, |u16| u16 == '/' or u16 == '\\') {
						Ok(last_sep_index) => Ok(Windows(after_index_u16(u16s, last_sep_index)))
						Err(NotFound) => Ok(path)
					}
				}
			}

	## Returns the filename extension without the leading dot.
	ext : Path -> Try(Path, [IsDirPath, EndsInDots])
	ext = |path|
		match filename(path) {
			Err(err) => Err(err)
			Ok(Unix(bytes)) => Ok(Unix(ext_units_u8(bytes)))
			Ok(Windows(u16s)) => Ok(Windows(ext_units_u16(u16s)))
		}

	## Adds a separator and a string component to the path.
	join : Path, Str -> Path
	join = |path, str|
		match path {
			Unix(bytes) => Unix(bytes.append('/').concat(Str.to_utf8(str)))
			Windows(u16s) => Windows(u16s.append('\\').concat(str_to_utf16(str)))
		}

	## Expose the raw OS-specific representation.
	to_raw : Path -> [UnixBytes(List(U8)), WindowsU16s(List(U16))]
	to_raw = |path|
		match path {
			Unix(bytes) => UnixBytes(bytes)
			Windows(u16s) => WindowsU16s(u16s)
		}

	## Build a path from the raw OS-specific representation.
	from_raw : [UnixBytes(List(U8)), WindowsU16s(List(U16))] -> Path
	from_raw = |raw|
		match raw {
			UnixBytes(bytes) => Unix(bytes)
			WindowsU16s(u16s) => Windows(u16s)
		}
}

str_to_utf16 : Str -> List(U16)
str_to_utf16 = |str| utf8_to_utf16(Str.to_utf8(str), [])

utf8_to_utf16 : List(U8), List(U16) -> List(U16)
utf8_to_utf16 = |remaining, out|
	match remaining {
		[] => out

		[byte, .. as rest] if byte < 0x80 =>
			utf8_to_utf16(rest, out.append(U8.to_u16(byte)))

		[byte1, byte2, .. as rest] if byte1 < 0xE0 => {
			top = U32.shift_left_by(U8.to_u32(U8.bitwise_and(byte1, 0x1F)), 6)
			bottom = U8.to_u32(U8.bitwise_and(byte2, 0x3F))
			code_point = U32.bitwise_or(top, bottom)

			utf8_to_utf16(rest, out.append(U32.to_u16_wrap(code_point)))
		}

		[byte1, byte2, byte3, .. as rest] if byte1 < 0xF0 => {
			top = U32.shift_left_by(U8.to_u32(U8.bitwise_and(byte1, 0x0F)), 12)
			middle = U32.shift_left_by(U8.to_u32(U8.bitwise_and(byte2, 0x3F)), 6)
			bottom = U8.to_u32(U8.bitwise_and(byte3, 0x3F))
			code_point = U32.bitwise_or(U32.bitwise_or(top, middle), bottom)

			utf8_to_utf16(rest, out.append(U32.to_u16_wrap(code_point)))
		}

		[byte1, byte2, byte3, byte4, .. as rest] => {
			top = U32.shift_left_by(U8.to_u32(U8.bitwise_and(byte1, 0x07)), 18)
			middle1 = U32.shift_left_by(U8.to_u32(U8.bitwise_and(byte2, 0x3F)), 12)
			middle2 = U32.shift_left_by(U8.to_u32(U8.bitwise_and(byte3, 0x3F)), 6)
			bottom = U8.to_u32(U8.bitwise_and(byte4, 0x3F))
			upper = U32.bitwise_or(U32.bitwise_or(top, middle1), middle2)
			code_point = U32.bitwise_or(upper, bottom)

			high = U32.to_u16_wrap(0xD800 + U32.shift_right_by(code_point - 0x10000, 10))
			low = U32.to_u16_wrap(0xDC00 + U32.bitwise_and(code_point - 0x10000, 0x3FF))

			utf8_to_utf16(rest, out.append(high).append(low))
		}

		_ => {
			crash "A Str contained invalid UTF-8. This should never happen."
		}
	}

utf16_to_str : List(U16) -> Try(Str, [InvalidStr(U64)])
utf16_to_str = |u16s|
	match utf16_to_utf8(u16s, [], 0) {
		Ok(bytes) =>
			match Str.from_utf8(bytes) {
				Ok(str) => Ok(str)
				Err(BadUtf8({ index, problem: _ })) => Err(InvalidStr(index))
			}

		Err(InvalidUtf16(index)) => Err(InvalidStr(index))
	}

utf16_to_utf8 : List(U16), List(U8), U64 -> Try(List(U8), [InvalidUtf16(U64)])
utf16_to_utf8 = |remaining, out, index|
	match remaining {
		[] => Ok(out)

		[high, low, .. as rest] if is_high_surrogate(high) and is_low_surrogate(low) => {
			high_bits = U32.shift_left_by(U16.to_u32(high) - 0xD800, 10)
			low_bits = U16.to_u32(low) - 0xDC00
			code_point = 0x10000 + high_bits + low_bits

			utf16_to_utf8(rest, append_code_point_utf8(out, code_point), index + 2)
		}

		[unit, ..] if is_surrogate(unit) => Err(InvalidUtf16(index))

		[unit, .. as rest] =>
			utf16_to_utf8(rest, append_code_point_utf8(out, U16.to_u32(unit)), index + 1)
		}

utf16_to_utf8_lossy : List(U16) -> List(U8)
utf16_to_utf8_lossy = |u16s| utf16_to_utf8_lossy_help(u16s, [])

utf16_to_utf8_lossy_help : List(U16), List(U8) -> List(U8)
utf16_to_utf8_lossy_help = |remaining, out|
	match remaining {
		[] => out

		[high, low, .. as rest] if is_high_surrogate(high) and is_low_surrogate(low) => {
			high_bits = U32.shift_left_by(U16.to_u32(high) - 0xD800, 10)
			low_bits = U16.to_u32(low) - 0xDC00
			code_point = 0x10000 + high_bits + low_bits

			utf16_to_utf8_lossy_help(rest, append_code_point_utf8(out, code_point))
		}

		[unit, .. as rest] if is_surrogate(unit) =>
			utf16_to_utf8_lossy_help(rest, append_code_point_utf8(out, 0xFFFD))

		[unit, .. as rest] =>
			utf16_to_utf8_lossy_help(rest, append_code_point_utf8(out, U16.to_u32(unit)))
		}

append_code_point_utf8 : List(U8), U32 -> List(U8)
append_code_point_utf8 = |out, code_point|
	if code_point < 0x80 {
		out.append(U32.to_u8_wrap(code_point))
	} else if code_point < 0x800 {
		out.append(U32.to_u8_wrap(0xC0 + U32.shift_right_by(code_point, 6)))
			.append(U32.to_u8_wrap(0x80 + U32.bitwise_and(code_point, 0x3F)))
	} else if code_point < 0x10000 {
		out.append(U32.to_u8_wrap(0xE0 + U32.shift_right_by(code_point, 12)))
			.append(U32.to_u8_wrap(0x80 + U32.bitwise_and(U32.shift_right_by(code_point, 6), 0x3F)))
			.append(U32.to_u8_wrap(0x80 + U32.bitwise_and(code_point, 0x3F)))
	} else {
		out.append(U32.to_u8_wrap(0xF0 + U32.shift_right_by(code_point, 18)))
			.append(U32.to_u8_wrap(0x80 + U32.bitwise_and(U32.shift_right_by(code_point, 12), 0x3F)))
			.append(U32.to_u8_wrap(0x80 + U32.bitwise_and(U32.shift_right_by(code_point, 6), 0x3F)))
			.append(U32.to_u8_wrap(0x80 + U32.bitwise_and(code_point, 0x3F)))
	}

is_high_surrogate : U16 -> Bool
is_high_surrogate = |unit| unit >= 0xD800 and unit <= 0xDBFF

is_low_surrogate : U16 -> Bool
is_low_surrogate = |unit| unit >= 0xDC00 and unit <= 0xDFFF

is_surrogate : U16 -> Bool
is_surrogate = |unit| unit >= 0xD800 and unit <= 0xDFFF

ends_with_u8 : List(U8), U8 -> Bool
ends_with_u8 = |list, suffix|
	match list {
		[.., last] => last == suffix
		[] => False
	}

ends_with_u16 : List(U16), U16 -> Bool
ends_with_u16 = |list, suffix|
	match list {
		[.., last] => last == suffix
		[] => False
	}

ends_with_two_u8 : List(U8), U8, U8 -> Bool
ends_with_two_u8 = |list, first_suffix, second_suffix|
	match list {
		[.., first, second] => first == first_suffix and second == second_suffix
		_ => False
	}

ends_with_two_u16 : List(U16), U16, U16 -> Bool
ends_with_two_u16 = |list, first_suffix, second_suffix|
	match list {
		[.., first, second] => first == first_suffix and second == second_suffix
		_ => False
	}

after_index_u8 : List(U8), U64 -> List(U8)
after_index_u8 = |list, index| {
	start = index + 1
	List.sublist(list, { start, len: List.len(list) - start })
}

after_index_u16 : List(U16), U64 -> List(U16)
after_index_u16 = |list, index| {
	start = index + 1
	List.sublist(list, { start, len: List.len(list) - start })
}

ext_units_u8 : List(U8) -> List(U8)
ext_units_u8 = |units|
	match List.find_first_index(units, |unit| unit == '.') {
		Err(NotFound) => []
		Ok(0) => {
			rest = List.drop_first(units, 1)

			match List.find_first_index(rest, |unit| unit == '.') {
				Err(NotFound) => []
				Ok(dot_index) => after_index_u8(rest, dot_index)
			}
		}
		Ok(dot_index) => after_index_u8(units, dot_index)
	}

ext_units_u16 : List(U16) -> List(U16)
ext_units_u16 = |units|
	match List.find_first_index(units, |unit| unit == '.') {
		Err(NotFound) => []
		Ok(0) => {
			rest = List.drop_first(units, 1)

			match List.find_first_index(rest, |unit| unit == '.') {
				Err(NotFound) => []
				Ok(dot_index) => after_index_u16(rest, dot_index)
			}
		}
		Ok(dot_index) => after_index_u16(units, dot_index)
	}
