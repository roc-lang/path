module [
    Path,
    unix,
    unixBytes,
    windows,
    windowsU16s,
    ext,
    extStr,
    filename,
    filenameStr,
    join,
    toStr,
    toStrWindows,
    toStrUnix,
    concat,
    normalize,
    display,
    displayUnix,
    displayWindows,
    toRaw,
    fromRaw,
]

Path := [
    Unix (List U8),
    Windows (List U16),
]
    implements [Eq]

unix : Str -> Path
unix = \str -> @Path (Unix (Str.toUtf8 str))

unixBytes : List U8 -> Path
unixBytes = \bytes -> @Path (Unix bytes)

windows : Str -> Path
windows = \str -> @Path (Windows (strToUtf16 str))

windowsU16s : List U16 -> Path
windowsU16s = \list -> @Path (Windows list)

# TODO these functions need to be available.
# Could depend on roc/unicode, but they're so simple it's probably nicer for end users to inline them.
strToUtf16 : Str -> List U16
strToUtf16 = \str ->
    utf8 = Str.toUtf8 str
    len = List.len utf8
    crashInvalid = \numBytes ->
        crash "A Str contained an invalid $(Num.toStr numBytes)-byte UTF-8 sequence. This should never happen!"

    List.walkWithIndex utf8 (List.withCapacity len) \state, b, index ->
        ## 1-byte (ASCII) code unit
        if b < 0x80 then
            state
            |> List.append (Num.toU16 b)
            ## 2-byte sequence
            # else if b < 0xE0 then
            #    when (List.get utf8 (index + 1)) is
            #        Ok nextByte ->
            #            state
            #            |> List.append (Num.toU16 (((b |> Num.bitwiseAnd 0x1F) |> Num.shiftLeftBy 6) |> Num.bitwiseOr (nextByte |> Num.bitwiseAnd 0x3F)))
            #        Err NotFound -> crashInvalid 2
            ## 3-byte sequence
            # else if b < 0xF0 then
            #    when (List.get utf8 (index + 1), List.get utf8 (index + 2)) is
            #        (Ok nextByte1, Ok nextByte2) ->
            #            state
            #            |> List.append (Num.toU16 (((b |> Num.bitwiseAnd 0x0F) |> Num.shiftLeftBy 12) |> Num.bitwiseOr ((nextByte1 |> Num.bitwiseAnd 0x3F) |> Num.shiftLeftBy 6) |> Num.bitwiseOr (nextByte2 |> Num.bitwiseAnd 0x3F)))
            #        (_, _) -> crashInvalid 3
            # 4-byte sequence
        else
            when (List.get utf8 (index + 1), List.get utf8 (index + 2), List.get utf8 (index + 3)) is
                (Ok nextByte1, Ok nextByte2, Ok nextByte3) ->
                    codePoint =
                        (b |> Num.bitwiseAnd 0x07 |> Num.shiftLeftBy 18)
                        |> Num.bitwiseOr ((nextByte1 |> Num.bitwiseAnd 0x3F) |> Num.shiftLeftBy 12)
                        |> Num.bitwiseOr ((nextByte2 |> Num.bitwiseAnd 0x3F) |> Num.shiftLeftBy 6)
                        |> Num.bitwiseOr (nextByte3 |> Num.bitwiseAnd 0x3F)
                        |> Num.toU16

                    if codePoint > 0xFFFF then
                        highSurrogate = 0xD800 + (((codePoint - 0x10000) |> Num.shiftRightBy 10) |> Num.bitwiseAnd 0x3FF)
                        crash ""
                        #    lowSurrogate = 0xDC00 + ((codePoint - 0x10000) |> Num.bitwiseAnd 0x3FF)
                        #    state
                        #    |> List.append (Num.toU16 highSurrogate)
                        #    |> List.append (Num.toU16 lowSurrogate)
                    else
                        state
                        |> List.append (Num.toU16 codePoint)

                (_, _, _) -> crashInvalid 4

Utf16Problem : []
windowsToStr : List U16 -> Result Str [BadUtf16 Utf16Problem U64]
utf8toUtf16 : U8 -> U16
windowsToUnix : List U16 -> List U8
unixToWindows : List U8 -> List U16

## Returns everything after the last directory separator in the path. Returns `Err` if the path
## ends in `..` or in a directory separator.
##
## ```roc
## expect Path.filename (Path.unix "foo/bar.txt") == Ok (Path.unix "bar.txt")
## expect Path.filename (Path.unix "foo/bar") == Ok (Path.unix "bar")
## expect Path.filename (Path.unix "foo/bar/") == Err IsDirPath
## expect Path.filename (Path.windows "foo\\bar\\") == Err IsDirPath
## expect Path.filename (Path.unix "foo/bar..") == Err EndsInDots
## expect Path.filename (Path.unix "foo") == Ok (Path.unix "foo")
## expect Path.filename (Path.unix "") == Ok (Path.unix "")
## ```
filename : Path -> Result Path [IsDirPath, EndsInDots]
filename = \@Path path ->
    when path is
        Windows u16s ->
            when u16s is
                [.., '/'] -> Err IsDirPath
                [.., '\\'] -> Err IsDirPath
                [.., '.', '.'] -> Err EndsInDots
                _ ->
                    when List.findLastIndex u16s (\u16 -> u16 == '/' || u16 == '\\') is
                        Ok lastSepIndex -> Ok (@Path (Windows (afterSep u16s lastSepIndex)))
                        Err NotFound -> Ok (@Path path) # No separators? Entire path is the filename!

        Unix bytes ->
            when bytes is
                [.., '/'] -> Err IsDirPath
                # Note that backslashes are *not* directory separators in UNIX
                [.., '.', '.'] -> Err EndsInDots
                _ ->
                    when List.findLastIndex bytes (\u8 -> u8 == '/') is
                        Ok lastSepIndex -> Ok (@Path (Unix (afterSep bytes lastSepIndex)))
                        Err NotFound -> Ok (@Path path) # No separators? Entire path is the filename!

expect Path.filename (Path.unix "foo/bar.txt") == Ok (Path.unix "bar.txt")
expect Path.filename (Path.unix "foo/bar") == Ok (Path.unix "bar")
expect Path.filename (Path.unix "foo/bar/") == Err IsDirPath
expect Path.filename (Path.windows "foo\\bar\\") == Err IsDirPath
expect Path.filename (Path.unix "foo/bar..") == Err EndsInDots
expect Path.filename (Path.unix "foo") == Ok (Path.unix "foo")
expect Path.filename (Path.unix "") == Ok (Path.unix "")

afterSep : List (Num a), U64 -> List (Num a)
afterSep = \list, lastSepIndex ->
    # Return everything after the separator. Example:
    #
    # "foo/bar.txt"
    #     len = 11
    #     lastSepIndex = 3
    #     start = 4
    #     len - start = 11 - 4 = 7
    start = lastSepIndex |> Num.addWrap 1
    len = List.len list |> Num.subWrap start

    List.sublist list { start, len }

## Like [filename], except converts the resulting path to a [Str] using [toStr].
filenameStr : Path -> Result Str [IsDirPath, EndsInDots, FilenameIsNotStr Path U64]

## The extension is considered to be everything following the first dot in the filename,
## unless the filename begins with a dot - in which case it's everything following the
## second dot in the filename.
##
## * If the filename has only one dot, and it's at the end of the filename, returns `Ok` with an empty [Path].
## * If the filename is empty, returns `Ok` with an empty [Path].
## * If the filename ends in a slash, returns `Err` because this path refers to a directory, and directories don't have file extensions.'
## * If the filename ends in multiple dots, returns `Err` because the extension can't be known without resolving the `..` first.
##
## ```roc
## expect Path.ext (Path.unix "foo/bar.txt") == Ok (Path.unix "txt")
## expect Path.ext (Path.unix "foo/bar.") == Ok (Path.unix "")
## expect Path.ext (Path.unix "foo/.bar.txt") == Ok (Path.unix "txt")
## expect Path.ext (Path.unix "foo/bar.") == Ok (Path.unix "")
## expect Path.ext (Path.unix "foo/bar") == Ok (Path.unix "")
## expect Path.ext (Path.unix "foo/.bar") == Ok (Path.unix "")
## expect Path.ext (Path.unix "foo/bar.baz.txt") == Ok (Path.unix "baz.txt")
## expect Path.ext (Path.unix "foo/.bar.baz.txt") == Ok (Path.unix "baz.txt")
## expect Path.ext (Path.unix "foo/bar/") == Err IsDirPath
## expect Path.ext (Path.unix "foo/bar..") == Err EndsInDots
## expect Path.ext (Path.unix "") == Ok (Path.unix "")
## ```
ext : Path -> Result Path [IsDirPath, EndsInDots]

## Like [ext], except converts the resulting path to a [Str] using [toStr].
extStr : Path -> Result Str [IsDirPath, EndsInDots, ExtIsNotStr Path U64]

## Adds a file separator followed by the given string.
##
## The file separator will be either a slash or backslash, depending on how this [Path]
## was created. If the path was created using [Path.unix], the separator will be a slash.
## If it was created using [Path.windows], it will be a backslash.
join : Path, Str -> Path
join = \@Path path, str ->
    when path is
        Windows u16s ->
            suffix = strToUtf16 str

            u16s
            |> List.reserve (1 + List.len suffix)
            |> List.append (utf8toUtf16 '/')
            |> List.concat suffix
            |> Windows
            |> @Path

        Unix bytes ->
            suffix = Str.toUtf8 str

            bytes
            |> List.reserve (1 + List.len suffix)
            |> List.append '/'
            |> List.concat suffix
            |> Unix
            |> @Path

concat : Path, Path -> Path
concat = \@Path p1, @Path p2 ->
    when (p1, p2) is
        (Windows list1, Windows list2) -> windowsU16s (List.concat list1 list2)
        (Unix list1, Unix list2) -> unixBytes (List.concat list1 list2)
        (Windows list1, Unix list2) -> windowsU16s (List.concat list1 (unixToWindows list2))
        (Unix list1, Windows list2) -> unixBytes (List.concat list1 (windowsToUnix list2))

## Normalizes the path by simplifying redundant parts.
##
## If the path was created with [Path.unix], this does the following:
## 1. Replaces `foo/bar/../baz/` with `foo/baz/` (and does the same with `\` on Windows).
## 2. Replaces `foo/./bar/` with `foo/bar/` (and does the same with `\` on Windows).
## 3. Replaces repeated path separators (e.g. `//`) with one path separator.
## 4. If the path contains any `"\u(0)"`s, ends the path before the first one. (See [fromRaw] for why this would be helpful.)
##
## If the path was created with [Path.windows], this does the same thing except that it considers `/`
## and `\` to be equivalent (since Windows considers both to be directory separators), and normalizes
## all directory separators to `\`s in the returned path.
##
## Note that operating systems generally do not normalize symlinks, which means that normalizing a path
## can change program behavior! For example, if there is a symlink in the operating system which
## contains two consecitive file separators, then normalizing could mean that a path which previously
## would have resolved using that symlink will no longer involve the symlink.
##
## The process of normalizing while also resolving symlinks is known as *canonicalization*. Operating
## systems already canonicalize paths automatically before operating on them, so typically the only
## reason to explicitly canonicalize them in a program is to display or record the canonicalized path.
## Canonicalizing paths is out of scope for this module, because it requires a [Task] that talks to
## the operating system (symlinks can change on disk in the middle of a running program, so there's
## no way to get a canonicalized path besides asking the OS for it), and this module is designed not
## to depend on talking to the operating system.
normalize : Path -> Path
normalize = \@Path path ->
    when path is
        Windows u16s ->
            List.withCapacity (List.len u16s)
            |> normalizeWindows u16s
            |> Windows
            |> @Path

        Unix bytes ->
            List.withCapacity (List.len bytes)
            |> normalizeUnix bytes
            |> Unix
            |> @Path

normalizeWindows : List U16, List U16 -> List U16
normalizeWindows = \answer, remaining ->
    when remaining is
        ['/', '/', ..] | ['/', '\\', ..] | ['\\', '/', ..] | ['\\', '\\', ..] ->
            if List.isEmpty answer then
                # At the very beginning of a Windows path, two backslashes
                # (either of which could be slashes instead) means a UNC Path
                # and should be preserved. See https://learn.microsoft.com/en-us/dotnet/standard/io/file-path-formats#unc-paths
                answer
                |> List.append '\\'
                |> List.append '\\'
                |> normalizeWindows (remaining |> List.dropFirst 2)
            else
                # Collapse other consecutive separators into one backslash.
                answer
                |> List.append '\\'
                |> normalizeWindows (remaining |> List.dropFirst 2)

        ['/', '.', '/', ..] | ['/', '.', '\\', ..] | ['\\', '.', '/', ..] | ['\\', '.', '\\', ..] ->
            # Normalize separator-dot-separator into one backslash.
            answer
            |> List.append '\\'
            |> normalizeWindows remaining

        ['/', '.', '.', '/', ..] | ['\\', '.', '.', '/', ..] | ['/', '.', '.', '\\', ..] | ['\\', '.', '.', '\\', ..] ->
            # "/../" means we should delete the component we most recently added.
            when List.findLastIndex answer (\u16 -> u16 == '/' || u16 == '\\') is
                Ok lastSepIndex ->
                    lenToDelete = List.len answer |> Num.subWrap lastSepIndex

                    # Example:
                    #     "foo/things"
                    #     lastSepIndex = 3
                    #     lenToDelete = 10 - 3 = 7
                    #     |> List.dropLast 7 yields "foo" as desired

                    answer
                    |> List.dropLast lenToDelete
                    |> List.append '\\' # replace the "/../" with one backslash
                    |> normalizeWindows (remaining |> List.dropFirst 4)

                Err NotFound ->
                    # There are no separators in the answer we've accumulated so far.
                    if List.isEmpty answer then
                        # If the answer was empty (e.g. the whole input path begins with "/../"),
                        # then the input path was invalid, and we leave it alone. (We don't want to
                        # have normalize change an invalid path to a different and potentially valid
                        # one!) It's fine if the path itself begins with "../" - so don't change that.
                        answer
                        |> List.concat ['\\', '.', '.', '\\']
                        |> normalizeWindows (remaining |> List.dropFirst 4)
                    else
                        # If the path was nonempty, then we eliminate everything up to this point -
                        # e.g. normalizing `foo/../bar` to `bar`
                        answer # TODO this comment should appear on the next line; formatter bug!
                        # Drop all the elements instead of starting over with empty list,
                        # in order to keep the capacity we already reserved on the heap.
                        |> List.dropFirst (List.len answer)
                        |> normalizeWindows (remaining |> List.dropFirst 4)

        [0, ..] | [] ->
            # If we encounter a zero, we're immediately done. Drop the zero and everything after it!
            # We're also done if we ran out of remaining elements to process.
            answer

        [next, ..] ->
            # This element is unremarkable; copy it into the answer and keep moving
            answer
            |> List.append next
            |> normalizeWindows (remaining |> List.dropFirst 1)

normalizeUnix : List U8, List U8 -> List U8
normalizeUnix = \answer, remaining ->
    when remaining is
        ['/', '/', ..] ->
            # Collapse consecutive separators into one slash.
            answer
            |> List.append '/'
            |> normalizeUnix (remaining |> List.dropFirst 2)

        ['/', '.', '/', ..] ->
            # Normalize separator-dot-separator into one backslash.
            answer
            |> List.append '\\'
            |> normalizeUnix remaining

        ['/', '.', '.', '/', ..] ->
            # "/../" means we should delete the component we most recently added.
            when List.findLastIndex answer (\byte -> byte == '/') is
                Ok lastSepIndex ->
                    lenToDelete = List.len answer |> Num.subWrap lastSepIndex

                    # Example:
                    #     "foo/things"
                    #     lastSepIndex = 3
                    #     lenToDelete = 10 - 3 = 7
                    #     |> List.dropLast 7 yields "foo" as desired

                    answer
                    |> List.dropLast lenToDelete
                    |> List.append '/' # replace the "/../" with one slash
                    |> normalizeUnix (remaining |> List.dropFirst 4)

                Err NotFound ->
                    # There are no separators in the answer we've accumulated so far.
                    if List.isEmpty answer then
                        # If the answer was empty (e.g. the whole input path begins with "/../"),
                        # then the input path was invalid, and we leave it alone. (We don't want to
                        # have normalize change an invalid path to a different and potentially valid
                        # one!) It's fine if the path itself begins with "../" - so don't change that.
                        answer
                        |> List.concat ['/', '.', '.', '/']
                        |> normalizeUnix (remaining |> List.dropFirst 4)
                    else
                        # If the path was nonempty, then we eliminate everything up to this point -
                        # e.g. normalizing `foo/../bar` to `bar`
                        answer # TODO this comment should appear on the next line; formatter bug!
                        # Drop all the elements instead of starting over with empty list,
                        # in order to keep the capacity we already reserved on the heap.
                        |> List.dropFirst (List.len answer)
                        |> normalizeUnix (remaining |> List.dropFirst 4)

        [0, ..] | [] ->
            # If we encounter a zero, we're immediately done. Drop the zero and everything after it!
            # We're also done if we ran out of remaining elements to process.
            answer

        [next, ..] ->
            # This element is unremarkable; copy it into the answer and keep moving
            answer
            |> List.append next
            |> normalizeUnix (remaining |> List.dropFirst 1)

## Returns a string representation of the path, replacing anything that can't be
## represented in a string with the Unicode Replacement Character.
##
## To get back an `Err` instead of silently replacing problems with the Unicode Replacement Character,
## use [toStr] instead.
display : Path -> Str
# display = \@Path path ->
#    when path is
#        Unix bytes -> crash "TODO fromUtf8Lossy"
#        Windows u16s -> crash "TODO fromUtf16Lossy"

## Like [display], but renders the path Windows-style (with backslashes for directory separators)
## even if it was originally created as a UNIX path (e.g. using [Path.unix]).
displayWindows : Path -> Str

## Like [display], but renders the path UNIX-style (with slashes for directory separators)
## even if it was originally created as a Windows path (e.g. using [Path.windows]).
displayUnix : Path -> Str

## If any content is encountered that can't be converted to a [Str],
## returns the index into the underlying [List] of data (which can be obtained
## from the [Path] using [toRaw]) where that content was encountered.
toStr : Path -> Result Str [InvalidStr U64]
toStr = \@Path path ->
    when path is
        Windows u16s ->
            windowsToStr u16s
            |> Result.mapErr \BadUtf16 _ index -> InvalidStr index

        Unix bytes ->
            Str.fromUtf8 bytes
            |> Result.mapErr \BadUtf8 _ index -> InvalidStr index

## Like [toStr], but renders the path Windows-style (with backslashes for directory separators)
## even if it was originally created as a UNIX path (e.g. using [Path.unix]).
toStrWindows : Path -> Result Str [InvalidStr U64]

## Like [display], but renders the path UNIX-style (with slashes for directory separators)
## even if it was originally created as a Windows path (e.g. using [Path.windows]).
toStrUnix : Path -> Result Str [InvalidStr U64]

## Converts the given [Path] to either a [List U8] (if the path was created
## using [Path.unix]) or a [List U16] (if the path was created with [Path.windows]).
toRaw : Path -> [Windows (List U16), Unix (List U8)]
toRaw = \@Path path -> path

## Takes the output of a [toRaw] call and returns a [Path].
##
## This function is most often called by platforms, passing values that were received
## directly from the operating system. To maximize performance, no validation is performed
## on the provided lists. Here are some ways the lists can be invalid, and what
## the consequences will be if they are:
##
## * If a `Windows` list contains any numbers beween 1 and 31, then the path is not a valid Windows path. All the operations in this `Path` module will work as normal (e.g. [ext], [display], etc.), but if you try to use the path with any operation system functions (like reading a file from disk), Windows will give an error.
## * If either a `Windows` or `Unix` list contains any zeroes, then the operating system will ignore the zero as well as everything that comes after it. (Once again, all the operations in this `Path` module will work as normal.)
##
## The reason this function does not perform validation is that it will almost always
## be called by platforms, passing lists that are definitely valid because they came directly from
## the operating system. For example, when returning the contents of a (maybe very large) directory,
## a validation function would have to spend time verifying each of those entries, even though it
## would always pass.
##
## In the unusual situation where this function isn't being called by a platform,
## accidentally passing invalid lists is possible, but it's an unlikely mistake to make.
fromRaw : [Windows (List U16), Unix (List U8)] -> Path
fromRaw = \raw -> @Path raw
