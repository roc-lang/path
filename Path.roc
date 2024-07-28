module [
    Path,
    unix,
    unixBytes,
    windows,
    windowsU16s,
    filename,
    toStr,
    toNums,
    toStrWindows,
    toStrUnix,
    display,
    displayUnix,
    displayWindows,
]

Path := [
    Unix (List U8),
    Windows (List U16),
]

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
## expect Path.filename (Path.unix "foo") == Ok "foo"
## expect Path.filename (Path.unix "") == Ok ""
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
## expect Path.ext (Path.unix "") == Ok ""
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

## Returns a string representation of the path, replacing anything that can't be
## represented in a string with the Unicode Replacement Character.
##
## To get back an `Err` instead of silently replacing problems with the Unicode Replacement Character,
## use [toStr] instead.
display : Path -> Str
display = \@Path path ->
    when path is
        Unix bytes -> crash "TODO fromUtf8Lossy"
        Windows u16s -> crash "TODO fromUtf16Lossy"

## Like [display], but renders the path Windows-style (with backslashes for directory separators)
## even if it was originally created as a UNIX path (e.g. using [Path.unix]).
displayWindows : Path -> Str

## Like [display], but renders the path UNIX-style (with slashes for directory separators)
## even if it was originally created as a Windows path (e.g. using [Path.windows]).
displayUnix : Path -> Str

## If any content is encountered that can't be converted to a [Str],
## returns the index into the underlying [List] of data (which can be obtained
## from the [Path] using [toNums]) where that content was encountered.
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
toNums : Path -> [Windows (List U16), Unix (List U8)]
toNums \@Path path -> path
