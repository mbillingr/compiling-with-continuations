module HelloWorld

import StdEnv

// read a number from stdin and write it back to stdout

Start :: *World -> Int
Start world
    # (io,world) = stdio world
    # (ok,n,io) = freadi io
    # (io) = fwritec '\n' io
    # (io) = fwritei n io
    # (io) = fwritec '\n' io
    # (ok,world) = fclose io world
    | not ok = 0
    = 456
