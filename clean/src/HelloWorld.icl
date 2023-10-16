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


::Sexpr = I Int
        | R Real
        | S String  // Symbol
        | T String  // String (Text)
        | L [Sexpr]

tokenize :: *File -> [String]
tokenize io = tokenize_ io [] []

tokenize_ :: *File [Char] [String] -> [String]
tokenize_ io current tokens
    # (at_end, io) = fend io
    | at_end = finalize_tokens_ current tokens
    = [] //todo

finalize_tokens_ :: [Char] [String] -> [String]
finalize_tokens_ [] tokens = tokens
finalize_tokens_ current tokens = [(toString current) : tokens]