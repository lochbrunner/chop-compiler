# Compiler

## Architecture

The Compiler for has these data flow chain

* *Lexer*: Code -> tokens
* *Parser*: Token -> AST
* *Simplifier*: Removes simple overhead (e.g. 3*5 -> 15)
* *Generator* (also planed: *Injector* & *Checker*)
* *Compiler*: AST -> byte-code
* *Exporter*
  * Interpreter byte-code
  * LLVM: byte-code -> LLVM-IR

## Challenges

* How to propagate information (from *Generator* and *Injector*) back to the *Parser* and *Lexer*?

