# Compiler

## Architecture

The Compiler for has these data flow chain

* *Lexer*
* *Parser*
* *Generator* (also planed: *Injector* & *Checker*)
* *Exporter*
  * Interpreter byte-code
  * planed: llvm
  * planed: chop IR

## Challenges

* How to propagate information (from *Generator* and *Injector*) back to the *Parser* and *Lexer*?

