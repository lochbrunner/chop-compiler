# Milestone 6 - Objects

## Implementation Hints

* Local scopes get ignored in LLVM.

## Example

```chop
#!/usr/bin/env ichop

obj := {
    a :+ 12
    b :+ a * 3
}

stdout obj.a + obj.b
```

Equivalent C code

```c
#include <stdio.h>

int main() {
  int a = 12;
  struct {
    int a;
    int b;
  } obj = {a, a * 3};

  printf("%i\n", obj.a + obj.b);
}
```

Difference: Chop has no variable `a` in outer scope.
