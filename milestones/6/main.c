#include <stdio.h>

int main() {
  int a = 12;
  struct {
    int a;
    int b;
  } obj = {a, a * 3};

  printf("%i\n", obj.a + obj.b);
}