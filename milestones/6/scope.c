#include <stdio.h>

int main() {
  int a;
  {
    int b = 1;
    int c = 2;
    a = b + c;
  }

  printf("%i\n", a);
}