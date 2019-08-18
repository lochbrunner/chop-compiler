import * from iostream

"Hello World!" | stdout

// Get integer from terminal
i := stdin.once | i32.parse


// Parse struct
parse_struct = (a, b) => {
    a:+ i32.parse(a),
    b:+ i32.parse(b),
}

sum = (obj) => obj.a + obj.b

obj := stdin.once | split | parse_struct

obj | sum | stdout

type a := i32|i64

// in one line
stdin.once | split | i32.parse | + | stdout

// a+b*c*d
stdin.once | split | i32.parse | + | * | stdout
