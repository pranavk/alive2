@a = constant i32 4
@b = constant i32 5
@x = constant [2 x i8*] [i8* bitcast (i32* @a to i8*), i8* bitcast (i32* @b to i8*)]

define i8* @f() {
  %1 = getelementptr inbounds [2 x i8*], [2 x i8*]* @x, i64 0, i64 1
  %2 = load i8*, i8** %1
  ret i8* %2
}