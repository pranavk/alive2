@a = external constant [2 x i32], align 1

define i32 @f() {
  %a = getelementptr inbounds [2 x i32], [2 x i32]* @a, i64 0, i64 1
  %b = load i32, i32* %a
  ret i32 %b
}