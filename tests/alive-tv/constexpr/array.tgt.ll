@a = constant [2 x i8] [i8 0, i8 0]

define i8 @f() {
  %a = load i8, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @a, i64 0, i64 1)
  ret i8 %a
}