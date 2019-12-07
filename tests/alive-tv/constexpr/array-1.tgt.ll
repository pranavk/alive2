@a = constant i32 4
@b = constant i32 5
@x = constant [2 x i8*] [i8* bitcast (i32* @a to i8*), i8* bitcast (i32* @b to i8*)]

define i8* @f() {
  %1 = bitcast i32* @b to i8*
  ret i8* %1
}