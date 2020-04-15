define i16 @foo(i8 %a, i16 %b, i8 %c, i16 %d) {
  %x = sub i8 %a, %c
  %y = sub i16 %b, %d

  %z = sext i8 %x to i16
  %res = add i16 %y, %z
  ret i16 %res
}