define {i32, i1, i24} @saddtest_nsw(i8 %a, i8 %b) {
%0:
  %aa = sext i8 %a to i32
  %bb = sext i8 %b to i32
  %x = sadd_overflow {i32, i1, i24} %aa, %bb
  ret {i32, i1, i24} %x
}
=>
define {i32, i1, i24} @saddtest_nsw(i8 %a, i8 %b) {
%0:
  %aa = sext i8 %a to i32
  %bb = sext i8 %b to i32
  %x = add nsw i32 %aa, %bb
  %1 = insertvalue {i32, i1, i24} { undef, 0, poison }, i32 %x, 0
  ret {i32, i1, i24} %1
}
