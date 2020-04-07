define { i8, i8 } @func(i8 %x, i8 %y) {
  %1 = insertvalue { i8, i8 } {i8 0, i8 1}, i8 %x, 0
  %2 = insertvalue { i8, i8 } %1, i8 %y, 1
  ret { i8, i8 } %2
}
