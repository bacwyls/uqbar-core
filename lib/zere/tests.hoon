/+  *zere-test-gen, set-tests=zere-test-set
::
|%
++  dec  [[6 [5 [0 6] 1 0] [0 0] 7 [[0 95] [1 0] 0 6] 6 [5 [0 7] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 0 0]
++  dec-jet  [[11 [500.151.969.402 [1 0 6.514.020] 0 6] 7 [10 [2 0 47] 0 1] 6 [5 [0 6] 1 0] [0 0] 7 [[0 95] [1 0] 0 6] 6 [5 [0 7] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 0 0]
--
^-  json
%-  finish:mk
%-  tests:mk
:~  set+set-tests
:: :~  :-  'dec-gates'
::     %-  tests:mk
::     :~  dec+test:mk(s dec, f [9 2 10 [6 1 5] 0 1])
::         dec-jet+test:mk(s dec-jet, f [9 2 10 [6 1 5] 0 1])
::     ==
::     :-  'jets'
::     %-  tests:mk
::     :~  dec+(mint:mk '(dec 5)')
::         add+(mint:mk '(add 5 32)')
::         turn+(mint:mk '(turn ~[1 2 3] |=(a=@ +(a)))')
::         roll+(mint:mk '(roll `(list @)`~[1 2 3] add)')
::         reel+(mint:mk '(reel `(list @)`~[1 2 3] add)')
::         set+set-tests
::     ==
==