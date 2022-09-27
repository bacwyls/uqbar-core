/+  *zere-test-gen
|%
++  test-set  [n=10 l=[n=3 l=[n=4 [n=12 l=~ r=~] r=~] r=[n=2 l=[n=1 l=~ r=[n=11 l=~ r=~]] r=[n=7 l=~ r=~]]] r=[n=5 l=[n=6 l=~ r=[n=8 l=~ r=~]] r=[n=9 l=~ r=~]]]
++  balanced-a  [2 [1 ~ ~] [3 ~ ~]]
  ::  Doesn't follow vertical ordering
  ::
++  unbalanced-a  [1 [2 ~ ~] [3 ~ ~]]
++  unbalanced-b  [1 ~ [2 ~ ~]]
++  unbalanced-c  [1 [2 ~ ~] ~]
  ::  Doesn't follow horizontal ordering
  ::
++  unbalanced-d  [2 [3 ~ ~] [1 ~ ~]]
  ::  Doesn't follow horizontal & vertical ordering
  ::
++  unbalanced-e  [1 [3 ~ ~] [2 ~ ~]]
--
%-  tests:mk
:~
:: :~  :-  'has'
::     %-  tests:mk
::     :~  has+(mint:mk (crip "(~(has pin `(pset)`{<test-set>}) 5)"))
::         has-head+(mint:mk (crip "(~(has pin `(pset)`{<test-set>}) 10)"))
::         not-has-branch-right+(mint:mk (crip "(~(has pin `(pset)`{<test-set>}) 32)"))
::         not-has-branch-left+(mint:mk (crip "(~(has pin `(pset)`{<test-set>}) 39)"))
::         not-has-head-branch-left+(mint:mk '(~(has pin `(pset)`[34 ~ ~]) 65)')
::         not-has-head-branch-right+(mint:mk '(~(has pin `(pset)`[34 ~ ~]) 10)')
::     ==
::     :-  'put'
::     %-  tests:mk
::     :~  put+(mint:mk (crip "(~(put pin `(pset)`{<test-set>}) 20)"))
::         put-exists+(mint:mk (crip "(~(put pin `(pset)`{<test-set>}) 11)"))
::         put-exists-head+(mint:mk (crip "(~(put pin `(pset)`{<test-set>}) 10)"))
::     ==
::     :-  'tap'
::     %-  tests:mk
::     :~  tap+(mint:mk (crip "~(tap pin `(pset)`{<test-set>})"))
::         tap-empty+(mint:mk (crip "~(tap pin `(pset)`~)"))
::         tap-one+(mint:mk (crip "~(tap pin `(pset)`[n=10 ~ ~])"))
::         tap-two-left+(mint:mk (crip "~(tap pin `(pset)`[n=10 l=[n=3 ~ ~] ~])"))
::         tap-two-right+(mint:mk (crip "~(tap pin `(pset)`[n=10 ~ r=[n=5 ~ ~]])"))
::         tap-three-right+(mint:mk (crip "~(tap pin `(pset)`[n=10 l=[n=3 ~ ~] r=[n=5 ~ ~]])"))
::     ==
::     :-  'apt'
::     %-  tests:mk
::     :~  apt-balanced-a+(mint:mk (crip "~(apt pin `(pset)`{<balanced-a>})"))
::         apt-unbalanced-a+(mint:mk (crip "~(apt pin `(pset)`{<unbalanced-a>})"))
::         apt-unbalanced-b+(mint:mk (crip "~(apt pin `(pset)`{<unbalanced-b>})"))
::         apt-unbalanced-c+(mint:mk (crip "~(apt pin `(pset)`{<unbalanced-c>})"))
::         apt-unbalanced-d+(mint:mk (crip "~(apt pin `(pset)`{<unbalanced-d>})"))
::         apt-unbalanced-e+(mint:mk (crip "~(apt pin `(pset)`{<unbalanced-e>})"))
::     ==
    :-  'gas'
    %-  tests:mk
    :~  gas+(mint:mk (crip "(~(gas pin `(pset)`{<test-set>}) ~[20 21 22])"))
    ==
==
