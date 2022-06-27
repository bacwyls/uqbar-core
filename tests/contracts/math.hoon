::  Test suite for math.hoon
::
/+  *test, cont=zig-contracts-math, *zig-sys-smart
!:
=>  |%
    +$  value  number=@ud
    +$  action
      $%  [%make-value initial=@ud]
          [%add amount=@ud]
          [%sub amount=@ud]
          [%mul multiplier=@ud]
          [%giv who=id]
      ==
    ::
    ++  grainz
      |=  grz=(list grain)
      %-  ~(gas by *(map id grain))
      %+  turn  grz
      |=  [=grain]
      [id.grain grain]
    ++  make-cart
      |=  [owns=(map id grain)]
      ^-  cart
      [me=math-wheat-id init-now town-id owns]
    ::
    ++  init-now  ~2022.6.20..17.54.07..7d8d
    ++  town-id    0x1
    ++  owner-1
      ^-  account
      [id=0xbeef nonce=0 zigs=0x1234.5678]
    ::
    ++  math-wheat-id  0xadd
    ++  math-salt      `@`'math'
    ++  make-grain
      |=  holder=id
      |=  =value
      ^-  grain
      :*  id=(fry-rice holder math-wheat-id town-id math-salt)
          lord=math-wheat-id
          holder
          town-id
          germ=[%& math-salt data=value]
      ==
    ++  math-grain-1  ^-(grain ((make-grain id:owner-1) [number=100]))
    ++  math-grain-2  ^-(grain ((make-grain id:owner-1) [number=120]))
    --
|%
++  test-contract-typechecks  ^-  tang
  =/  valid  (mule |.(;;(contract cont)))
  (expect-eq !>(%.y) !>(-.valid))
::
++  test-create-value
  ^-  tang
  =/  =embryo
    :*  caller=owner-1
        args=`[%make-value 100]
        grains=~
    ==
  =/  =cart  (make-cart ~)
  =/  res=chick  (~(write cont cart) embryo)
  =*  expected-grain  math-grain-1
  =/  grain  ?>(?=(%.y -.res) (snag 0 ~(val by issued.p.res)))
  (expect-eq !>(expected-grain) !>(grain))
::
++  test-add-value
  ^-  tang
  ::  setting up the tx to propose
  ::  creating the execution context by hand
  =/  =embryo
    :*  caller=owner-1
        args=`[%add 20]
        grains=~
    ==
  =/  =cart  (make-cart (grainz ~[math-grain-1]))
  ::  executing the contract call with the context
  =/  res=chick  (~(write cont cart) embryo)
  ::
  =*  expected-grain  math-grain-2
  =/  grain  ?>(?=(%.y -.res) (snag 0 ~(val by changed.p.res)))
  (expect-eq !>(expected-grain) !>(grain))
--